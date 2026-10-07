"""Check browser metadata controls through the exact rc4 language server.

This deliberately includes one invalid proof, which MUST be rejected. It does
not check the log-two theorem. Only one file worker is opened, under the shared
compiler lock, with a 4 GiB allocator limit and a bounded lifetime.
"""
from datetime import datetime,timezone
from pathlib import Path
import fcntl
import json
import os
import queue
import signal
import subprocess
import threading
import time

from build_audit import write_json,sha
from compiler_environment import compiler_environment
from make_lean4web_paste import INTRO,RESTORE,WRAPPER,WEB

ROOT=WEB.parent


def read_messages(stream,inbox):
    try:
        while True:
            headers={}
            while True:
                line=stream.readline()
                if not line:
                    return
                if line in (b'\r\n',b'\n'):
                    break
                key,_,value=line.decode().partition(':')
                headers[key.lower()]=value.strip()
            count=int(headers['content-length']);data=b''
            while len(data)<count:
                part=stream.read(count-len(data))
                if not part:return
                data+=part
            inbox.put(json.loads(data))
    finally:
        inbox.put(None)


def main():
    guard=(ROOT/'lean/.lake/check.lock').open('a')
    try:fcntl.flock(guard,fcntl.LOCK_EX|fcntl.LOCK_NB)
    except BlockingIOError:raise SystemExit('Another proof checker is active')
    directory=WEB/'evidence'/(datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-paste-editor')
    directory.mkdir()
    # Exact generated control sequences, with lightweight proofs between them.
    source=('module\npublic meta import Lean.Elab.Tactic\n'
            'public meta import Lean.Elab.BuiltinEvalCommand\n'
            'public import Lean.Elab.Tactic\n@[expose] public section\n'+INTRO+
            f'theorem paste_hidden : 2 + 3 = 3 + 2 := by{WRAPPER}\n'
            '  exact Nat.add_comm 2 3\n'
            f'example : False := by{WRAPPER} exact True.intro\n'+RESTORE+
            'run_cmd Lean.logInfo m!"PASTE_OUTER_INFO={(← Lean.Elab.getInfoState).enabled}"\n'
            'theorem paste_visible : 2 + 3 = 3 + 2 := by\n'
            '  exact Nat.add_comm 2 3\n'
            '#print axioms paste_hidden\n#print axioms paste_visible\n'
            'run_cmd Lean.logInfo "PASTE_EDITOR_DONE"\n')
    path=directory/'EditorProbe.lean';path.write_text(source)
    record=dict(status='running',scope=__doc__.strip(),source_sha256=sha(path),
                memory_mib=4096,threads=1,timeout_seconds=90,
                final_log_two_theorem_checked=False,browser_execution_performed=False,
                language_server_execution_performed=True)
    proc=None;messages=[];start=time.monotonic()
    try:
        compiler,env=compiler_environment(WEB)
        version=subprocess.check_output([compiler,'--version'],text=True,timeout=15).strip()
        assert version.startswith('Lean (version 4.35.0-rc4,')
        record['compiler_version']=version
        inbox=queue.Queue()
        with (directory/'stderr.log').open('wb') as err:
            proc=subprocess.Popen([compiler,'--server','--memory=4096','--threads=1','--trust=1'],
                                  cwd=WEB,env=env,stdin=subprocess.PIPE,stdout=subprocess.PIPE,
                                  stderr=err,start_new_session=True)
            threading.Thread(target=read_messages,args=(proc.stdout,inbox),daemon=True).start()
            def send(method,params=None,id=None):
                value={'jsonrpc':'2.0','method':method}
                if params is not None:value['params']=params
                if id is not None:value['id']=id
                data=json.dumps(value).encode()
                proc.stdin.write(f'Content-Length: {len(data)}\r\n\r\n'.encode()+data);proc.stdin.flush()
            deadline=time.monotonic()+90
            def receive_until(predicate):
                while time.monotonic()<deadline:
                    try:item=inbox.get(timeout=min(1,max(.01,deadline-time.monotonic())))
                    except queue.Empty:continue
                    if item is None:raise RuntimeError('Language server connection ended')
                    messages.append(item)
                    if predicate(item):return item
                raise TimeoutError('Bounded language-server probe exceeded 90 seconds')
            uri=path.resolve().as_uri()
            send('initialize',{'processId':os.getpid(),'rootUri':WEB.resolve().as_uri(),
                               'capabilities':{},'initializationOptions':{'hasWidgets':False}},1)
            initialized=receive_until(lambda m:m.get('id')==1)
            if 'error' in initialized:raise RuntimeError(initialized['error'])
            send('initialized',{})
            send('textDocument/didOpen',{'textDocument':{'uri':uri,'languageId':'lean4','version':1,'text':source}})
            receive_until(lambda m:m.get('method')=='textDocument/publishDiagnostics' and
                          any('PASTE_EDITOR_DONE' in d.get('message','') for d in m['params'].get('diagnostics',[])))
            latest=[m for m in messages if m.get('method')=='textDocument/publishDiagnostics'][-1]['params']['diagnostics']
            errors=[d for d in latest if d.get('severity')==1]
            invalid_line=source.splitlines().index(f'example : False := by{WRAPPER} exact True.intro')
            if len(errors)!=1 or errors[0]['range']['start']['line']!=invalid_line:
                raise ValueError('Expected exactly the deliberately invalid proof error')
            joined='\n'.join(d['message'] for d in latest)
            for expected in ['PASTE_OUTER_INFO=true',
                             "'paste_hidden' does not depend on any axioms",
                             "'paste_visible' does not depend on any axioms"]:
                if expected not in joined:raise ValueError('Missing diagnostic: '+expected)
            hover_results={}
            proof_lines=[i for i,line in enumerate(source.splitlines()) if line=='  exact Nat.add_comm 2 3']
            for ident,(name,line) in enumerate(zip(['paste_hidden','paste_visible'],proof_lines),10):
                char=source.splitlines()[line].index('Nat.add_comm')+5
                send('textDocument/hover',{'textDocument':{'uri':uri},'position':{'line':line,'character':char}},ident)
                response=receive_until(lambda m:m.get('id')==ident)
                if 'error' in response:raise ValueError(response['error'])
                hover_results[name]=response.get('result')
            # The server may still display static tactic documentation from the
            # syntax. It must not retain the hidden proof's elaborated term hover.
            if 'Nat.add_comm' in json.dumps(hover_results['paste_hidden']) or \
                    'Nat.add_comm' not in json.dumps(hover_results['paste_visible']):
                raise ValueError('Dependency term hover was not disabled, or final hover not restored')
            record.update(status='passed',invalid_proof_rejected=True,
                          hidden_and_visible_proofs_axiom_free=True,editor_state_restored=True,
                          dependency_term_hover_absent=True,final_hover_present=True,
                          hover_results=hover_results,diagnostics=latest)
            send('textDocument/didClose',{'textDocument':{'uri':uri}})
            send('shutdown',None,20)
            receive_until(lambda m:m.get('id')==20)
            send('exit')
            proc.wait(timeout=10)
        if any(token in (directory/'stderr.log').read_text() for token in ['PANIC','ASSERTION VIOLATION','uncaught exception']):
            raise ValueError('Internal compiler/server failure in stderr')
    except BaseException as exc:
        record.update(status='failed',error=str(exc))
    finally:
        if proc is not None:
            # Includes the one file worker if a request timed out or failed.
            try:os.killpg(proc.pid,signal.SIGTERM)
            except ProcessLookupError:pass
            try:proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid,signal.SIGKILL);proc.wait()
        record['elapsed_seconds']=round(time.monotonic()-start,3)
        write_json(directory/'messages.json',messages)
        write_json(directory/'result.json',record)
        guard.close()
    print(directory)
    print(json.dumps({k:v for k,v in record.items() if k not in {'diagnostics','hover_results'}},indent=2))
    return 0 if record['status']=='passed' else 1


if __name__=='__main__':raise SystemExit(main())
