"""Bounded single-file check on the browser project's exact toolchain.

Stop at the first compiler error, or after the time limit. A failure does not
invalidate the separately checked split proof; it is retained as migration work.
"""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import fcntl
import hashlib
import json
import os
import re
import resource
import selectors
import subprocess
import time
import uuid
from compiler_environment import compiler_environment

ROOT = Path(__file__).resolve().parents[2]
WEB = ROOT/'lean4web'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout-seconds',type=int,default=900)
    parser.add_argument('--edition',choices=['full','lite','sequential','paste'],default='full')
    args=parser.parse_args()
    if args.timeout_seconds <= 0:parser.error('Timeout must be positive')
    source_name='LogTwoLean4WebLite.lean' if args.edition=='lite' else 'LogTwoLean4Web.lean'
    status_name='lite-build-status.json' if args.edition=='lite' else 'build-status.json'
    if args.edition=='sequential':
        source_name='LogTwoLean4WebSequential.lean'
        status_name='sequential-build-status.json'
    if args.edition=='paste':
        source_name='LogTwoLean4WebPaste.lean'
        status_name='paste-build-status.json'
    guard=(ROOT/'lean/.lake/check.lock').open('a')
    try:fcntl.flock(guard,fcntl.LOCK_EX|fcntl.LOCK_NB)
    except BlockingIOError:raise SystemExit('Another proof checker is active; no compiler started')
    run_id=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ-')+uuid.uuid4().hex[:8]
    directory=WEB/'evidence'/run_id;directory.mkdir(parents=True)
    record={'run_id':run_id,'started_at_utc':datetime.now(timezone.utc).isoformat(),
            'status':'preparing','requested_lean':'leanprover/lean4:v4.35.0-rc4',
            'memory_mib':4096,'threads':1,'timeout_seconds':args.timeout_seconds,
            'browser_execution_performed':False,
            'scope':'Local CLI build of the selected single-file edition, not a browser/server run.',
            'edition':args.edition,'source':source_name,
            'source_sha256':hashlib.sha256((WEB/source_name).read_bytes()).hexdigest(),
            'log':str((directory/'build.log').relative_to(WEB))}
    started=time.monotonic();proc=None
    try:
        compiler,env=compiler_environment(WEB)
        version=subprocess.check_output([compiler,'--version'],text=True).strip()
        record['compiler_version']=version
        if not version.startswith('Lean (version 4.35.0-rc4,'):
            raise RuntimeError('Compiler version differs from the requested v4.35.0-rc4')
        record['mathlib_commit']=subprocess.check_output(
            ['git','-C',str(WEB/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip()
        if record['mathlib_commit']!='1f414401f69059aa7eead47b53ee40bd38455eeb':
            raise RuntimeError('Mathlib revision differs from the rc4 pin')
        command=[compiler,'--memory=4096','--threads=1','--trust=1',source_name]
        record['command']=['lean',*command[1:]]
        cpu_before=resource.getrusage(resource.RUSAGE_CHILDREN)
        proc=subprocess.Popen(command,cwd=WEB,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        selector=selectors.DefaultSelector();selector.register(proc.stdout,selectors.EVENT_READ)
        buffered=b'';first_error=None;stop_reason=None
        with (directory/'build.log').open('wb') as log:
            while selector.get_map():
                if time.monotonic()-started > args.timeout_seconds and proc.poll() is None:
                    stop_reason='time_limit';proc.terminate()
                for key,_ in selector.select(timeout=1):
                    data=os.read(key.fd,65536)
                    if not data:
                        selector.unregister(key.fileobj);continue
                    log.write(data);log.flush();buffered+=data
                    while b'\n' in buffered:
                        line,buffered=buffered.split(b'\n',1)
                        text=line.decode(errors='replace')
                        memory_error=any(s in text.lower() for s in
                            ['out of memory','memory_exception','excessive memory consumption'])
                        if first_error is None and (re.search(r'PANIC|ASSERTION VIOLATION|uncaught exception|\berror(?:\([^)]*\))?:',text) or memory_error):
                            first_error=text;stop_reason='first_compiler_error'
                            if memory_error:stop_reason='memory_limit'
                            if proc.poll() is None:proc.terminate()
            code=proc.wait(timeout=15)
        record.update(exit_code=code,first_error=first_error,stop_reason=stop_reason)
        record['status']='passed' if code==0 and stop_reason is None else 'failed'
        cpu_after=resource.getrusage(resource.RUSAGE_CHILDREN)
        record['compiler_cpu_seconds']=round(cpu_after.ru_utime+cpu_after.ru_stime-
                                             cpu_before.ru_utime-cpu_before.ru_stime,3)
        if record['status']=='passed':
            output=(directory/'build.log').read_text()
            prints=re.findall(r"'LogTwo.irrationalityExponent_log_two' depends on axioms: \[([^\]]*)\]",output)
            if len(prints)!=1 or 'sorryAx' in output or not {a.strip() for a in prints[0].split(',')} <= {'propext','Classical.choice','Quot.sound'}:
                record.update(status='failed',stop_reason='missing_or_unexpected_final_axioms')
    except BaseException as exc:
        record.update(status='failed',error=str(exc))
        if proc is not None and proc.poll() is None:
            proc.terminate()
            try:proc.wait(timeout=10)
            except subprocess.TimeoutExpired:proc.kill();proc.wait()
    record['elapsed_seconds']=round(time.monotonic()-started,3)
    record['completed_at_utc']=datetime.now(timezone.utc).isoformat()
    log=directory/'build.log'
    if log.exists():record['log_sha256']=hashlib.sha256(log.read_bytes()).hexdigest()
    value=json.dumps(record,ensure_ascii=False,indent=2)+'\n'
    (directory/'result.json').write_text(value)
    (WEB/status_name).write_text(value)
    guard.close()
    print(value)
    return 0 if record['status']=='passed' else 1


if __name__=='__main__':raise SystemExit(main())
