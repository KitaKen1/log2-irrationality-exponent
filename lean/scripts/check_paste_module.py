"""Check complete selected source modules with the paste edition's actual imports.

This is a focused regression check, not a full log-two proof build. Selected
modules include their pinned local import closure and retain source order.
"""
import argparse
from datetime import datetime,timezone
import fcntl
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

from build_audit import graph,sha,write_json,ALLOWED_AXIOMS
from compiler_environment import compiler_environment
from make_lean4web_lite import header_imports
from check_lite_prefix import compiler_reported_failure

ROOT=Path(__file__).resolve().parents[2]
WEB=ROOT/'lean4web'
MODULES=['OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology',
         'OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor']
AUDITS=['OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5',
        'OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck',
        'OAI.PiExponentSeshadri.ModuleGrothendieck.enoughInjectives',
        'OAI.PiExponentSeshadri.Geometry.modulePresheafTensorRestrict']


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout-seconds',type=int,default=180)
    args=parser.parse_args()
    if args.timeout_seconds<1:parser.error('Timeout must be positive')
    guard=(ROOT/'lean/.lake/check.lock').open('a')
    try:fcntl.flock(guard,fcntl.LOCK_EX|fcntl.LOCK_NB)
    except BlockingIOError:raise SystemExit('Another proof checker is active')
    _,sources,order,_=graph()
    selected=set()
    def visit(name):
        if name in selected:return
        selected.add(name)
        for dep in header_imports((ROOT/'lean'/sources[name]['path']).read_text()):
            if dep in sources:visit(dep)
    for module in MODULES:visit(module)
    source=WEB/'LogTwoLean4WebPaste.lean'
    mapping=json.loads((WEB/'paste-source-map.json').read_text())
    if sha(source)!=mapping['source_sha256']:raise ValueError('Source-map hash mismatch')
    lines=source.read_text().splitlines(keepends=True)
    header=''.join(lines[:mapping['sources'][0]['first_line']-1])
    chunks=[header]
    for rec in mapping['sources']:
        if rec['module'] in selected:
            chunks.append(''.join(lines[rec['first_line']-1:rec['last_line']]))
    chunks.extend(f'\n#print axioms {name}\n' for name in AUDITS)
    directory=WEB/'evidence'/(datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-paste-instances')
    directory.mkdir()
    harness=directory/'Modules.lean';harness.write_text(''.join(chunks))
    record=dict(status='preparing',scope=__doc__.strip(),source_sha256=sha(source),
                harness_sha256=sha(harness),header_sha256=hashlib.sha256(header.encode()).hexdigest(),
                modules=[n for n in order if n in selected],memory_mib=4096,threads=1,
                timeout_seconds=args.timeout_seconds,browser_execution_performed=False,
                final_log_two_theorem_checked=False)
    start=time.monotonic()
    try:
        compiler,env=compiler_environment(WEB)
        version=subprocess.check_output([compiler,'--version'],text=True).strip()
        assert version.startswith('Lean (version 4.35.0-rc4,')
        revision=subprocess.check_output(['git','-C',str(WEB/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip()
        assert revision=='1f414401f69059aa7eead47b53ee40bd38455eeb'
        record.update(compiler_version=version,mathlib_commit=revision)
        print(f'Checking {len(selected)} complete module(s) with actual paste imports.',flush=True)
        with (directory/'build.log').open('w') as log:
            proc=subprocess.run([compiler,'--memory=4096','--threads=1','--trust=1',str(harness.relative_to(WEB))],
                                cwd=WEB,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=args.timeout_seconds)
        output=(directory/'build.log').read_text()
        printed=dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",output))
        valid=(proc.returncode==0 and not compiler_reported_failure(output) and
               set(printed)==set(AUDITS) and 'sorryAx' not in output and
               all({a.strip() for a in axioms.split(',') if a.strip()}<=ALLOWED_AXIOMS for axioms in printed.values()))
        record.update(status='passed' if valid else 'failed',exit_code=proc.returncode,axiom_prints=printed)
        if sha(source)!=record['source_sha256']:record.update(status='failed',reason='Source changed during check')
    except subprocess.TimeoutExpired:
        record.update(status='time_limit')
    except BaseException as exc:
        record.update(status='failed',error=str(exc))
    finally:
        record['elapsed_seconds']=round(time.monotonic()-start,3)
        log=directory/'build.log'
        if log.exists():record['log_sha256']=sha(log)
        write_json(directory/'result.json',record)
        guard.close()
    print(directory)
    print(json.dumps(record,indent=2))
    if log.exists():print(log.read_text()[-5000:])
    return 0 if record['status']=='passed' else 1


if __name__=='__main__':raise SystemExit(main())
