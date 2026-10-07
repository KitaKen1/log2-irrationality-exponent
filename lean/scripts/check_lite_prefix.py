"""Bounded rc4 check of a complete-module prefix of the reduced source.

This covers pruning/import regressions in their actual preceding source context.
It does not check the final log-two theorem or the rest of the source.
"""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import fcntl
import json
import re
import subprocess
import time

from build_audit import sha, write_json
from compiler_environment import compiler_environment

ROOT = Path(__file__).resolve().parents[2]
WEB = ROOT / 'lean4web'


def compiler_reported_failure(output):
    # Lean can emit an internal panic and still return zero with axiom prints.
    return bool(re.search(r'PANIC|ASSERTION VIOLATION|uncaught exception|\berror(?:\([^)]*\))?:', output))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--edition',choices=['lite','sequential','paste'],default='lite')
    parser.add_argument('--module-count',type=int,default=100)
    parser.add_argument('--timeout-seconds',type=int,default=240)
    args=parser.parse_args()
    if not 100<=args.module_count<=884:
        parser.error('Choose 100–884 modules; use the full checker for all 885.')
    if args.timeout_seconds<1:parser.error('Timeout must be positive')
    guard = (ROOT / 'lean/.lake/check.lock').open('a')
    try:
        fcntl.flock(guard, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        raise SystemExit('Another proof checker is active; no compiler started')
    source = WEB / ('LogTwoLean4WebSequential.lean' if args.edition=='sequential' else 'LogTwoLean4WebLite.lean')
    reduced = json.loads((WEB / ('sequential-source-map.json' if args.edition=='sequential' else 'reduction.json')).read_text())
    if args.edition=='paste':
        source=WEB/'LogTwoLean4WebPaste.lean'
        reduced=json.loads((WEB/'paste-source-map.json').read_text())
    assert sha(source) == reduced['source_sha256']
    stop = reduced['sources'][args.module_count-1]['last_line']
    prefix = '\n'.join(source.read_text().splitlines()[:stop]) + '\n'
    declarations = [
        'OAI.PiExponent.irrationalityExponent_eq_two_of_eventualLowerBound',
        'LogTwo.Geometry.coordinateKernel_height_le',
        'OAI.PiExponent.derivation_mem_polynomialTangent',
    ]
    if args.module_count>=313:
        declarations += [
            'OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5',
            'OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck',
            'OAI.PiExponentSeshadri.ModuleGrothendieck.enoughInjectives',
            'OAI.PiExponentSeshadri.Geometry.modulePresheafTensorRestrict',
        ]
    prefix += ''.join(f'#print axioms {name}\n' for name in declarations)
    directory = WEB / 'evidence' / (datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ') + '-'+args.edition+'-prefix')
    directory.mkdir()
    harness = directory / 'Prefix.lean'
    harness.write_text(prefix)
    record = dict(scope=__doc__.strip(), source_sha256=sha(source), prefix_sha256=sha(harness),
                  edition=args.edition,
                  module_count=args.module_count, source_lines_checked=stop, memory_mib=4096,
                  threads=1, timeout_seconds=args.timeout_seconds, final_log_two_theorem_checked=False,
                  browser_execution_performed=False)
    compiler, env = compiler_environment(WEB)
    version = subprocess.check_output([compiler,'--version'],text=True).strip()
    assert version.startswith('Lean (version 4.35.0-rc4,')
    record['compiler_version'] = version
    record['mathlib_commit'] = subprocess.check_output(
        ['git','-C',str(WEB/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip()
    assert record['mathlib_commit'] == '1f414401f69059aa7eead47b53ee40bd38455eeb'
    print(f'Checking {args.edition} prefix: {args.module_count} modules, one compiler, 4 GiB, {args.timeout_seconds}-second cap.',flush=True)
    start = time.monotonic()
    with (directory / 'build.log').open('w') as log:
        try:
            result = subprocess.run([compiler,'--memory=4096','--threads=1','--trust=1',
                                     str(harness.relative_to(WEB))],cwd=WEB,env=env,
                                    stdout=log,stderr=subprocess.STDOUT,timeout=args.timeout_seconds)
            record.update(status='passed' if result.returncode == 0 else 'failed',exit_code=result.returncode)
        except subprocess.TimeoutExpired:
            record.update(status='time_limit',exit_code=None)
    record['elapsed_seconds'] = round(time.monotonic()-start,3)
    output = (directory / 'build.log').read_text()
    if compiler_reported_failure(output):
        record.update(status='failed',reason='Compiler error or internal failure in log')
    printed = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",output)
    if record['status'] == 'passed':
        if {n for n,_ in printed} != set(declarations) or 'sorryAx' in output or \
                any(not {a.strip() for a in axioms.split(',')} <= {'propext','Classical.choice','Quot.sound'}
                    for _,axioms in printed):
            record.update(status='failed',reason='Missing or unexpected axioms')
    if sha(source) != record['source_sha256']:
        record.update(status='failed',reason='Source changed during prefix check')
    record['axiom_prints'] = dict(printed)
    record['log_sha256'] = sha(directory / 'build.log')
    write_json(directory / 'result.json',record)
    print(directory)
    print(json.dumps(record,indent=2))
    print(output[-6000:])
    guard.close()
    return 0 if record['status']=='passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
