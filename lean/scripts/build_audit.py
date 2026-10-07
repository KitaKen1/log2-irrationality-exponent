"""Sequential, resumable proof build and final type/axiom audit.

Run after `lake update` and `lake exe cache get`. No external proof service,
independent kernel, or publication is performed by this script.
"""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import fcntl
import hashlib
import json
import re
import shutil
import subprocess
import sys
import time
import uuid
from compiler_environment import compiler_environment
from module_headers import imports

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
    temp.replace(path)


def graph():
    manifest = json.loads((ROOT/'evidence/source-manifest.json').read_text())
    sources = {r['module']: r for r in manifest['sources']}
    actual = {str(p.relative_to(ROOT)) for directory in ['LogTwo','OAI']
              for p in (ROOT/directory).rglob('*.lean')} | {'LogTwo.lean'}
    if actual != {r['path'] for r in sources.values()}:
        raise ValueError('Source inventory differs from the pinned manifest')
    if (ROOT/'lean-toolchain').read_text().strip() != manifest['lean']:
        raise ValueError('Toolchain differs from the verified split proof')
    environment = sha(ROOT/'lake-manifest.json') + manifest['lean']
    ordered, active, fingerprints = [], set(), {}
    def visit(name):
        if name in fingerprints: return
        if name in active: raise ValueError('Import cycle: ' + name)
        active.add(name)
        r = sources[name]; source = ROOT/r['path']
        if sha(source) != r['sha256']: raise ValueError('Source hash mismatch: ' + r['path'])
        deps = [d for d in imports(source.read_text()) if d in sources]
        for d in deps: visit(d)
        fingerprints[name] = hashlib.sha256((environment+r['sha256']+
            ''.join(fingerprints[d] for d in deps)).encode()).hexdigest()
        active.remove(name); ordered.append(name)
    visit('LogTwo')
    if set(ordered) != set(sources): raise ValueError('Unreachable source module')
    return manifest, sources, ordered, fingerprints


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-sources-only', action='store_true')
    parser.add_argument('--rebuild-own', action='store_true')
    parser.add_argument('--reuse-verified', type=Path,
                        help='Optional existing original workspace with matching audited artifacts')
    args = parser.parse_args()
    manifest, sources, ordered, fingerprints = graph()
    if args.check_sources_only:
        print(json.dumps({'source_hashes_matched':len(ordered), 'lean':manifest['lean']})); return
    build = ROOT/'.lake/build/lib/lean'; cache_path = ROOT/'.lake/check-cache.json'
    (ROOT/'.lake').mkdir(exist_ok=True)
    guard = (ROOT/'.lake/check.lock').open('a')
    try: fcntl.flock(guard, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        guard.close()
        raise SystemExit('Another proof checker is active; no compiler started')
    run_id = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ-') + uuid.uuid4().hex[:8]
    run_dir = ROOT/'evidence/runs'/run_id; run_dir.mkdir(parents=True)
    result = {'run_id':run_id, 'status':'running', 'started_at_utc':datetime.now(timezone.utc).isoformat(),
              'lean':manifest['lean'], 'freshly_compiled':[], 'reused':[], 'commands':[],
              'source_manifest_sha256':sha(ROOT/'evidence/source-manifest.json'),
              'resource_policy':{'compilers':1, 'threads':1, 'lean_memory_mib':4096, 'trust':1},
              'clean_network_bootstrap_executed':False, 'independent_kernel_executed':False}
    cache = json.loads(cache_path.read_text()) if cache_path.exists() else {}
    def save(): write_json(run_dir/'result.json', result)
    def run(label, cmd, env):
        log = run_dir/(label+'.log'); start=time.monotonic()
        with log.open('x') as output:
            completed=subprocess.run(cmd,cwd=ROOT,env=env,stdout=output,stderr=subprocess.STDOUT)
        item={'label':label, 'exit_code':completed.returncode,
              'elapsed_seconds':round(time.monotonic()-start,3),
              'log':str(log.relative_to(ROOT)), 'log_sha256':sha(log)}
        result['commands'].append(item); save()
        if completed.returncode: raise RuntimeError('Failed '+label+'; see '+item['log'])
        return log
    try:
        save()
        if args.reuse_verified:
            old_root=args.reuse_verified.resolve()
            old=json.loads((old_root/'audit/lean-verification.json').read_text())
            if old['lean'] != manifest['lean'] or old['mathlib_commit'] != manifest['mathlib_commit']:
                raise ValueError('Reuse toolchain/Mathlib mismatch')
            known={x['module']:x for x in old['compiled_module_artifacts']}
            old_hashes={'.'.join(Path(x['path']).with_suffix('').parts):x['sha256'] for x in old['source_files']}
            old_hashes.update({x['module']:x['sha256'] for x in old['comparison_source_hashes']})
            for name in ordered:
                # New public definitions/bridges are deliberately absent from
                # the historical workspace and must be freshly compiled below.
                if old_hashes.get(name)!=sources[name]['sha256']:continue
                relative=Path(*name.split('.')).with_suffix('.olean')
                old_out=old_root/'.lake/build/lib/lean'/relative
                if sha(old_out)!=known[name]['olean_sha256']:raise ValueError('Reuse artifact mismatch: '+name)
                out=build/relative;out.parent.mkdir(parents=True,exist_ok=True)
                for suffix in ['.olean','.olean.private','.olean.server','.ilean']:
                    if old_out.with_suffix(suffix).exists():shutil.copyfile(old_out.with_suffix(suffix),out.with_suffix(suffix))
                cache[name]={'fingerprint':fingerprints[name], 'olean_sha256':sha(out),
                             'origin':'matched_original_audit', 'original_verified_at_utc':old['verified_at_utc']}
            write_json(cache_path,cache)
        compiler, env=compiler_environment(ROOT)
        result['compiler_version']=subprocess.check_output([compiler,'--version'],text=True).strip()
        result['compiler_sha256']=sha(compiler)
        current_mathlib=subprocess.check_output(['git','-C',str(ROOT/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip()
        if current_mathlib != manifest['mathlib_commit']:raise ValueError('Mathlib revision mismatch')
        force_path=ROOT/'.lake/rebuild-pending.json'
        forced=set(json.loads(force_path.read_text())) if force_path.exists() else set()
        if args.rebuild_own:forced.update(n for n in ordered if n=='LogTwo' or n.startswith('LogTwo.'))
        if forced-set(ordered):raise ValueError('Unknown forced module')
        write_json(force_path,sorted(forced))
        for name in ordered:
            out=build/Path(*name.split('.')).with_suffix('.olean'); entry=cache.get(name,{})
            if name not in forced and out.exists() and entry.get('fingerprint')==fingerprints[name] and entry.get('olean_sha256')==sha(out):
                result['reused'].append(name);continue
            out.parent.mkdir(parents=True,exist_ok=True)
            cache[name]={'origin':'attempt_started_unverified'};write_json(cache_path,cache)
            print('CHECK '+name,flush=True)
            run(name,[compiler,'--memory=4096','--threads=1','--trust=1','--root='+str(ROOT),
                      '-o',str(out),'-i',str(out.with_suffix('.ilean')),str(ROOT/sources[name]['path'])],env)
            if sha(ROOT/sources[name]['path'])!=sources[name]['sha256']:raise ValueError('Source changed: '+name)
            cache[name]={'fingerprint':fingerprints[name],'olean_sha256':sha(out),'origin':'fresh_lean_cli'}
            write_json(cache_path,cache);result['freshly_compiled'].append(name)
            forced.discard(name);write_json(force_path,sorted(forced));save()
        log=run('type-axioms',[compiler,'--memory=4096','--threads=1','--trust=1','audit/Verify.lean'],env)
        text=log.read_text();records=[]
        for name,values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text):
            axioms=[a.strip() for a in values.split(',') if a.strip()]
            if not set(axioms)<=ALLOWED_AXIOMS:raise ValueError('Unexpected axioms: '+name)
            records.append({'declaration':name,'axioms':axioms})
        if len(records)!=(ROOT/'audit/Verify.lean').read_text().count('#print axioms ') or 'sorryAx' in text:
            raise ValueError('Incomplete/failed axiom audit')
        run('fc-target-type',[compiler,'--memory=4096','--threads=1','--trust=1','audit/FCType.lean'],env)
        graph() # refuse publication if a pinned source changed during the run
        result.update(status='passed',source_count=len(ordered),axioms_audited=records,
                      main_theorem='LogTwo.irrationalityExponent_log_two',explicit_assumptions=[],
                      main_theorem_statement='LogTwo.irrationalityExponent (Real.log 2) = 2',
                      fc_target_numeral_type_checked=True,fc_utilities_linted=False,
                      completed_at_utc=datetime.now(timezone.utc).isoformat())
        save();write_json(ROOT/'evidence/build-results.json',result)
        print(json.dumps({'status':'passed','fresh':len(result['freshly_compiled']),
                          'reused':len(result['reused']),'axioms_audited':len(records),'run_id':run_id}))
    except BaseException as exc:
        result.update(status='failed',error=str(exc),completed_at_utc=datetime.now(timezone.utc).isoformat());save();raise
    finally:
        guard.close()


if __name__=='__main__':main()
