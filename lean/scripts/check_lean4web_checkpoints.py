"""Bounded, single-worker rc4 build with hash-checked reusable checkpoints.

Run repeatedly to continue. Failed or interrupted outputs never enter the cache.
Only a successful fresh final type/axiom audit marks the entire proof as passed.
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
import shutil
import subprocess
import tempfile
import time
import uuid

from build_audit import sha, write_json, ALLOWED_AXIOMS
from compiler_environment import compiler_environment
from make_lean4web_checkpoints import ROOT, WEB, DEST, TOOLCHAIN, MATHLIB, TARGET, PREFIX

FLAGS = ['--memory=4096','--threads=1','--trust=1']
SUFFIXES = ['.olean','.olean.private','.olean.server','.ilean','.ir']


def fingerprint(source_hash, environment, dependencies):
    return hashlib.sha256(json.dumps([source_hash,environment,dependencies],
                                     sort_keys=True).encode()).hexdigest()


def dependency_key(entry):
    # Rebuilding identical artifacts need not invalidate clients merely because
    # the verification log lives in a new run directory.
    return {k:entry[k] for k in ('fingerprint','artifacts')}


def cache_matches(entry, expected, build, module):
    if entry.get('fingerprint') != expected:
        return False
    base=Path(*module.split('.'))
    artifacts=entry.get('artifacts',{})
    if str(base.with_suffix('.olean')) not in artifacts:
        return False
    allowed={str(base.with_suffix(s)) for s in SUFFIXES}
    if not set(artifacts) <= allowed:
        return False
    return all((build/p).is_file() and sha(build/p)==h for p,h in artifacts.items())


def audit_axioms(output):
    prints=re.findall(r"'"+re.escape(TARGET)+r"' depends on axioms: \[([^\]]*)\]",output)
    if len(prints)!=1 or 'sorryAx' in output:
        return False
    return {a.strip() for a in prints[0].split(',') if a.strip()} <= ALLOWED_AXIOMS


def validate_sources():
    manifest=json.loads((DEST/'manifest.json').read_text())
    if manifest['lean']!=TOOLCHAIN or manifest['mathlib_commit']!=MATHLIB:
        raise ValueError('Checkpoint version mismatch')
    reduced=json.loads((WEB/'reduction.json').read_text())
    lite=WEB/'LogTwoLean4WebLite.lean'
    if sha(lite)!=manifest['parent_source_sha256'] or sha(lite)!=reduced['source_sha256']:
        raise ValueError('Checkpoint parent source changed')
    rows=lite.read_text().splitlines(keepends=True)
    blocks={r['module']:''.join(rows[r['first_line']-1:r['last_line']]) for r in reduced['sources']}
    seen=set(); originals=[]
    for i,r in enumerate(manifest['modules']):
        expected=f'{PREFIX}.Part{i:03d}'
        if r['module']!=expected or r['path']!=str(Path(*expected.split('.')).with_suffix('.lean')):
            raise ValueError('Unexpected checkpoint path/order')
        if not set(r['imports'])<=seen:
            raise ValueError('Missing or forward checkpoint dependency')
        path=DEST/r['path']
        if sha(path)!=r['sha256']:
            raise ValueError('Checkpoint source changed: '+r['path'])
        body=''.join(path.read_text().splitlines(keepends=True)[r['body_start_line']-1:])
        if body!=''.join(blocks[n] for n in r['source_modules']):
            raise ValueError('Checkpoint changed a proof block')
        seen.add(expected); originals.extend(r['source_modules'])
    if originals!=[r['module'] for r in reduced['sources']]:
        raise ValueError('Proof blocks omitted, reordered or duplicated')
    if manifest['module_count']!=len(seen) or manifest['source_module_count']!=len(originals):
        raise ValueError('Incorrect manifest counts')
    target=manifest['target']
    if target['path']!='Target.lean' or not set(target['imports'])<=seen or target['declaration']!=TARGET:
        raise ValueError('Unexpected target')
    if sha(DEST/'Target.lean')!=target['sha256']:
        raise ValueError('Final target source changed')
    return manifest


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--through',type=int,help='Check only the first N checkpoints; never a full proof pass')
    parser.add_argument('--max-new-chunks',type=int,default=2,help='Maximum fresh checkpoint compilations per invocation')
    parser.add_argument('--total-seconds',type=int,default=300)
    parser.add_argument('--chunk-seconds',type=int,default=180)
    parser.add_argument('--check-sources-only',action='store_true')
    args=parser.parse_args(argv)
    if args.max_new_chunks<0 or min(args.total_seconds,args.chunk_seconds)<1:
        parser.error('Invalid resource bound')
    manifest=validate_sources()
    if args.through is not None and not 1<=args.through<=manifest['module_count']:
        parser.error('--through is outside the checkpoint range')
    if args.check_sources_only:
        print(json.dumps({'status':'source_parity_passed','checkpoints':manifest['module_count'],
                          'preserved_original_modules':manifest['source_module_count']}));return 0
    guard=(ROOT/'lean/.lake/check.lock').open('a')
    try:
        fcntl.flock(guard,fcntl.LOCK_EX|fcntl.LOCK_NB)
    except BlockingIOError:
        guard.close();raise SystemExit('Another proof checker is active; no compiler started')
    run_id=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ-')+uuid.uuid4().hex[:8]
    directory=WEB/'evidence'/('checkpoints-'+run_id)
    directory.mkdir(parents=True)
    build=WEB/'.lake/checkpoints/lib/lean'
    build.mkdir(parents=True,exist_ok=True)
    cache_path=WEB/'.lake/checkpoints/cache.json'
    cache=json.loads(cache_path.read_text()) if cache_path.exists() else {}
    record=dict(status='running',run_id=run_id,edition='local_rc4_checkpoints',
                manifest_sha256=sha(DEST/'manifest.json'),
                parent_source_sha256=manifest['parent_source_sha256'],
                resource_policy=dict(compilers=1,threads=1,lean_memory_mib=4096,trust=1,
                                     total_seconds=args.total_seconds,chunk_seconds=args.chunk_seconds),
                fresh=[],reused=[],commands=[],final_log_two_theorem_checked=False,
                browser_execution_performed=False)
    start=time.monotonic()

    def save():
        record['elapsed_seconds']=round(time.monotonic()-start,3)
        write_json(directory/'result.json',record)
        write_json(WEB/'checkpoint-build-status.json',record | {'result':str((directory/'result.json').relative_to(WEB))})

    def run(label,command,env):
        remaining=args.total_seconds-(time.monotonic()-start)
        if remaining<1:
            record.update(status='partial',stop_reason='total_time_budget');return False
        budget=min(args.chunk_seconds,remaining)
        log=directory/(label+'.log')
        before=resource.getrusage(resource.RUSAGE_CHILDREN)
        started=time.monotonic();code=None;timed_out=False;proc=None
        print(f'CHECK {label} (one compiler, 4096 MiB, {budget:.0f}s cap)',flush=True)
        with log.open('w') as stream:
            try:
                proc=subprocess.Popen(command,cwd=DEST,env=env,stdout=stream,stderr=subprocess.STDOUT)
                code=proc.wait(timeout=budget)
            except subprocess.TimeoutExpired:
                timed_out=True;proc.kill();proc.wait()
            except BaseException:
                if proc is not None and proc.poll() is None:
                    proc.kill();proc.wait()
                raise
        after=resource.getrusage(resource.RUSAGE_CHILDREN)
        output=log.read_text()
        item=dict(label=label,exit_code=code,time_limit_reached=timed_out,
                  elapsed_seconds=round(time.monotonic()-started,3),
                  compiler_cpu_seconds=round(after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,3),
                  log=str(log.relative_to(WEB)),log_sha256=sha(log))
        record['commands'].append(item)
        if timed_out or code!=0 or 'sorryAx' in output or re.search(r'\berror(?:\([^)]*\))?:',output):
            record.update(status='time_limit' if timed_out else 'failed',stopped_at=label)
            save();return False
        save();return True

    try:
        save()
        compiler,env=compiler_environment(WEB)
        version=subprocess.check_output([compiler,'--version'],text=True,timeout=15).strip()
        if not version.startswith('Lean (version 4.35.0-rc4,'):
            raise ValueError('Unexpected Lean version')
        actual=subprocess.check_output(['git','-C',str(WEB/'.lake/packages/mathlib'),'rev-parse','HEAD'],
                                       text=True,timeout=15).strip()
        if actual!=MATHLIB:
            raise ValueError('Unexpected Mathlib revision')
        environment=dict(compiler_sha256=sha(compiler),version=version,mathlib_commit=actual,
                         lake_manifest_sha256=sha(WEB/'lake-manifest.json'),flags=FLAGS)
        record['environment']=environment
        # Avoid accidentally resolving LogTwo modules from the old v4.34.1 tree.
        env=dict(env);env['LEAN_PATH']=str(build)+os.pathsep+env['LEAN_PATH']
        verified={}
        selected=manifest['modules'][:args.through] if args.through else manifest['modules']
        for r in selected:
            name=r['module']
            dep_records={n:dependency_key(verified[n]) for n in r['imports']}
            expected=fingerprint(r['sha256'],environment,dep_records)
            if cache_matches(cache.get(name,{}),expected,build,name):
                record['reused'].append(name);verified[name]=cache[name];continue
            if len(record['fresh'])>=args.max_new_chunks:
                record.update(status='partial',stop_reason='new_checkpoint_budget',next_checkpoint=name);break
            # Mark invalid before starting; even an interrupt cannot reuse a stale artifact.
            cache[name]={'status':'pending'};write_json(cache_path,cache)
            with tempfile.TemporaryDirectory(prefix='compile-',dir=WEB/'.lake/checkpoints') as tmp:
                out=Path(tmp)/'checkpoint.olean'
                command=[compiler,*FLAGS,'--root='+str(DEST),'-o',str(out),
                         '-i',str(out.with_suffix('.ilean')),r['path']]
                if not run(name,command,env):
                    break
                if sha(DEST/r['path'])!=r['sha256'] or not out.is_file():
                    raise ValueError('Changed source or missing artifact: '+name)
                base=build/Path(*name.split('.'))
                base.parent.mkdir(parents=True,exist_ok=True)
                produced={s:out.with_suffix(s) for s in SUFFIXES if out.with_suffix(s).is_file()}
                for s in SUFFIXES:
                    old=base.with_suffix(s)
                    if s in produced:
                        shutil.move(str(produced[s]),str(old))
                    elif old.exists():
                        old.unlink()
                entry=dict(fingerprint=expected,
                           artifacts={str(base.with_suffix(s).relative_to(build)):sha(base.with_suffix(s)) for s in produced},
                           verified_by=str((directory/'result.json').relative_to(WEB)))
                cache[name]=entry;write_json(cache_path,cache)
                verified[name]=entry;record['fresh'].append(name);save()
        else:
            if len(selected)<manifest['module_count']:
                record.update(status='partial',stop_reason='requested_prefix_complete')
            else:
                command=[compiler,*FLAGS,'--root='+str(DEST),'Target.lean']
                if run('final-target',command,env):
                    if not audit_axioms((directory/'final-target.log').read_text()):
                        raise ValueError('Missing or unexpected final axiom print')
                    validate_sources()
                    record.update(status='passed',final_log_two_theorem_checked=True,
                                  target_statement='LogTwo.irrationalityExponent (Real.log 2) = 2')
        if record['status']=='running':
            record.update(status='partial',stop_reason='bounded_run_complete')
        # No completed result may attest to a different source generation.
        if sha(DEST/'manifest.json')!=record['manifest_sha256']:
            raise ValueError('Checkpoint manifest changed during the build')
        validate_sources()
    except BaseException as exc:
        record.update(status='failed',error=str(exc))
        if isinstance(exc,KeyboardInterrupt):
            record['stop_reason']='interrupted'
    finally:
        save();guard.close()
    print(json.dumps({k:v for k,v in record.items() if k not in {'commands','environment','fresh','reused'}},indent=2))
    print(f'Fresh: {len(record["fresh"])}; reused: {len(record["reused"])}; evidence: {directory}')
    return 0 if record['status'] in {'passed','partial'} else 1


if __name__=='__main__':
    raise SystemExit(main())
