"""Regression tests for checkpoint validity and failure-safe resumption."""
from contextlib import ExitStack
from pathlib import Path
import json
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_lean4web_checkpoints as check
from build_audit import sha, write_json


class CacheTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        self.module='LogTwoCheckpoints.Part000'
        self.base=self.root/'LogTwoCheckpoints/Part000'
        self.base.parent.mkdir()
        self.base.with_suffix('.olean').write_bytes(b'compiled')
        self.base.with_suffix('.olean.private').write_bytes(b'private companion')
        self.entry={'fingerprint':'valid','artifacts':{
            str(self.base.with_suffix(s).relative_to(self.root)):sha(self.base.with_suffix(s))
            for s in ['.olean','.olean.private']}}

    def test_all_artifacts_required(self):
        self.assertTrue(check.cache_matches(self.entry,'valid',self.root,self.module))
        self.base.with_suffix('.olean.private').unlink()
        self.assertFalse(check.cache_matches(self.entry,'valid',self.root,self.module))

    def test_corruption_and_other_fingerprint_rejected(self):
        self.assertFalse(check.cache_matches(self.entry,'changed',self.root,self.module))
        self.base.with_suffix('.olean').write_bytes(b'corrupt')
        self.assertFalse(check.cache_matches(self.entry,'valid',self.root,self.module))

    def test_pending_or_missing_primary_is_never_a_hit(self):
        self.assertFalse(check.cache_matches({'status':'pending'},'valid',self.root,self.module))
        self.entry['artifacts'].pop('LogTwoCheckpoints/Part000.olean')
        self.assertFalse(check.cache_matches(self.entry,'valid',self.root,self.module))

    def test_cache_cannot_point_to_another_module_or_outside_build(self):
        self.entry['artifacts']['../outside']='hash'
        self.assertFalse(check.cache_matches(self.entry,'valid',self.root,self.module))

    def test_source_toolchain_and_dependency_change_invalidate(self):
        base=check.fingerprint('source',{'compiler':'rc4'},{'dep':'old'})
        for s,e,d in [('changed',{'compiler':'rc4'},{'dep':'old'}),
                      ('source',{'compiler':'other'},{'dep':'old'}),
                      ('source',{'compiler':'rc4'},{'dep':'new'})]:
            self.assertNotEqual(base,check.fingerprint(s,e,d))

    def test_provenance_only_change_does_not_force_rebuild(self):
        first=self.entry | {'verified_by':'first-run'}
        later=self.entry | {'verified_by':'later-run'}
        self.assertEqual(check.dependency_key(first),check.dependency_key(later))


class AuditTests(unittest.TestCase):
    def test_only_the_independent_final_target_can_pass(self):
        text=f"'{check.TARGET}' depends on axioms: [propext, Classical.choice, Quot.sound]"
        self.assertTrue(check.audit_axioms(text))
        self.assertFalse(check.audit_axioms(text.replace(check.TARGET,'Some.conditionalLemma')))
        self.assertFalse(check.audit_axioms(text.replace('propext','sorryAx')))
        self.assertFalse(check.audit_axioms(text.replace('propext','customAxiom')))
        self.assertFalse(check.audit_axioms(text+'\n'+text))
        self.assertFalse(check.audit_axioms(''))


class FailedBuildTests(unittest.TestCase):
    def test_failed_compiler_output_is_quarantined_and_old_entry_invalidated(self):
        # Fake process only exercises orchestration; this is not a Lean proof check.
        with tempfile.TemporaryDirectory() as temp, ExitStack() as stack:
            root=Path(temp);web=root/'lean4web';dest=web/'checkpoints'
            (root/'lean/.lake').mkdir(parents=True)
            (dest/'LogTwoCheckpoints').mkdir(parents=True)
            source=dest/'LogTwoCheckpoints/Part000.lean'
            source.write_text('-- test fixture\n')
            compiler=root/'fake-compiler';compiler.write_text('test')
            (web/'lake-manifest.json').write_text('{}')
            (dest/'manifest.json').write_text('{}')
            build=web/'.lake/checkpoints/lib/lean/LogTwoCheckpoints'
            build.mkdir(parents=True)
            old=build/'Part000.olean';old.write_bytes(b'old valid artifact')
            cache_path=web/'.lake/checkpoints/cache.json'
            write_json(cache_path,{'LogTwoCheckpoints.Part000':{'fingerprint':'stale'}})
            manifest={'module_count':1,'parent_source_sha256':'parent','modules':[
                {'module':'LogTwoCheckpoints.Part000','path':'LogTwoCheckpoints/Part000.lean',
                 'sha256':sha(source),'imports':[]}]}
            class FailedProcess:
                def __init__(self,cmd,**kwargs):
                    self.returncode=None
                    Path(cmd[cmd.index('-o')+1]).write_bytes(b'bad partial output')
                def wait(self,timeout=None):self.returncode=1;return 1
                def poll(self):return self.returncode
                def kill(self):self.returncode=-9
            for key,value in [('ROOT',root),('WEB',web),('DEST',dest)]:
                stack.enter_context(patch.object(check,key,value))
            stack.enter_context(patch.object(check,'validate_sources',return_value=manifest))
            stack.enter_context(patch.object(check,'compiler_environment',return_value=(str(compiler),{'LEAN_PATH':''})))
            stack.enter_context(patch.object(check.subprocess,'check_output',side_effect=[
                'Lean (version 4.35.0-rc4, test)',check.MATHLIB]))
            stack.enter_context(patch.object(check.subprocess,'Popen',FailedProcess))
            self.assertEqual(check.main(['--max-new-chunks','1']),1)
            self.assertEqual(old.read_bytes(),b'old valid artifact')
            self.assertEqual(json.loads(cache_path.read_text())['LogTwoCheckpoints.Part000'],{'status':'pending'})
            result=json.loads((web/'checkpoint-build-status.json').read_text())
            self.assertEqual(result['status'],'failed')
            self.assertFalse(result['final_log_two_theorem_checked'])
            self.assertEqual(result['fresh'],[])
            self.assertEqual(list((web/'.lake/checkpoints').glob('compile-*')),[])


if __name__=='__main__':
    unittest.main()
