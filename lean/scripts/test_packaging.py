"""Small regression checks for source flattening and fail-closed source manifests."""
from pathlib import Path
import hashlib
import json
import tempfile
import unittest
import sys
import subprocess
from unittest.mock import patch
import build_audit
from make_lean4web import mask_comments_strings,module_body
from make_lean4web_lite import header_imports, source_range, has_command_wrapper
from make_lean4web_paste import quiet_proofs, WRAPPER
from check_lite_prefix import compiler_reported_failure


class BrowserProofWrapperTests(unittest.TestCase):
    def test_panic_cannot_pass_even_with_axiom_output(self):
        output="'validTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        self.assertFalse(compiler_reported_failure(output))
        self.assertTrue(compiler_reported_failure('PANIC at outOfBounds\n'+output))
        self.assertTrue(compiler_reported_failure('error(lean.unknownIdentifier): missing\n'+output))

    def test_comments_strings_and_identifiers_are_not_rewritten(self):
        source=('theorem t : True := by\n'
                '  -- by in a comment\n'
                '  have h : True := by trivial\n'
                '  exact h\n/- nested /- by -/ comment -/\n'
                '#eval "by in a string"\n'
                '#check Foo.by\n#check «by»\n')
        rewritten,count=quiet_proofs(source)
        self.assertEqual(count,2)
        self.assertEqual(rewritten.replace(WRAPPER,''),source)
        self.assertIn(':= by logtwo_quiet\n',rewritten)
        self.assertIn(':= by logtwo_quiet trivial',rewritten)

    def test_nested_proof_indentation_and_tactic_names_are_preserved(self):
        source='by\n  by_cases h : P\n  · exact (by trivial)\n  · by_contra hh\n    contradiction\n'
        rewritten,count=quiet_proofs(source)
        self.assertEqual(count,2)
        self.assertEqual(rewritten.replace(WRAPPER,''),source)
        self.assertEqual(rewritten.count('\n'),source.count('\n'))


class HeaderImportTests(unittest.TestCase):
    def test_private_transitive_import_is_not_a_public_reexport(self):
        source='module\nimport Hidden\npublic import Visible\n'
        self.assertEqual(list(header_imports(source)), ['Hidden','Visible'])
        self.assertEqual(list(header_imports(source,public_only=True)), ['Visible'])

    def test_omit_wrapper_must_not_be_detached_from_its_theorem(self):
        self.assertTrue(has_command_wrapper('omit [Fintype ι] in\n\n/-- Documentation -/\n'))
        self.assertTrue(has_command_wrapper('open Foo in\n'))
        self.assertFalse(has_command_wrapper('namespace Foo\n'))

    def test_ilean_range_keeps_the_entire_last_proof_line(self):
        lines=['-- notice\n','theorem unused : True :=\n','  True.intro\n','theorem kept : True := by trivial\n']
        start,end=source_range([0,0,1,12],1)
        self.assertEqual(''.join(lines[start:end]),'theorem unused : True :=\n  True.intro\n')
        self.assertEqual(lines[end], 'theorem kept : True := by trivial\n')

    def test_documentation_import_is_not_a_dependency(self):
        source = ('/- Copyright /- nested -/ -/\nmodule -- note\n'
                  'public import Mathlib.Data.Nat.Basic\n'
                  '/-! Example:\nimport Mathlib\n-/\n'
                  'example : True := by trivial\n')
        self.assertEqual(list(header_imports(source)), ['Mathlib.Data.Nat.Basic'])

    def test_meta_import_and_nested_comments(self):
        source = ('module\n/- ignored /- import Wrong -/ -/\n'
                  'public meta import Lean.Elab.Command\n')
        self.assertEqual(list(header_imports(source)), ['Lean.Elab.Command'])


class FlatteningTests(unittest.TestCase):
    def test_nested_comments_and_strings_do_not_open_scopes(self):
        text='/- namespace Fake /- end Nope -/ -/\n"namespace Fake"\nnamespace Real\n'
        masked=mask_comments_strings(text)
        self.assertEqual(masked.count('\n'),text.count('\n'))
        self.assertNotIn('Fake',masked)
        self.assertIn('namespace Real',masked)

    def test_dotted_namespace_can_close_in_parts(self):
        text='module\npublic import Mathlib\n@[expose] public section\nnamespace A.B\nend B\nend A\n'
        self.assertEqual(module_body(text,'Test'),'namespace A.B\nend B\nend A')

    def test_dotted_namespace_can_close_together(self):
        self.assertEqual(module_body('namespace A.B\nend A.B\n','Test'),'namespace A.B\nend A.B')

    def test_eof_closes_unnamed_section(self):
        self.assertEqual(module_body('noncomputable section\n','Test'),'noncomputable section\nend')

    def test_unclosed_namespace_rejected(self):
        with self.assertRaises(ValueError):module_body('namespace A\n','Test')

    def test_mismatched_end_rejected(self):
        with self.assertRaises(ValueError):module_body('namespace A\nend B\n','Test')


class ManifestTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.root=Path(self.temp.name)
        (self.root/'evidence').mkdir();(self.root/'LogTwo').mkdir();(self.root/'OAI').mkdir()
        self.text='module\npublic import Mathlib\n'
        (self.root/'LogTwo.lean').write_text(self.text)
        (self.root/'lean-toolchain').write_text('lean-test\n')
        (self.root/'lake-manifest.json').write_text('{}')
        (self.root/'evidence/source-manifest.json').write_text(json.dumps({'lean':'lean-test','sources':[
            {'module':'LogTwo','path':'LogTwo.lean','sha256':hashlib.sha256(self.text.encode()).hexdigest()}]}))
        self.patch=patch.object(build_audit,'ROOT',self.root);self.patch.start()

    def tearDown(self):self.patch.stop();self.temp.cleanup()

    def test_matching_manifest_passes(self):self.assertEqual(build_audit.graph()[2],['LogTwo'])

    def test_changed_source_rejected(self):
        (self.root/'LogTwo.lean').write_text(self.text+'-- edit\n')
        with self.assertRaisesRegex(ValueError,'hash mismatch'):build_audit.graph()

    def test_unlisted_source_rejected(self):
        (self.root/'LogTwo/Extra.lean').write_text('module\n')
        with self.assertRaisesRegex(ValueError,'inventory'):build_audit.graph()

    def test_different_toolchain_rejected(self):
        (self.root/'lean-toolchain').write_text('different\n')
        with self.assertRaisesRegex(ValueError,'Toolchain'):build_audit.graph()

    def test_failed_forced_rebuild_stays_pending(self):
        manifest,sources,ordered,fingerprints=build_audit.graph()
        manifest['mathlib_commit']='pinned-mathlib'
        artifact=self.root/'.lake/build/lib/lean/LogTwo.olean'
        artifact.parent.mkdir(parents=True);artifact.write_text('old artifact')
        cache=self.root/'.lake/check-cache.json'
        cache.write_text(json.dumps({'LogTwo':{'fingerprint':fingerprints['LogTwo'],
            'olean_sha256':hashlib.sha256(artifact.read_bytes()).hexdigest()}}))
        previous={'status':'passed','run_id':'previous'}
        (self.root/'evidence/build-results.json').write_text(json.dumps(previous))
        with patch.object(sys,'argv',['build_audit.py','--rebuild-own']), \
             patch.object(build_audit,'graph',return_value=(manifest,sources,ordered,fingerprints)), \
             patch.object(build_audit,'compiler_environment',return_value=(sys.executable,{})), \
             patch.object(build_audit.subprocess,'check_output',side_effect=['Lean test','pinned-mathlib']), \
             patch.object(build_audit.subprocess,'run',return_value=subprocess.CompletedProcess([],1)):
            with self.assertRaisesRegex(RuntimeError,'Failed LogTwo'):build_audit.main()
        self.assertEqual(json.loads((self.root/'.lake/rebuild-pending.json').read_text()),['LogTwo'])
        self.assertNotIn('fingerprint',json.loads(cache.read_text())['LogTwo'])
        self.assertEqual(json.loads((self.root/'evidence/build-results.json').read_text()),previous)
        attempts=list((self.root/'evidence/runs').glob('*/result.json'))
        self.assertEqual(len(attempts),1)
        self.assertEqual(json.loads(attempts[0].read_text())['status'],'failed')


if __name__=='__main__':unittest.main()
