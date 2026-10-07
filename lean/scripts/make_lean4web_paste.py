"""Single-file browser edition with proof-internal goal-history collection disabled.

The kernel, proof scripts and final independent target are unchanged. Info trees
serve editor interaction; the dependency region trades hover/goals for lower
editor-state retention. Style linters are disabled, not compiler diagnostics.
"""
import json
import re
from pathlib import Path

from build_audit import sha, write_json
from make_lean4web import mask_comments_strings

WEB=Path(__file__).resolve().parents[2]/'lean4web'
INTRO='''-- Browser memory improvement: omit proof-internal goal/hover history for dependencies.
-- Outer command information remains, as required by rc4's language server.
-- Proof elaboration, kernel checking, errors and the final axiom audit remain enabled.
set_option Elab.async false
set_option linter.all false
namespace LogTwoWebMemory
syntax (name := quietProof) "logtwo_quiet " tacticSeq : tactic
@[tactic quietProof] meta def evalQuietProof : Lean.Elab.Tactic.Tactic :=
  fun stx => Lean.Elab.withEnableInfoTree false do
    Lean.Elab.Tactic.evalTactic stx[1]
end LogTwoWebMemory

'''
RESTORE='''
-- The independent public definition and final target use normal editor information.
-- Proof-internal wrappers are only inserted in the dependency blocks above.

'''
WRAPPER=' logtwo_quiet'
INSTANCE_IMPORTS=(
    'Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory',
    'Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives',
    'Mathlib.Algebra.Category.ModuleCat.EnoughInjectives',
    'Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal',
)


def quiet_proofs(block):
    """Wrap only actual `by` tokens, leaving strings, comments and newlines intact."""
    code=mask_comments_strings(block)
    positions=[m.end() for m in re.finditer(r'(?<![\w.\'«])by(?![\w\'»?])',code)]
    for position in reversed(positions):
        block=block[:position]+WRAPPER+block[position:]
    return block,len(positions)


def generate():
    base=WEB/'LogTwoLean4WebLite.lean'
    report=json.loads((WEB/'reduction.json').read_text())
    if sha(base)!=report['source_sha256']:
        raise ValueError('Reduced source differs from manifest')
    original=base.read_text();rows=original.splitlines(keepends=True)
    first=report['sources'][0]['first_line']-1
    # Explicit meta imports make the editor-only commands available without
    # depending on incidental tactic reexports; they introduce no project import.
    import_line='public meta import Lean.Elab.Tactic\npublic meta import Lean.Elab.BuiltinEvalCommand\n'
    # Identifier-use indexes omit implicit instance dependencies. Restore the
    # providers needed by the complete cohomology and tensor source modules.
    import_line+='-- Restore implicit instances for FiniteCoverCohomology and LineBundleTensor.\n'
    import_line+=''.join(f'public import {name}\n' for name in INSTANCE_IMPORTS)
    header=''.join(rows[:first])
    header=header.replace('module\n','module\n'+import_line,1)
    chunks=[header,INTRO];insertions=[import_line,INTRO]
    mapping=[];markers=[];quiet=True;wrapped_count=0
    line=sum(len(c.splitlines()) for c in chunks)+1
    for i,r in enumerate(report['sources']):
        if r['module']=='LogTwo.IrrationalityExponent':
            quiet=False
            chunks.append(RESTORE);insertions.append(RESTORE)
            line+=len(RESTORE.splitlines())
        block=''.join(rows[r['first_line']-1:r['last_line']])
        if quiet:
            block,count=quiet_proofs(block);wrapped_count+=count
        else:
            count=0
        mapping.append({**r,'first_line':line,'last_line':line+len(block.splitlines())-1,
                        'wrapped_proofs':count})
        chunks.append(block);line+=len(block.splitlines())
        if (i+1)%25==0 or i+1==len(report['sources']):
            marker=f'\nrun_cmd Lean.logInfo "LogTwo progress: reached module {i+1}/{len(report["sources"])}"\n'
            markers.append(dict(after_module=i+1,line=line+1))
            chunks.append(marker);insertions.append(marker);line+=len(marker.splitlines())
    chunks.append(''.join(rows[report['sources'][-1]['last_line']:]))
    content=''.join(chunks)
    restored=content
    for insertion in insertions:
        if restored.count(insertion)!=1:
            raise ValueError('Ambiguous insertion')
        restored=restored.replace(insertion,'',1)
    restored=restored.replace(WRAPPER,'')
    if restored!=original:
        raise ValueError('Browser optimization altered proof text')
    output=WEB/'LogTwoLean4WebPaste.lean';output.write_text(content)
    metadata=dict(generator='lean/scripts/make_lean4web_paste.py',parent_source_sha256=sha(base),
                  source_sha256=sha(output),lines=len(content.splitlines()),bytes=len(content.encode()),
                  base_source_restored_exactly=True,insertions=insertions,
                  wrapped_proofs=wrapped_count,
                  supplemental_instance_imports=list(INSTANCE_IMPORTS),
                  sources=mapping,progress_markers=markers,scope=__doc__.strip())
    write_json(WEB/'paste-source-map.json',metadata)
    status=WEB/'paste-build-status.json'
    old=json.loads(status.read_text()) if status.exists() else {}
    if old.get('source_sha256')!=metadata['source_sha256']:
        write_json(status,dict(status='not_checked',source_sha256=metadata['source_sha256'],
                              requested_lean='leanprover/lean4:v4.35.0-rc4',
                              scope='Generated optimized single file; full compilation not yet checked.'))
    print(json.dumps({k:v for k,v in metadata.items() if k not in {'sources','insertions','progress_markers'}},indent=2))


if __name__=='__main__':generate()
