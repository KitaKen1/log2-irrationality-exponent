"""Check source parity, generation, FC target, local links and source-only packaging."""
from pathlib import Path
import hashlib
import json
import re
from urllib.parse import unquote,urlsplit
from build_audit import graph
from make_lean4web import mask_comments_strings
from notice_updates import verify_notice_update

ROOT=Path(__file__).resolve().parents[2]


def main():
    manifest,sources,ordered,_=graph()
    fc=(ROOT/'FClikelean/LogTwoIrrationalityExponent.lean').read_text()
    statement=(ROOT/'lean/LogTwo/IrrationalityExponent.lean').read_text()
    definitions=statement.split('namespace LogTwo\n\n',1)[1].split('\nend LogTwo',1)[0].strip()
    assert definitions in fc,'FC definitions differ'
    fc_code=mask_comments_strings(fc)
    assert 'OAI.' not in fc and 'abbrev ' not in fc_code
    assert len(re.findall(r'^noncomputable def ',fc_code,re.M))==1,'Expected one independent definition'
    assert re.search(r'theorem irrationalityExponent_log_two\s*:\s*irrationalityExponent \(Real.log 2\) = answer\(2\)',fc)
    audit=json.loads((ROOT/'lean/evidence/build-results.json').read_text())
    assert audit['status']=='passed'
    same_split_source=audit['source_manifest_sha256']==hashlib.sha256((ROOT/'lean/evidence/source-manifest.json').read_bytes()).hexdigest()
    notice_files=0 if same_split_source else verify_notice_update(ROOT/'lean',audit['source_manifest_sha256'])
    assert audit['main_theorem']=='LogTwo.irrationalityExponent_log_two'
    assert audit['main_theorem_statement']=='LogTwo.irrationalityExponent (Real.log 2) = 2'
    web=ROOT/'lean4web/LogTwoLean4Web.lean'
    mapping=json.loads((web.parent/'source-map.json').read_text())
    assert hashlib.sha256(web.read_bytes()).hexdigest()==mapping['sha256']
    assert len(mapping['sources'])==len(ordered)==manifest['module_count']
    assert {x['module']:x['sha256'] for x in mapping['sources']}=={n:r['sha256'] for n,r in sources.items()}
    for p in [ROOT/'lean'/r['path'] for r in sources.values()]+[web]:
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',mask_comments_strings(p.read_text())),p
    assert re.findall(r'^(?:public )?import (.+)$',web.read_text(),re.M)==['Mathlib']
    assert web.read_text().rstrip().endswith('#print axioms LogTwo.irrationalityExponent_log_two')
    links=0
    for p in [ROOT/'README.md',ROOT/'lean/README.md',ROOT/'lean4web/README.md',
              ROOT/'FClikelean/README.md',ROOT/'lean4web/checkpoints/README.md']:
        for target in re.findall(r'\]\(([^\s)]+)\)',p.read_text()):
            u=urlsplit(target)
            if u.scheme or u.netloc or not u.path:continue
            assert (p.parent/unquote(u.path)).exists(),(str(p),target)
            links+=1
    web_status=json.loads((ROOT/'lean4web/build-status.json').read_text())
    same_web_source=web_status.get('source_sha256')==mapping['sha256']
    result={'status':'passed','pinned_source_files':len(ordered),'FC_definitions_identical':True,
            'FC_independent_definition_count':1,
            'split_audit_matches_current_sources':same_split_source,
            'split_audit_code_preserved_by_notice_only_update':bool(notice_files),
            'notice_only_files_verified':notice_files,
            'FC_draft_contains_intentional_sorry':True,'FC_utilities_linted':False,
            'complete_sources_without_proof_holes':True,'standalone_imports':['Mathlib'],
            'standalone_lines':mapping['lines'],'local_markdown_links':links,
            'standalone_build_status':web_status['status'] if same_web_source else 'current_source_not_checked',
            'standalone_build_matches_current_source':same_web_source}
    lite=ROOT/'lean4web/LogTwoLean4WebLite.lean'
    if lite.exists():
        reduced=json.loads((lite.parent/'reduction.json').read_text())
        lite_text=lite.read_text()
        assert hashlib.sha256(lite.read_bytes()).hexdigest()==reduced['source_sha256']
        assert reduced['baseline_sha256']==mapping['sha256']
        assert reduced['lines']==len(lite_text.splitlines())<mapping['lines']
        assert definitions in lite_text,'Reduced edition changed the independent definition'
        assert lite_text.rstrip().endswith('#print axioms LogTwo.irrationalityExponent_log_two')
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',mask_comments_strings(lite_text))
        assert lite_text.count('Modification notice for the LogTwo project.')==notice_files
        assert reduced['removed_declarations']==len(reduced['removed'])
        assert 'Mathlib' not in reduced['imports']
        lite_status=json.loads((lite.parent/'lite-build-status.json').read_text())
        assert lite_status['source_sha256']==reduced['source_sha256']
        result['reduced_edition']={'lines':reduced['lines'],'removed_lemmas':reduced['removed_declarations'],
                                   'independent_definition_identical':True,
                                   'build_status':lite_status['status']}
        sequential=ROOT/'lean4web/LogTwoLean4WebSequential.lean'
        if sequential.exists():
            diagnostic=json.loads((sequential.parent/'sequential-source-map.json').read_text())
            seq_text=sequential.read_text()
            assert hashlib.sha256(sequential.read_bytes()).hexdigest()==diagnostic['source_sha256']
            assert diagnostic['parent_source_sha256']==reduced['source_sha256']
            assert diagnostic['lines']==len(seq_text.splitlines())
            assert diagnostic['bytes']==len(sequential.read_bytes())
            assert diagnostic['base_source_restored_exactly'] and not diagnostic['elaboration_async']
            from make_lean4web_sequential import INTRO
            assert seq_text.count(INTRO)==1
            restored=seq_text.replace(INTRO,'',1)
            steps=list(range(25,len(ordered)+1,25))
            if steps[-1]!=len(ordered):steps.append(len(ordered))
            assert [m['after_module'] for m in diagnostic['progress_markers']]==steps
            for marker in diagnostic['progress_markers']:
                command=f'#eval IO.println "LogTwo progress: reached module {marker["after_module"]}/{len(ordered)}"'
                assert seq_text.splitlines()[marker['line']-1]==command
                assert restored.count('\n'+command+'\n')==1
                restored=restored.replace('\n'+command+'\n','',1)
            assert restored==lite_text,'Sequential edition changed the reduced proof text'
            seq_lines=seq_text.splitlines()
            lite_lines=lite_text.splitlines()
            assert len(diagnostic['sources'])==len(reduced['sources'])
            for original,shifted in zip(reduced['sources'],diagnostic['sources']):
                assert original['module']==shifted['module']
                assert lite_lines[original['first_line']-1:original['last_line']]==seq_lines[shifted['first_line']-1:shifted['last_line']]
            seq_status=json.loads((sequential.parent/'sequential-build-status.json').read_text())
            assert seq_status['source_sha256']==diagnostic['source_sha256']
            result['sequential_edition']={'lines':diagnostic['lines'],
                                          'reduced_proof_text_preserved_exactly':True,
                                          'source_map_verified':True,
                                          'build_status':seq_status['status']}
        if (ROOT/'lean4web/checkpoints/manifest.json').exists():
            from check_lean4web_checkpoints import validate_sources
            checkpoints=validate_sources()
            result['checkpoint_edition']={
                'modules':checkpoints['module_count'],
                'original_source_blocks_preserved':checkpoints['source_module_count'],
                'max_source_lines':max(r['lines'] for r in checkpoints['modules']),
                'whole_proof_compilation_inferred':False}
        paste=ROOT/'lean4web/LogTwoLean4WebPaste.lean'
        if paste.exists():
            from make_lean4web_paste import INTRO, RESTORE, WRAPPER
            paste_map=json.loads((paste.parent/'paste-source-map.json').read_text())
            paste_text=paste.read_text()
            assert hashlib.sha256(paste.read_bytes()).hexdigest()==paste_map['source_sha256']
            assert paste_map['parent_source_sha256']==reduced['source_sha256']
            assert paste_map['lines']==len(paste_text.splitlines())
            assert paste_text.count(INTRO)==paste_text.count(RESTORE)==1
            restored=paste_text
            for insertion in paste_map['insertions']:
                assert restored.count(insertion)==1
                restored=restored.replace(insertion,'',1)
            assert restored.count(WRAPPER)==paste_map['wrapped_proofs']
            restored=restored.replace(WRAPPER,'')
            assert restored==lite_text,'Paste edition altered original proof text'
            assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',mask_comments_strings(paste_text))
            assert definitions in paste_text
            assert paste_text.rstrip().endswith('#print axioms LogTwo.irrationalityExponent_log_two')
            from make_lean4web_lite import header_imports
            assert all(n.startswith(('Mathlib.','Lean.','Batteries.','Aesop.','Qq.')) for n in header_imports(paste_text))
            paste_status=json.loads((paste.parent/'paste-build-status.json').read_text())
            assert paste_status['source_sha256']==paste_map['source_sha256']
            result['paste_edition']={'lines':paste_map['lines'],
                                     'original_proof_preserved_exactly':True,
                                     'no_project_imports':True,
                                     'final_independent_target_unchanged':True,
                                     'build_status':paste_status['status']}
    (ROOT/'lean/evidence/package-check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
