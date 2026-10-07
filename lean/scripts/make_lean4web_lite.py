"""Generate a smaller rc4 edition; generation is not a proof check.

Keep all attributed declarations, instances, structures, and private helpers.
Remove only plain lemmas unreachable from the retained source text and the final
target. Use compiled identifier references to narrow the Mathlib import list.
Source ranges come from the cached split build and are checked against source
names. The split proof and the full generated edition are never changed.
"""
from collections import defaultdict
from pathlib import Path
import hashlib
import json
import re

from build_audit import ROOT as LEAN, graph, sha, write_json
from make_lean4web import mask_comments_strings, module_body, rc4_compatibility, RC4_EDITS
from notice_updates import verify_notice_update

WEB = LEAN.parent / 'lean4web'
TARGET = 'LogTwo.irrationalityExponent_log_two'


def source_range(span, offset):
    """Convert zero-based .ilean start/end positions to a whole-line slice."""
    return span[0] + offset, span[2] + offset + 1


def has_command_wrapper(prefix):
    """Do not detach a declaration from an `omit/include/open/... in` command."""
    code = mask_comments_strings(prefix).rstrip()
    return bool(code) and (code.splitlines()[-1].strip() == 'in' or code.endswith(' in'))


def header_imports(text, public_only=False):
    """Read Lean's initial module header, skipping nested comments.

    Stop at the first non-header command: imports in documentation/examples
    must never create an edge back to the umbrella Mathlib import.
    """
    i, depth, cleaned, is_module = 0, 0, [], False
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth:
            if text.startswith('-/', i):
                depth -= 1; i += 2; continue
            i += 1; continue
        if text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
            continue
        if text[i] == '\n':
            line = ''.join(cleaned).strip(); cleaned = []
            if line:
                if line.startswith('module') or line == 'prelude':
                    is_module = is_module or line.startswith('module')
                elif re.fullmatch(r'(?:(?:public|meta) )*import [\w. ]+', line):
                    if not public_only or not is_module or 'public' in line.split('import ',1)[0].split():
                        yield from line.split('import ', 1)[1].split()
                else:
                    return
        else:
            cleaned.append(text[i])
        i += 1


def collect():
    manifest, sources, ordered, _ = graph()
    audit = json.loads((LEAN / 'evidence/build-results.json').read_text())
    verify_notice_update(LEAN, audit['source_manifest_sha256'])
    texts, candidates, indexes, artifacts = {}, {}, {}, []
    # Implicit typeclass dependencies are absent from identifier usage tables.
    external = {'Mathlib.Analysis.Complex.Polynomial.Basic'}
    for name in ordered:
        rec = sources[name]
        text = (LEAN / rec['path']).read_text()
        texts[name] = text
        external.update(d for d in header_imports(text) if d not in sources and d != 'Mathlib')
        index_path = LEAN / '.lake/build/lib/lean' / Path(rec['path']).with_suffix('.ilean')
        index = json.loads(index_path.read_text())
        if index['module'] != name:
            raise ValueError('Cached index module mismatch: ' + name)
        indexes[name] = index
        artifacts.append({'module': name, 'ilean_sha256': sha(index_path)})
        offset = 0
        if text.startswith('/-\nModification notice'):
            end = text.index('-/\n\n') + len('-/\n\n')
            offset = text[:end].count('\n')
        lines = text.splitlines(keepends=True)
        spans = defaultdict(list)
        for decl, span in index['decls'].items():
            spans[tuple(span[:4])].append(decl)
        for span, names in spans.items():
            # Shared source spans can include generated/aliased declarations.
            if len(names) != 1 or span[1] != 0:
                continue
            decl = names[0]
            # .ilean uses zero-based line positions; the end line is included.
            start, end = source_range(span, offset)
            if has_command_wrapper(''.join(lines[:start])):
                continue
            tail = lines[end-1].encode('utf-16-le')[2*span[3]:].decode('utf-16-le').strip()
            if tail and not tail.startswith('--'):
                continue  # Do not cut a command extending beyond the recorded range.
            body = ''.join(lines[start:end])
            code = mask_comments_strings(body).lstrip()
            match = re.match(r'(?:theorem|lemma)\s+([^\s(:]+)', code)
            if match is None:
                continue
            base = decl.rsplit('.', 1)[-1]
            if match[1].rsplit('.', 1)[-1] != base:
                continue  # Fail closed: retain ambiguous cached positions.
            candidates[decl] = dict(module=name, start=start, end=end, text=body, base=base)
        for key in index['references']:
            mod = json.loads(key).get('c', {}).get('m', '')
            if mod.startswith(('Mathlib.', 'Lean.', 'Batteries.', 'Aesop.', 'Qq.')):
                external.add(mod)

    bybase = defaultdict(set)
    bymodule = defaultdict(list)
    for name, rec in candidates.items():
        bybase[rec['base']].add(name)
        bymodule[rec['module']].append(rec)

    def refs(text):
        # Deliberately includes comments/strings and every namespace sharing a
        # basename. False positives retain extra lemmas rather than remove them.
        result = set()
        for token in re.findall(r"[\w'₀-₉]+", text):
            result.update(bybase.get(token, ()))
        return result

    roots = {TARGET}
    for mod, text in texts.items():
        removed_lines = {i for r in bymodule[mod] for i in range(r['start'], r['end'])}
        roots.update(refs(''.join(line for i, line in enumerate(text.splitlines(keepends=True))
                                  if i not in removed_lines)))
    edges = {n: refs(r['text']) - {n} for n, r in candidates.items()}
    # Resolved references supplement conservative spelling-based dependencies.
    for index in indexes.values():
        for key, record in index['references'].items():
            dep = json.loads(key).get('c', {}).get('n')
            if dep not in candidates:
                continue
            for usage in record['usages']:
                owner = usage[4] if len(usage) > 4 else None
                if owner in candidates:
                    edges[owner].add(dep)
                else:
                    roots.add(dep)
    kept, todo = set(), list(roots)
    while todo:
        name = todo.pop()
        if name not in kept:
            kept.add(name); todo.extend(edges.get(name, set()) - kept)
    removed = {n: r for n, r in candidates.items() if n not in kept}
    return sources, ordered, texts, external, removed, artifacts


def minimal_imports(external):
    mathlib = WEB / '.lake/packages/mathlib'
    cache = {}

    def closure(names, public_only=False):
        seen, todo = set(), list(names)
        while todo:
            name = todo.pop()
            if name in seen or not (name == 'Mathlib' or name.startswith('Mathlib.')):
                continue
            seen.add(name)
            key = (name, public_only)
            if key not in cache:
                path = mathlib / Path(*name.split('.')).with_suffix('.lean')
                if not path.exists():
                    raise ValueError('Missing rc4 import: ' + name)
                cache[key] = list(header_imports(path.read_text(), public_only=public_only))
            todo.extend(cache[key])
        return seen

    full, selected = closure({'Mathlib'}), closure(external)
    if 'Mathlib' in selected:
        raise ValueError('Umbrella Mathlib import remains')
    roots = set(external)
    for name in external:
        if name.startswith('Mathlib.'):
            # A private transitive import loads a module but does not expose its
            # declarations to our file in Lean's public module system.
            roots.difference_update(closure({name}, public_only=True) - {name})
    assert closure(roots) == selected
    return sorted(roots), len(full), len(selected)


def main():
    sources, ordered, texts, external, removed, artifacts = collect()
    imports, full_count, selected_count = minimal_imports(external)
    header = '''/-
Copyright 2026 Kenta Kitamura. Portions: OpenAI, openai/math (Apache-2.0).
Modified for LogTwo: flattening, rc4 compatibility, narrower imports, and
removal of unused plain lemmas. Individual provenance notices are retained.
See ../THIRD_PARTY_NOTICES.txt and ../LICENSES/openai-math-Apache-2.0.txt.
-/
module
'''
    header += ''.join(f'public import {name}\n' for name in imports)
    header += '''@[expose] public section

/-! Reduced proof source for Lean v4.35.0-rc4.
The public target and its independent definition are unchanged.
Generation is not verification: see lite-build-status.json and reduction.json.
-/
'''
    chunks, mapping = [header], []
    line = len(header.splitlines()) + 1
    bymodule = defaultdict(list)
    for decl, rec in removed.items():
        bymodule[rec['module']].append((decl, rec))
    for index, name in enumerate(ordered):
        body = rc4_compatibility(texts[name], name)
        for decl, rec in bymodule[name]:
            fragment = rec['text']
            for old, new, _ in RC4_EDITS.get(name, []):
                fragment = fragment.replace(old, new)
            if body.count(fragment) != 1:
                raise ValueError('Removal range is not unique after compatibility edits: ' + decl)
            body = body.replace(fragment, '', 1)
        body = module_body(body, name)
        body = re.sub(r'^See (?:\.\./)+THIRD_PARTY_NOTICES\.txt for provenance and the recorded changes\.$',
                      'See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.', body, flags=re.M)
        if bymodule[name]:
            body = '-- Modified in this edition: unused plain lemmas removed; see reduction.json.\n' + body
        # Keep source notices, docstrings and local scopes; only collapse excess blank lines.
        body = re.sub(r'\n{3,}', '\n\n', body)
        chunk = f'\n-- Source: {sources[name]["path"]}\nsection Source{index:04d}\n{body}\nend Source{index:04d}\n'
        mapping.append(dict(module=name, first_line=line, last_line=line+len(chunk.splitlines())-1,
                            source_sha256=sources[name]['sha256']))
        chunks.append(chunk); line += len(chunk.splitlines())
    chunks.append(f'\nexample : LogTwo.irrationalityExponent (Real.log 2) = 2 :=\n  {TARGET}\n#print axioms {TARGET}\n')
    content = ''.join(chunks)
    if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', mask_comments_strings(content)):
        raise ValueError('Unexpected proof hole or unchecked construct')
    output = WEB / 'LogTwoLean4WebLite.lean'
    output.write_text(content)
    original = WEB / 'LogTwoLean4Web.lean'
    report = dict(generator='lean/scripts/make_lean4web_lite.py',
                  source_manifest_sha256=sha(LEAN/'evidence/source-manifest.json'),
                  baseline_sha256=sha(original), source_sha256=sha(output),
                  baseline_lines=len(original.read_text().splitlines()), lines=len(content.splitlines()),
                  baseline_bytes=original.stat().st_size, bytes=output.stat().st_size,
                  mathlib_modules_before=full_count, mathlib_modules_after=selected_count,
                  imports=imports, removed_declarations=len(removed),
                  removed=[dict(declaration=n, **{k:v for k,v in r.items() if k not in {'text','base'}})
                           for n,r in sorted(removed.items())],
                  removed_range_convention='zero-based start inclusive, end exclusive in pinned source',
                  sources=mapping, index_artifacts=artifacts,
                  scope='Conservative source/identifier pruning; no kernel dependency export succeeded. Full rc4 validation required.')
    write_json(WEB/'reduction.json', report)
    status_path = WEB/'lite-build-status.json'
    old = json.loads(status_path.read_text()) if status_path.exists() else {}
    if old.get('source_sha256') != report['source_sha256']:
        write_json(status_path, dict(status='not_checked', source_sha256=report['source_sha256'],
                                    requested_lean='leanprover/lean4:v4.35.0-rc4',
                                    scope='Generated reduced source; not a compiler result.'))
    print(json.dumps({k:v for k,v in report.items() if k not in {'removed','sources','imports','index_artifacts'}},indent=2))


if __name__ == '__main__':
    main()
