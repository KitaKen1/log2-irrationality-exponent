"""Partition the reduced rc4 proof into reusable, separately compiled modules.

Each original source block is preserved byte for byte. Only new module headers
and scheduling options are added. Imports come from pinned source headers and
the cached identifier index, with the same implicit Complex instance supplement
as the reduced edition. Generation alone does not verify these import choices.
"""
from functools import lru_cache
from pathlib import Path
import argparse
import hashlib
import json

from build_audit import graph, sha, write_json
from make_lean4web_lite import header_imports

ROOT = Path(__file__).resolve().parents[2]
WEB = ROOT / 'lean4web'
DEST = WEB / 'checkpoints'
PREFIX = 'LogTwoCheckpoints'
TARGET = 'LogTwo.irrationalityExponent_log_two'
TOOLCHAIN = 'leanprover/lean4:v4.35.0-rc4'
MATHLIB = '1f414401f69059aa7eead47b53ee40bd38455eeb'


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


class ImportGraph:
    def __init__(self, root):
        self.root = root

    @lru_cache(maxsize=None)
    def imports(self, name, public_only):
        path = self.root / Path(*name.split('.')).with_suffix('.lean')
        if not path.exists():
            raise ValueError('Missing rc4 dependency: ' + name)
        return tuple(header_imports(path.read_text(), public_only=public_only))

    def closure(self, names, public_only=False):
        seen, todo = set(), list(names)
        while todo:
            name = todo.pop()
            if name in seen or not (name == 'Mathlib' or name.startswith('Mathlib.')):
                continue
            seen.add(name)
            todo.extend(self.imports(name, public_only))
        return seen

    def narrow(self, names):
        names = set(names)
        if 'Mathlib' in names:
            raise ValueError('Umbrella import is not allowed')
        roots = set(names)
        for name in names:
            if name.startswith('Mathlib.'):
                roots.difference_update(self.closure([name], True) - {name})
        assert self.closure(roots) == self.closure(names)
        return sorted(roots)


def generate(group_size=25):
    if group_size < 1:
        raise ValueError('Group size must be positive')
    _, sources, ordered, _ = graph()
    reduced = json.loads((WEB / 'reduction.json').read_text())
    source = WEB / 'LogTwoLean4WebLite.lean'
    if sha(source) != reduced['source_sha256']:
        raise ValueError('Reduced source differs from its manifest')
    if [r['module'] for r in reduced['sources']] != ordered:
        raise ValueError('Reduced source order differs from the pinned graph')
    rows = source.read_text().splitlines(keepends=True)
    blocks = {r['module']: ''.join(rows[r['first_line']-1:r['last_line']])
              for r in reduced['sources']}
    artifacts = {r['module']: r['ilean_sha256'] for r in reduced['index_artifacts']}
    groups = [ordered[i:i+group_size] for i in range(0,len(ordered),group_size)]
    owners = {name: f'{PREFIX}.Part{i:03d}' for i,g in enumerate(groups) for name in g}
    imports = ImportGraph(WEB / '.lake/packages/mathlib')
    records = []
    for i, group in enumerate(groups):
        module = f'{PREFIX}.Part{i:03d}'
        external = {'Mathlib.Analysis.Complex.Polynomial.Basic'}
        deps = set()
        for name in group:
            text = (ROOT / 'lean' / sources[name]['path']).read_text()
            index_path = ROOT / 'lean/.lake/build/lib/lean' / Path(sources[name]['path']).with_suffix('.ilean')
            if sha(index_path) != artifacts[name]:
                raise ValueError('Identifier index changed: ' + name)
            index = json.loads(index_path.read_text())
            if index['module'] != name:
                raise ValueError('Identifier index module mismatch: ' + name)
            referenced = {json.loads(key).get('c',{}).get('m','') for key in index['references']}
            for dep in set(header_imports(text)) | referenced:
                if dep in owners:
                    if owners[dep] != module:
                        deps.add(owners[dep])
                elif dep.startswith(('Mathlib.', 'Lean.', 'Batteries.', 'Aesop.', 'Qq.')):
                    external.add(dep)
                elif dep == 'Mathlib' or not dep or dep.startswith(('Init.', 'Lake.')):
                    continue
                else:
                    # Core references have no additional import requirement.
                    if dep in set(header_imports(text)):
                        raise ValueError('Unexpected header import: ' + dep)
        if any(d >= module for d in deps):
            raise ValueError('Checkpoint would have a forward dependency: ' + module)
        external = imports.narrow(external)
        header = ('/- Generated rc4 checkpoint for LogTwo.\n'
                  'Modified from the reduced edition: new imports, separate module compilation,\n'
                  'and synchronous elaboration. Original source blocks and notices are retained.\n'
                  'See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.\n-/\nmodule\n')
        header += ''.join(f'public import {n}\n' for n in sorted(deps) + external)
        header += '@[expose] public section\nset_option Elab.async false\n'
        body = ''.join(blocks[name] for name in group)
        content = header + body
        path = Path(*module.split('.')).with_suffix('.lean')
        output = DEST / path
        output.parent.mkdir(parents=True,exist_ok=True)
        output.write_text(content)
        records.append(dict(module=module, path=str(path), sha256=sha(output),
                            imports=sorted(deps), external_imports=external,
                            source_modules=group, lines=len(content.splitlines()),
                            body_sha256=digest(body), body_start_line=len(header.splitlines())+1,
                            mathlib_modules=len(imports.closure(external)),
                            source_blocks_preserved_exactly=True))
    # The final independent target is compiled and audited in a fresh process.
    target = (f'module\npublic import {owners["LogTwo"]}\n'
              '@[expose] public section\nset_option Elab.async false\n\n'
              'example : LogTwo.irrationalityExponent (Real.log 2) = 2 :=\n'
              f'  {TARGET}\n#print axioms {TARGET}\n')
    output = DEST / 'Target.lean'
    output.write_text(target)
    record = dict(generator='lean/scripts/make_lean4web_checkpoints.py',
                  lean=TOOLCHAIN, mathlib_commit=MATHLIB, group_size=group_size,
                  parent_source_sha256=sha(source), source_module_count=len(ordered),
                  module_count=len(records), modules=records,
                  target=dict(path='Target.lean', sha256=sha(output), imports=[owners['LogTwo']],
                              declaration=TARGET),
                  scope='Local resumable rc4 edition. Generation is not compilation. '
                        'The stock public Lean4Web server does not contain these local modules.')
    write_json(DEST / 'manifest.json',record)
    print(json.dumps({k:v for k,v in record.items() if k not in {'modules','target'}},indent=2))
    print(f'Largest checkpoint: {max(r["lines"] for r in records)} lines')
    return record


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--group-size',type=int,default=25)
    generate(parser.parse_args().group_size)
