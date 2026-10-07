"""Create a synchronous diagnostic edition without changing any proof text.

Elab.async false disables asynchronous elaboration. It is not a memory cap,
does not discard the language server's history, and cannot guarantee completion.
Progress messages indicate that a location was reached, not that prior commands
were error-free. The final independent target and axiom audit remain in place.
"""
import json
from pathlib import Path

from build_audit import sha, write_json

WEB = Path(__file__).resolve().parents[2] / 'lean4web'
INTRO = '''-- Sequential diagnostic edition: proof text is unchanged from the reduced edition.
-- Disable asynchronous elaboration; this does not bypass kernel checking.
set_option Elab.async false

'''


def generate():
    base = WEB / 'LogTwoLean4WebLite.lean'
    report = json.loads((WEB / 'reduction.json').read_text())
    assert sha(base) == report['source_sha256']
    original = base.read_text()
    lines = original.splitlines(keepends=True)
    first = report['sources'][0]['first_line'] - 1
    chunks = [''.join(lines[:first]), INTRO]
    added = [INTRO]
    mapping, markers = [], []
    line = sum(len(c.splitlines()) for c in chunks) + 1
    for i, source in enumerate(report['sources']):
        fragment = ''.join(lines[source['first_line']-1:source['last_line']])
        mapping.append({**source, 'first_line':line,
                        'last_line':line+len(fragment.splitlines())-1})
        chunks.append(fragment)
        line += len(fragment.splitlines())
        if (i+1) % 25 == 0 or i+1 == len(report['sources']):
            message = f'LogTwo progress: reached module {i+1}/{len(report["sources"])}'
            marker = f'\n#eval IO.println "{message}"\n'
            markers.append(dict(after_module=i+1, module=source['module'], line=line+1))
            chunks.append(marker); added.append(marker)
            line += len(marker.splitlines())
    chunks.append(''.join(lines[report['sources'][-1]['last_line']:]))
    content = ''.join(chunks)
    # Byte-for-byte round trip: no original code, options or notices are changed.
    restored = content
    for insertion in added:
        assert restored.count(insertion) == 1
        restored = restored.replace(insertion, '', 1)
    assert restored == original
    output = WEB / 'LogTwoLean4WebSequential.lean'
    output.write_text(content)
    record = dict(generator='lean/scripts/make_lean4web_sequential.py',
                  parent_source_sha256=sha(base), source_sha256=sha(output),
                  lines=len(content.splitlines()), bytes=len(content.encode()),
                  elaboration_async=False, sources=mapping, progress_markers=markers,
                  base_source_restored_exactly=True,
                  scope=__doc__.strip())
    write_json(WEB / 'sequential-source-map.json',record)
    status_path = WEB / 'sequential-build-status.json'
    old = json.loads(status_path.read_text()) if status_path.exists() else {}
    if old.get('source_sha256') != record['source_sha256']:
        write_json(status_path, dict(status='not_checked',source_sha256=record['source_sha256'],
                                    requested_lean='leanprover/lean4:v4.35.0-rc4',
                                    scope='Generated synchronous diagnostic edition; not a compiler result.'))
    print(json.dumps({k:v for k,v in record.items() if k not in {'sources','progress_markers'}},indent=2))


if __name__ == '__main__':
    generate()
