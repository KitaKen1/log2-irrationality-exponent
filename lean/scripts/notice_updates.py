"""Verify that distribution notices only prepend closed non-doc comments.

Preserve the old kernel-audit record: this is byte comparison, not compilation.
"""
import hashlib
import json
from pathlib import Path


def sha(data):
    return hashlib.sha256(data).hexdigest()


def verify_notice_update(lean: Path, audited_manifest_sha256: str):
    evidence = lean/'evidence'
    update = json.loads((evidence/'notice-update.json').read_text())
    assert update['kind'] == 'prepended_comment_only'
    before_data = (evidence/'source-manifest-before-notices.json').read_bytes()
    after_data = (evidence/'source-manifest.json').read_bytes()
    assert sha(before_data) == update['before_manifest_sha256'] == audited_manifest_sha256
    assert sha(after_data) == update['after_manifest_sha256']
    before, after = json.loads(before_data), json.loads(after_data)
    assert {k:v for k,v in before.items() if k!='sources'} == {k:v for k,v in after.items() if k!='sources'}
    old = {r['module']:r for r in before['sources']}
    new = {r['module']:r for r in after['sources']}
    entries = {r['module']:r for r in update['entries']}
    assert old.keys() == new.keys()
    changed = {n for n in old if old[n]['sha256'] != new[n]['sha256']}
    assert changed == entries.keys()
    assert len(entries) == len(update['entries']) == update['changed_files']
    for name, record in new.items():
        assert {k:v for k,v in record.items() if k!='sha256'} == {k:v for k,v in old[name].items() if k!='sha256'}
        data = (lean/record['path']).read_bytes()
        assert sha(data) == record['sha256']
        if name not in entries:
            assert sha(data) == old[name]['sha256']
            continue
        entry = entries[name]
        assert entry['path'] == record['path']
        assert data.startswith(b'/-\nModification notice for the LogTwo project.\n')
        split = data.index(b'-/\n\n') + len(b'-/\n\n')
        prefix, original = data[:split], data[split:]
        assert prefix.count(b'/-') == 1 and prefix.count(b'-/') == 1
        assert sha(prefix) == entry['notice_sha256']
        assert sha(original) == entry['before_sha256'] == old[name]['sha256']
        assert sha(data) == entry['after_sha256']
    return len(entries)
