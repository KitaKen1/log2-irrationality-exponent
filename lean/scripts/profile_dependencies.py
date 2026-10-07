"""Measure pinned source import closures without starting Lean.

These counts describe packaged source volume, not CPU time or the minimal
declaration dependencies of a proof. Mathlib and Lean sources are excluded.
Closures overlap and must not be added together.
"""
from pathlib import Path
import argparse
import json

from build_audit import ROOT, graph, sha, write_json
from module_headers import imports


ENTRIES = (
    'LogTwo',
    'LogTwo.Target',
    'LogTwo.Main',
    'LogTwo.Geometry.MatrixInterpolation',
    'LogTwo.Geometry.IntrinsicContactBound',
    'LogTwo.Analysis.AnalyticUpper',
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        help='Optionally save the source-volume report as JSON')
    args = parser.parse_args()
    _, sources, _, _ = graph()  # Verify source inventory and every pinned hash.
    bodies = {name: (ROOT / row['path']).read_text()
              for name, row in sources.items()}
    deps = {name: {d for d in imports(body) if d in sources}
            for name, body in bodies.items()}
    lines = {name: len(body.splitlines()) for name, body in bodies.items()}

    def closure(entry):
        seen, pending = set(), [entry]
        while pending:
            name = pending.pop()
            if name not in seen:
                seen.add(name)
                pending.extend(deps[name] - seen)
        return seen

    baseline = closure('LogTwo')
    rows = []
    for entry in ENTRIES:
        names = closure(entry)
        rows.append({
            'entry': entry,
            'modules': len(names),
            'raw_source_lines': sum(lines[n] for n in names),
            'omitted_module_count_vs_LogTwo': len(baseline - names),
            'omitted_raw_source_lines_vs_LogTwo':
                sum(lines[n] for n in baseline - names),
        })
    flattened = ROOT.parent / 'lean4web/LogTwoLean4Web.lean'
    report = {
        'scope': __doc__.strip(),
        'source_manifest_sha256': sha(ROOT / 'evidence/source-manifest.json'),
        'flattened_source_sha256': sha(flattened),
        'flattened_source_lines': len(flattened.read_text().splitlines()),
        'entries': rows,
        'lean_compiler_started': False,
    }
    if args.output:
        write_json(args.output, report)
    print(json.dumps({k: v for k, v in report.items() if k != 'entries'}, indent=2))
    for row in rows:
        print(f"{row['entry']}: {row['modules']} modules, "
              f"{row['raw_source_lines']:,} raw source lines")


if __name__ == '__main__':
    main()
