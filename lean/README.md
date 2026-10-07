# Complete split Lean proof

Entry point: [LogTwo.lean](LogTwo.lean). Final theorem:
[LogTwo/Target.lean](LogTwo/Target.lean), `LogTwo.irrationalityExponent_log_two`.

This project is pinned to Lean v4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
It contains 88 LogTwo modules and the 797 imported supporting modules from
OpenAI's `openai/math`, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Every source is listed in [source-manifest.json](evidence/source-manifest.json).

```bash
lake update
lake exe cache get
python3 scripts/build_audit.py
```

The script compiles sequentially at 4096 MiB and one worker thread, preserves
successful cache entries, audits 401 declarations, and checks exact final types.
`--rebuild-own` forces all project modules; failed forced modules remain pending.
`--check-sources-only` checks all 885 source hashes without running Lean.
`--reuse-verified PATH` optionally copies matching artifacts from the original
workspace after checking its recorded source and olean hashes; this is explicitly
reported as artifact reuse and is not a fresh rebuild.

[build-results.json](evidence/build-results.json) points to the latest successful
package audit. Every attempt has its own directory under `evidence/runs/`.
[historical-verification.json](evidence/historical-verification.json) records the
pre-packaging proof audit. Do not conflate the two scopes.

Modification notices were subsequently prepended to 838 files. The
[notice-update record](evidence/notice-update.json) preserves before/after hashes
and [the prior source manifest](evidence/source-manifest-before-notices.json).
`python3 scripts/check_package.py` verifies that removing only the new comment
prefixes restores every affected file byte for byte to the audited version.
This preserves the proof code while distinguishing the new source hashes from
the earlier compilation. No complete rebuild was run solely for these comments.

The OAI tree is already included with its full compatibility patch and license
notice. No nested repository, local absolute path, or development cache is needed
in a published checkout. Standard `lake build` is also available, but the audit
script provides the explicit sequential resource policy.

The v4.35.0-rc4 single-file edition is in [../lean4web/](../lean4web/); its success
or failure does not replace verification of this pinned split proof.
