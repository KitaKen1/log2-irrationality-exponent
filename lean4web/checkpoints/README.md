# Resumable local rc4 proof

The reduced proof is divided into **36 checkpoints** of at most 25 original
modules each. The largest is **5,995 source lines**, versus 94,778 lines in the
single file. Every original proof block is preserved exactly, including its
notices, independent definition and final theorem. Narrow imports are selected
per checkpoint; the entire Mathlib umbrella is not imported.

Each checkpoint runs in a fresh Lean process with one worker and a **4096 MiB**
limit. Completed artifacts are cached. Repeating the command reuses matching
results and continues at the first unfinished or invalid checkpoint. Source,
compiler, package-manifest, dependency or artifact changes invalidate the cache.
Failed and interrupted output is quarantined and never marked as verified.

From the repository root, using the existing rc4 Mathlib cache:

```bash
# Generate after changing the reduced source or its manifest:
python3 lean/scripts/make_lean4web_checkpoints.py
# Each invocation compiles at most two new checkpoints, for at most five minutes:
python3 lean/scripts/check_lean4web_checkpoints.py
# Inspect source parity without starting Lean:
python3 lean/scripts/check_lean4web_checkpoints.py --check-sources-only
```

The default per-checkpoint limit is 180 seconds. A limit hit is recorded and
retains all earlier completed checkpoints. Every invocation uses the shared
proof-checker lock, so another checker cannot start a second compiler.

When all 36 checkpoints have been checked, [Target.lean](Target.lean) verifies
the independent final type and prints its axioms in a fresh process. Only an
error-free final audit using at most `propext`, `Classical.choice`, and
`Quot.sound` can mark the whole proof as passed. A completed prefix is recorded
as `partial`, not a full proof pass. See the current
[status](../checkpoint-build-status.json) and [manifest](manifest.json).

The [first build](../evidence/checkpoints-20261007T175635Z-e827ccf2/result.json)
successfully compiled checkpoints 0 and 1 (50 original modules): 88.8 and
141.9 seconds, respectively; 249.1 seconds including setup and bookkeeping.
The [repeat run](../evidence/checkpoints-20261007T180132Z-bb01932a/result.json)
reused both in 11.9 seconds with zero proof compilations. This verifies cache
reuse for that prefix, not the remaining 835 modules or final log-two theorem.
The compiler emitted only a deprecated-import warning in each checkpoint.

This is a **local** build route on Lean v4.35.0-rc4. The stock public Lean4Web
server does not have these local modules or cached artifacts: pasting
`Target.lean` there is insufficient. The single-file editions remain available.
Checkpointing reduces repeated elaboration and resets per-process working state;
it does not establish a measured peak-memory reduction or first-build speedup.

Generated files retain the original source blocks verbatim. Relative provenance
links inside those blocks refer to their original single-file context; the new
header in each checkpoint links to the package's notices from its new location.
No files have been uploaded or registered with a remote server.
