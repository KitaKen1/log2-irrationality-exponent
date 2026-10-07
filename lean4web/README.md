# Complete single-file edition for Lean4Web

**Copy/paste edition:** [LogTwoLean4WebPaste.lean](LogTwoLean4WebPaste.lean).
Copy the entire file into Lean4Web with **Lean v4.35.0-rc4**. It has no local
project imports and needs no checkpoint cache or additional files.

**Browser result — 2026-10-08:** the user reports that the full run passed on
Lean v4.35.0-rc4. The [saved screenshot](evidence/20261008T080310JST-browser-pass/screenshot.png)
shows **885/885** and the final axiom output for
`LogTwo.irrationalityExponent_log_two`. See the
[browser report](evidence/20261008T080310JST-browser-pass/report.json).
Browser source bytes, the raw log, runtime, and peak memory were not captured;
the local CLI evidence below remains a separate partial check.

This edition wraps **7,784 `by` proofs** with a tactic that runs the original
steps while omitting their internal editor information. It preserves outer
command information required by rc4, and uses normal editor information for the
independent definition and final target. Style linters and asynchronous
elaboration are disabled. Kernel checking, compiler errors and the final axiom
print remain enabled. Inner term hovers and intermediate tactic goals are omitted;
static tactic help and outer information may remain. Progress is reported every
25 modules. Removing the wrappers and added commands restores the original
reduced source exactly. This targets retained editor metadata, not source length.

The [rc4 language-server probe](evidence/20261007T220327Z-paste-editor/result.json)
confirms that inner term hover is omitted, final hover remains, and a deliberately
invalid proof is still rejected, with no internal server errors. Both valid
probe theorems are axiom-free.
That small protocol test is not a full log-two proof or public-browser run.
See [paste-build-status.json](paste-build-status.json) for the exact check scope;
the successful browser report above is separate from these local checks.

The 07:16/07:18 browser errors came from implicit instance imports omitted by
the reduction. The paste edition now explicitly imports the providers for
functor-category exact colimits, Grothendieck-category and module-category
injectives, and monoidal presheaf pushforward. Their transitive Mathlib source
closure is **4,330 modules**, up from 4,288; the umbrella import is still absent.

Both affected source modules, `FiniteCoverCohomology` and `LineBundleTensor`,
[pass together](evidence/20261007T222044Z-paste-instances/result.json) with the
current paste header on rc4 in **53.7 seconds**, one worker and 4096 MiB.
The four audited declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. The preceding [unfixed check](evidence/20261007T221759Z-paste-grothendieck/result.json)
reproduced the missing-instance errors. This is a focused check of complete
source modules, not the entire single file or its final theorem.

The regenerated file also [passes its first 325 modules](evidence/20261007T222145Z-paste-prefix/result.json)
(**36,292 source lines**) in **238.8 seconds**, under the same rc4/one-worker/4096 MiB
limits. This uses the actual preceding source order and goes beyond the reported
error locations. All seven audited declarations use only the standard three axioms;
no compiler errors or internal panics were reported. The remaining 560 modules
and final target have not been independently checked by a full local rc4 CLI run.

The previous hash's [first 100 modules](evidence/20261007T220350Z-paste-prefix/result.json)
passed in **58.4 seconds**. That result does not certify the regenerated file;
it is retained as historical evidence, not a controlled speed comparison.

An earlier experiment disabled info trees globally and triggered rc4 internal
panics despite normal process/protocol completion; it was rejected. The current
file keeps outer info trees. Checkers now reject internal `PANIC` messages too.

```bash
python3 lean/scripts/make_lean4web_paste.py
python3 lean/scripts/check_paste_editor.py
python3 lean/scripts/check_paste_module.py
python3 lean/scripts/check_lite_prefix.py --edition paste --module-count 325 --timeout-seconds 360
```

The new [local checkpoint build](checkpoints/README.md) divides the reduced
proof into **36 separately compiled modules**, at most **5,995 source lines**
per checkpoint, and reuses hash-checked artifacts after a stop. The first 50
original modules compiled successfully on rc4 in a
[249.1-second run](evidence/checkpoints-20261007T175635Z-e827ccf2/result.json).
A [repeat check](evidence/checkpoints-20261007T180132Z-bb01932a/result.json)
reused both checkpoints in **11.9 seconds**, with no proof recompilation.
This measures reuse of a completed prefix, not a full-proof speedup. The remaining
835 original modules and final target have not been checked by this route.
It is local only; the stock public Lean4Web server cannot import the local cache.

The reduced file lost its Lean connection after about **15 minutes** in the
[user's browser report](evidence/20261008T022952JST-browser-report/report.json).
The screenshot does not identify the cause or the last completed declaration.
The browser source hash was not recovered; its line count and final target
match the reduced edition.

[LogTwoLean4WebSequential.lean](LogTwoLean4WebSequential.lean) is a diagnostic
variant: `set_option Elab.async false` disables asynchronous elaboration, and
messages every 25 modules show which location was reached. All proof text and
the final independent target are unchanged. This may reduce concurrent work;
it does not cap every server thread or discard editor history, and **is not a
demonstrated speedup or crash fix**. A progress message is not proof that earlier
commands were error-free.

Its [100-module local check](evidence/20261007T173614Z-sequential-prefix/result.json)
stopped at the **240-second cap**, with no diagnostics or axiom output recorded.
The complete sequential edition remains unverified; see
[sequential-build-status.json](sequential-build-status.json).

```bash
python3 lean/scripts/make_lean4web_sequential.py
# Bounded local check of the diagnostic edition:
python3 lean/scripts/check_lean4web.py --edition sequential --timeout-seconds 300
```

The reduced edition is [LogTwoLean4WebLite.lean](LogTwoLean4WebLite.lean):
**94,778 lines**, with 641 unused plain lemmas removed. Narrower imports reduce
the transitive Mathlib source-module count from **8,600 to 4,288**. These are
source/dependency counts, not a measured speedup. See [reduction.json](reduction.json)
for exact removals and hashes, and [lite-build-status.json](lite-build-status.json)
for the separate rc4 check. The independent public definition and final target
are unchanged; all instances, attributed declarations and source notices remain.
The original edition below is retained for comparison.

The [first 100 reduced modules](evidence/20261007T171752Z-lite-prefix/result.json)
(11,436 source lines) pass on rc4 in **211.7 seconds**, with one worker and a
4096 MiB limit. All three audited declarations use only the standard axioms.
This covers the import-visibility and source-pruning fixes; **the entire reduced
file and its final log-two theorem have not yet passed**. The earlier full
attempts apply to previous hashes. No end-to-end speedup is claimed.

```bash
python3 lean/scripts/make_lean4web_lite.py
python3 lean/scripts/check_lean4web.py --edition lite --timeout-seconds 300
# Recheck the tested prefix only:
python3 lean/scripts/check_lite_prefix.py
```

[LogTwoLean4Web.lean](LogTwoLean4Web.lean) contains the entire imported proof
closure in one file: **885 source modules, 104,875 lines**, importing only Mathlib.
It targets **Lean v4.35.0-rc4**, with Mathlib pinned to
`1f414401f69059aa7eead47b53ee40bd38455eeb`.

**Verification status:** consult [build-status.json](build-status.json).
The current 104,875-line file has **not passed** the complete rc4 check. It was
regenerated after adding distribution notices and further compatibility fixes.
The [last full-attempt log](evidence/20261007T150219Z-d3fe54ac/build.log), for the
earlier 95,661-line source, reports
`lean::memory_exception: excessive memory consumption detected at 'interpreter'`.
The process exited with signal 6 after about 42 seconds under the 4096 MiB Lean
allocator limit. This is not a report of exhausted system RAM or a mathematical
counterexample. No memory limit was increased.
The split proof is separately verified on v4.34.1 in [../lean/](../lean/).

The [earlier attempt](evidence/20261007T144641Z-f2e81a2c/result.json), before the
independent final target and the explicit torsion-free instance were added,
stopped at the 600-second time limit. Its empty diagnostic log did not certify
success. Each result records the exact source hash it checked.

```bash
# Run from the repository root:
python3 lean/scripts/make_lean4web.py
cd lean4web
lake update
lake exe cache get
python3 ../lean/scripts/check_lean4web.py --timeout-seconds 600
```

The checker uses a single Lean process, one worker thread, a 4096 MiB Lean
allocator limit, and a 600-second bound in the command above. It retains logs
under `evidence/`, stops on a compiler error or time limit, and does not raise
resource limits automatically. It checks the local CLI source; no successful
browser/server execution is inferred from that result.

The [source map](source-map.json) records the original paths, hashes and generated
line ranges. Generation removes module/import headers, wraps each original body
in a named section, and closes sections that originally ended at EOF. The
mathematical statements are preserved. Twenty-three source modules receive explicit
compatibility edits: qualify the HasAntidiagonal membership lemma, and bundle
the monotonicity witnesses in two AddValuation.map calls; explicitly supply the
field torsion-free instance for `quotientSection` in `PrimeHilbertDegree`;
remove one redundant `rfl` in `FiniteFreeResolutionExt`; replace two deprecated
`SetLike` order-lemma names with `IsConcreteLE` names; parenthesize multiline
singleton elements in twelve modules; qualify `restrictScalar` in `TwistSectionClearing`
and `tensorFrame` in `CartierMixedEuler`; rename
three private helpers that collide when separate modules share one file.
No heartbeat limit is raised.
Modification notices are retained for each source, and the generated file's
header also identifies the flattening and rc4 edits.

The [three-module compatibility check](evidence/20261007T150117Z-hilbert/result.json)
for `PrimeHilbertDegree` passes on v4.35.0-rc4, including the reported theorem and
its axiom print. It can be rerun with
`python3 lean/scripts/check_rc4_hilbert.py` from the repository root.
This limited check does not verify the complete single file or its final target.

The latest [seven-module compatibility check](evidence/20261007T151450Z-browser/result.json)
also passes the reported `projectiveResolutionOfExact` error and the displayed
style/deprecation fixes. Its [raw log](evidence/20261007T151450Z-browser/build.log)
contains the standard-three axiom prints and no errors or warnings.
Rerun it with `python3 lean/scripts/check_rc4_compat.py --case browser`.

The [37-module geometry check](evidence/20261007T153549Z-geometry/result.json)
passes the singleton parser and `restrictScalar` fixes with their dependencies
on v4.35.0-rc4 (168.5 seconds, 4096 MiB limit, one worker thread).
Its [raw log](evidence/20261007T153549Z-geometry/build.log) reports only
`propext`, `Classical.choice`, and `Quot.sound` for the three checked theorems,
with no errors or warnings. Rerun it with
`python3 lean/scripts/check_rc4_compat.py --case geometry`.

The [100-module curves run](evidence/20261007T161004Z-curves/result.json) recorded
only the standard three axioms for all eleven audited theorems, including the
reported curve-degree and zero-stalk results. It exited with one `tensorFrame`
name-ambiguity error in a later simplification; it is **not** a successful
100-module build. The current generated file qualifies that name.
Rerun the complete group with
`python3 lean/scripts/check_rc4_compat.py --case curves --timeout-seconds 600`.
The [focused tensor-frame check](evidence/20261007T161918Z-tensor-frame/result.json)
then passed the fix on rc4: 26 complete dependency modules and the complete
`framed_map` and `tensorMap_framed` lemmas (174.8 seconds, 4096 MiB limit).
The [raw log](evidence/20261007T161918Z-tensor-frame/build.log) reports only the
standard three axioms, with no errors or warnings. Rerun this scope with
`python3 lean/scripts/check_rc4_compat.py --case tensor-frame`.
The matching singleton syntax in `AmpleCurveDegreePositive` and
`LogTwo.Geometry.SectionIdealBridge` is also parenthesized; those two modules
are outside this focused group.

The remaining work is to reduce the retained declaration closure and Mathlib
imports, use bounded groups of modules to locate further rc4 compatibility
issues, and rerun the generated full source. Success of a smaller prefix does
not certify the final theorem. Future optimization must retain the same
independent definition, argument-free target and standard-three axiom closure.

The file can be opened at https://live.lean-lang.org/ after selecting v4.35.0-rc4
and pasting/uploading the source. Its size may make browser loading impractical.
After the source has a public commit, the repository's `fill_links.py` can prepare
a fixed-commit `#url=` link. No link to an unpublished proof is presented as live.
