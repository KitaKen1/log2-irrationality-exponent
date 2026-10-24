# Exact Formal Conjectures PR 6923 verification

This directory compares the original pinned proof with the exact statement in [Formal Conjectures PR #6923](https://github.com/google-deepmind/formal-conjectures/pull/6923). The proof sources are unchanged.

- Proof: `KitaKen1/log2-irrationality-exponent@93a66a6c6b69e5e2f7775d791fd4943f4b1cf671`.
- FC statement: `KitaKen1/formal-conjectures@78d227fba77b02455c326e4e4d93d9881b3db025`, `FormalConjectures/Arxiv/2510.02059/LogTwo.lean`.
- Lean: `leanprover/lean4:v4.34.1`, matching the original split proof.
- The mathematical namespace body is preserved byte for byte. Only the module wrapper/imports are adapted from FC's Lean 4.33.1. `answer(2)` is unchanged. `ModelAuditFC` also checks the compiled definition and target against the raw PR variant.
- SHA256 locks cover every pinned proof source and its dependency manifests; the pinned FC utilities are checked against their upstream Git blob hashes.

The first run builds the proof from source on a new Linux runner, using the fixed Mathlib revision's cache. Later runs may restore proof build products under an exact key for the original proof-source lock, dependency manifest and Lean version; the receipt records whether this happened. The Challenge is freshly exported before the solution build, and comparison and nanoda replay always run again. It builds pinned Comparator core, lean4export and nanoda sources, compares the theorem and its reachable definitions, checks the allowed axioms, and independently replays the solution with nanoda. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted; there are no definition holes.

Seven controls exercise valid proofs and rejection of `sorryAx`, an extra axiom, a changed definition, a changed target, a missing target, and a malformed exported proof. Evidence is uploaded even if a stage fails.

Scope: this uses the same Comparator-core driver and independent nanoda approach as the Funk verification. It does not run Comparator's separate landrun CLI pipeline, perform an adversarial build sandbox test, rebuild all Mathlib dependencies from scratch, or constitute human mathematical review. The workflow requires the public `KitaKen1/log2-irrationality-exponent` repository. It runs on pushes to `fc-6923-public-verification-20261024`.


## Existing source warnings

Preliminary CI identified eight existing source style/deprecation warnings in the unchanged pinned proof. `reference/accepted-build-warnings.json` records their exact locations and messages. The revised proof build permits only these eight known warnings and fails on any other warning. The immutable proof is unchanged; axiom restrictions, definition comparison, independent replay and negative controls remain required. Challenge compilation and direct audit elaboration still reject warnings.

The three visible CI steps now separately freeze the Challenge, build/audit the proof, and run comparison/replay/controls. Phase receipts must belong to the same CI SHA, run and attempt, with identical source and tool locks.

## Reproduce

On Linux x86_64 with the pinned Lean and Rust toolchains, follow [the workflow](../.github/workflows/fc-log2-verification.yml) to install dependencies and tools. The verification commands are:

```bash
python3 leanWithComparator/scripts/make_challenge.py --check
(cd leanWithComparator && lake exe cache get)
python3 leanWithComparator/scripts/setup_tools.py
python3 leanWithComparator/scripts/verify.py
```

Use a clean checkout with no `leanWithComparator/evidence/` directory. A successful run writes `evidence/result.json`; the workflow publishes logs and receipts as an Actions artifact. The receipt records the CI source commit, original proof and FC statement commits, export hashes, tool revisions, definition agreement, axiom report and all seven controls.

## Public verification result

[Run 40066294960](https://github.com/KitaKen1/log2-irrationality-exponent/actions/runs/40066294960) passed on 2026-10-24 at verification commit `2303de25fb0d06866563ee62d2f8759dd7333b62`. The original pinned proof was built from source using the fixed Mathlib cache, without restoring a proof build cache. Comparator core matched the exact target and its reachable definitions, nanoda checked 117,647 declarations, and all seven controls passed. The reported axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.

[Permanent receipt and logs](receipts/public-run-40066294960/README.txt) include the unchanged CI result JSON and a file-hash manifest. The receipt commit adds evidence and documentation to the tested source commit; it is not a separate verification run.
