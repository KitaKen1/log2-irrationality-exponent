# Statement in the format of Formal Conjectures

[LogTwoIrrationalityExponent.lean](LogTwoIrrationalityExponent.lean) is a local
draft for the affirmative answer `answer(2)` to the irrationality-exponent
question for the natural logarithm of 2. The proposed category is
`research solved`, AMS 11. This is not a claim of FC acceptance.

The single independent definition is shared verbatim with
[the project definition file](../lean/LogTwo/IrrationalityExponent.lean).
This file imports only Mathlib and uses no comparison-library definition or alias.
The proof-side bridge establishes equivalence with the comparison definition.
The target after elaborating `answer(2)` is checked against
[the complete proof](../lean/LogTwo/Target.lean) by
[FCType.lean](../lean/audit/FCType.lean).
The real supremum is accompanied by checked boundedness and membership of 2
in the full proof audit.

The draft uses `by sorry` as an externally linked statement. The split proof
contains no holes. Actual FC utility/metadata linting has not been run; this file
must be integrated into a version-compatible Formal Conjectures checkout before
submission. No local fake implementation of FC attributes is supplied.

After publishing a proof commit,
`python3 ../lean/scripts/fill_links.py FULL_COMMIT_SHA` can prepare fixed proof
and browser links; it does not publish anything. Until then, the draft intentionally
omits a `formal_proof` URL instead of citing a commit without the Lean files.
