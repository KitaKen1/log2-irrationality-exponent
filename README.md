# The irrationality exponent of log 2

The natural logarithm of 2 has irrationality exponent 2:

```math
\mu(\log 2)=2.
```

This repository contains the complete split Lean proof and a statement in the style
of Formal Conjectures.

**Lean4Web edition:** [copy/paste single file](lean4web/LogTwoLean4WebPaste.lean),
94,873 lines; browser pass reported on **v4.35.0-rc4**.

## Formal Conjectures target

[FC-style statement draft](FClikelean/LogTwoIrrationalityExponent.lean) of
`μ(log 2) = 2`, using an independent definition of the irrationality exponent.

```lean
theorem LogTwo.irrationalityExponent_log_two :
    LogTwo.irrationalityExponent (Real.log 2) = answer(2)
```

## Files

| Directory | Lean version | Purpose |
|---|---|---|
| [lean/](lean/) | `v4.34.1` | Complete split proof: 88 project modules and 797 pinned supporting modules |
| [FClikelean/](FClikelean/) | FC-style draft; not FC-linted | Statement and one independent definition |
| [lean4web/](lean4web/) | `v4.35.0-rc4` | Copy/paste source and browser verification report |
| [PDF/](PDF/) | — | Mathematical proof notes |

The split entry point is [LogTwo.lean](lean/LogTwo.lean). The included
[OAI/](lean/OAI/) tree is exactly the imported closure from the pinned OpenAI
comparison source, with its recorded Lean-module compatibility patch. It includes
no nested Git repository and requires no separate OpenAI checkout.
[Third-party notices](THIRD_PARTY_NOTICES.txt) record provenance and modifications.

## Proof sketch

The [PDF proof notes](PDF/log2_proof_notes.pdf) describe the structure and steps
of the Lean proof in detail.

## Verification

```bash
cd lean
lake update
lake exe cache get
python3 scripts/build_audit.py
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

[Build results](lean/evidence/build-results.json) ·
[Build instructions](lean/README.md) · [Lean4Web](lean4web/README.md)

## Mathematical explanation (AI generated)

The following sketch follows the formal proof. The Lean statements and proofs,
rather than this sketch or the earlier PDF, determine the formal result.



Write $\lambda=\log 2$, where $\log$ is the natural logarithm. To establish that its irrationality exponent is $2$, it suffices to show that for every real $\nu>2$, there is an integer $Q\ge 2$ such that

$$
\left|\lambda-\frac{p}{q}\right|\ge q^{-\nu}
\qquad (p\in\mathbb Z,\ q\in\mathbb Z,\ q\ge Q).
$$

The threshold $Q$ may depend on $\nu$, and the fractions need not be reduced. Dirichlet's approximation theorem supplies the matching lower bound for the irrationality exponent.

### 1. Choose rational approximations and interpolation centers

Fix $\nu>2$ and suppose that arbitrarily large denominators $q$ admit approximations satisfying

$$
\left|\lambda-\frac{p}{q}\right|\le q^{-\nu}.
$$

Choose finitely many such approximations $r_i=p_i/q_i$, with the denominators growing successively fast enough that the weights $w_i=\lceil\log q_i\rceil$ satisfy the required separation conditions. Use the centers

$$
(Y,X_1,\ldots,X_m)=(2^j,jr_1,\ldots,jr_m),
\qquad 0\le j<K.
$$

The coordinates $Y=2^j$ are pairwise distinct.

### 2. Establish weighted interpolation

The geometric step gives surjectivity of the weighted jet evaluation map for sufficiently large admissible polynomial degrees. Its numerical condition is

$$
K\frac{w_0}{v_0}\theta^m<1,
\qquad 0<\theta<1,
\qquad v_i=\frac{w_i}{\theta}\quad(1\le i\le m),
$$

where $w_0$ is the degree weight of $Y$ and $v_0$ is the weight of the local parameter in the $Y$ direction.

The argument first derives a curve contact bound. If that bound failed, separated weights and local multiplicity estimates would force $Y$ to be constant on the curve. Such a curve can meet at most one interpolation center. Comparing the zero and pole degrees of a nonconstant coordinate then contradicts the excessive contact.

On a suitable blow-up, this curve bound yields ampleness of the interpolation line bundle. Serre vanishing and the high-degree description of sections on Proj then give the required jet surjectivity.

### 3. Obtain a nonzero rational determinant and an arithmetic lower bound

Replace the local logarithms by sufficiently long rational polynomial truncations. The weighted evaluation map is represented by a rational matrix, and surjectivity provides a nonzero square minor $\Delta_H$ using every row.

Clear denominators using the $q_i$ and least common multiples of the denominators in the truncated logarithms. The factors $2^{jh}$ are integers. The resulting determinant is a nonzero integer, so its absolute value is at least $1$. Keeping track of the row and column scaling factors gives an arithmetic lower bound for $|\Delta_H|$.

### 4. Bound the same determinant analytically

Use $e^{j\lambda}=2^j$ to rewrite the rows in terms of entire functions along

$$
(Y,X_1,\ldots,X_m)=(e^z,z,\ldots,z).
$$

The errors $r_i-\lambda$ supply small coefficients. In the Taylor expansion of the determinant, a term vanishes whenever two rows use the same transverse multi-index and Taylor degree. This cancellation forces decay in the surviving terms.

Separate the expansion into two cases: many rows have low transverse degree, giving strong decay from the Taylor-degree restriction; or many have high transverse degree, giving strong decay from the approximation errors. Both estimates apply to the same minor $\Delta_H$ chosen above.

### 5. Choose the parameters and reach a contradiction

Choose the scalar parameters first, then the dimension, then the approximations and their weights. One uses

$$
v_0=2K\theta^m w_0,
$$

so the interpolation ratio is exactly $1/2$. The dimension and weights are chosen so that the analytic and arithmetic error terms are small enough for the analytic upper bound to fall below the arithmetic lower bound. Only after fixing these data does the degree $H$ tend to infinity.

The incompatible bounds on the same nonzero determinant rule out arbitrarily large denominators with error at most $q^{-\nu}$. Since $\nu>2$ was arbitrary, this gives $\mu(\log 2)\le 2$. The classical lower bound from Dirichlet approximation gives the equality.

## Status boundary

The split proof has been checked locally on Lean v4.34.1.
A successful Lean4Web v4.35.0-rc4 run was [reported with a screenshot](lean4web/evidence/20261008T080310JST-browser-pass/report.json).

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation
were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using
GPT-6 Astra and GPT-6.1 sol.

## References

1. OpenAI. [*The irrationality exponent of pi is 2*][openai]. September 24, 2026. Fixed revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`; particularly the interpolation, determinant, and parameter-selection arguments.
2. Raffaele Marcovecchio. [*The Rhin–Viola method for log 2*][marcovecchio]. 2009.
3. Yann Bugeaud and Dong Han Kim. [*On the $b$-ary expansion of a real number whose irrationality exponent is close to 2*][bugeaud-kim]. arXiv:2510.02059v2, April 20, 2026.
4. The Stacks Project Authors. *The Stacks Project*: [Tag 0AG6][stacks-cohomology] and [Tag 0AG7][stacks-sections] on coherent sheaves and sections on Proj; [Tag 0B5U][stacks-serre] on ampleness and cohomology vanishing.

## Appendix: History

| Date | Development |
| :--- | :--- |
| 1987 | Rukhadze obtains $\mu(\log 2)\le 3.891\ldots$ (reported in [Marcovecchio][marcovecchio]). |
| 2009 | [Marcovecchio][marcovecchio] improves the upper bound to $\mu(\log 2)\le 3.574\ldots$. |
| 2026-04-20 | [Bugeaud–Kim, v2][bugeaud-kim] lists the exact value of $\mu(\log 2)$ as unknown. |
| 2026-09-24 | [OpenAI][openai] presents a proof of $\mu(\pi)=2$. |
| 2026-10-07 | The complete split Lean proof was checked locally on v4.34.1; the FC-style statement and v4.35.0-rc4 browser edition were prepared separately. |
| 2026-10-08 | The independent public definition and final target passed the local v4.34.1 audit; the browser's `quotientSection` error was fixed and its three-module rc4 check passed. |

[openai]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/main.tex
[marcovecchio]: https://ricerca.unich.it/handle/11564/648605
[bugeaud-kim]: https://arxiv.org/html/2510.02059v2
[stacks-cohomology]: https://stacks.math.columbia.edu/tag/0AG6
[stacks-sections]: https://stacks.math.columbia.edu/tag/0AG7
[stacks-serre]: https://stacks.math.columbia.edu/tag/0B5U
