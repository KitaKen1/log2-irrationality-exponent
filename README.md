# The irrationality exponent of log 2

The conjecture on the irrationality exponent of $\log 2$ states the following.

| Conjecture |
| :--- |
| The natural logarithm of $2$ has irrationality exponent $2$: $\mu(\log 2)=2$. |

This repository presents a proof giving an affirmative answer to this conjecture: $\mu(\log 2)=2$.

Its purpose is to support adding this conjecture to Formal Conjectures and proposing its classification as `research solved`. It describes the solution and the main steps of the proof.

For more detailed proof notes, see the [PDF](PDF/log2_proof_notes.pdf).

## Proof sketch

Write $\lambda=\log 2$, where $\log$ is the natural logarithm. To establish that its irrationality exponent is $2$, it suffices to show that for every real $\nu>2$, there is an integer $Q\ge 2$ such that

$$
\left|\lambda-\frac{p}{q}\right|>q^{-\nu}
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

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra and GPT-6.1 sol

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
| 2026-10-07 | This repository presents a proof outline for $\mu(\log 2)=2$, intended for a proposal to Formal Conjectures. |

[openai]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/main.tex
[marcovecchio]: https://ricerca.unich.it/handle/11564/648605
[bugeaud-kim]: https://arxiv.org/html/2510.02059v2
[stacks-cohomology]: https://stacks.math.columbia.edu/tag/0AG6
[stacks-sections]: https://stacks.math.columbia.edu/tag/0AG7
[stacks-serre]: https://stacks.math.columbia.edu/tag/0B5U
