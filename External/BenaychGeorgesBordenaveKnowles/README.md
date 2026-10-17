# The spectral norm of `A − E A`: the paper's cited results

The sparse paper's Lemma A.7 bounds `‖A − E A‖_op` for the adjacency matrix `A` of `G(n, p)` with
`pn ≥ c log n`. Its proof combines two cited results. Both are stated in
[`RandomMatrix.lean`](RandomMatrix.lean), and the paper's derivation of Lemma A.7 from them is
formalized as `PowerOfFew.Sparse.lemmaA_7_of_bbk_blm`, with the two results as hypotheses.

The library proves Lemma A.7 itself (`PowerOfFew.Sparse.lemmaA_7`) by Feige and Ofek's argument
instead ([`../FeigeOfek/`](../FeigeOfek/README.md)), at the author's request: no result of the
library, and no statement of the Challenge, assumes the two results below.

## Benaych-Georges, Bordenave, Knowles, Theorem 3.2

**Source.** F. Benaych-Georges, C. Bordenave, A. Knowles, *Spectral radii of sparse random
matrices*, Ann. Inst. H. Poincaré Probab. Statist. 56 (2020), arXiv:1704.02945, Theorem 3.2 (the
inhomogeneous Erdős–Rényi graph): with `d = maxᵢ ∑ⱼ pᵢⱼ`, `κ = maxᵢⱼ pᵢⱼ / (d/n)`,
`q = √d ∧ n^(1/10) κ^(−1/9)` and `η = √(log n)/q`, if `q ≥ 1` then
`E‖A − E A‖ / √d ≤ 2 + C η / √(1 ∨ log η)` for a universal constant `C`.

**In the formalization.** `PowerOfFew.BBKTheorem3_2` states the homogeneous case `pᵢⱼ = p`
(`i ≠ j`): `d = p(n − 1)`, `κ = n/(n − 1)`. The sparse paper quotes it with `d = p(1 − p)(n − 1)` and
`η = √(log n)/min{√d, n^0.1}`; the difference only changes constants.

## Boucheron, Lugosi, Massart, Theorem 6.10

**Source.** S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities: A Nonasymptotic
Theory of Independence*, Oxford University Press (2013), Theorem 6.10 (first proved by Talagrand):
for independent `X₁, …, X_N` with values in `[0, 1]` and `f : [0, 1]^N → ℝ` separately convex with
`|f(x) − f(y)| ≤ ‖x − y‖`, `Z = f(X)` satisfies `P{Z > E Z + t} ≤ e^(−t²/2)` for `t > 0`.

**In the formalization.** `PowerOfFew.BLMTheorem6_10`, stated for real random variables on a
probability space in `Type`. The sparse paper applies it to `2^(−1/2) ‖Z − E A‖_op` as a function
of the upper-triangular entries, which gives `e^(−t²/4)` for `‖A − E A‖_op`.

## What Lean lacks

Mathlib has the operator norm of matrices but no moment method for random matrices (BBK's proof
estimates `E tr Bˡ B*ˡ` for the non-backtracking matrix `B` and uses an Ihara–Bass type formula)
and no Talagrand-type concentration inequality (BLM's proof uses the entropy method and
logarithmic Sobolev inequalities). Feige and Ofek's argument needs neither: only Chernoff bounds,
union bounds and a net of the unit ball.
