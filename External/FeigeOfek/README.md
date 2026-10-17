# Feige and Ofek's bound on the spectral norm of `G(n, p)` (proved)

**Source.** U. Feige, E. Ofek, *Spectral techniques applied to sparse random graphs*, Random
Structures & Algorithms 27 (2005) 251–275, Section 2: for `pn ≥ c log n`, the second eigenvalue of
`G(n, p)` is `O(√(pn))` with high probability, by a bound on the bilinear form `xᵀ A y` over a net of
the unit ball for `x ⊥ 1` (as Hoffman, Kahle and Paquette recount it; Feige and Ofek's paper could not
be opened here, so the names below follow the content, not its numbering). The argument goes back to
Kahn and Szemerédi's bound for random regular graphs (Friedman, Kahn, Szemerédi, STOC 1989). Run on
the centred form `xᵀ (A − E A) y`, the same argument gives `‖A − E A‖ = O(√(pn))` with high
probability; the formalization follows that presentation, by P. Chin, A. Rao, V. Vu, *Stochastic block model and
community detection in sparse graphs: a spectral algorithm with optimal rate of recovery*, COLT
2015 (arXiv:1501.05021, Appendix A.1 and the appendix that proves their heavy-pair lemma); C.
Hoffman, M. Kahle, E. Paquette, *Spectral gaps of random graphs and applications*
(arXiv:1201.0425, the proof of their bound for the adjacency matrix) is a second write-up.

**Statement.** [`External.FeigeOfek.opNorm_adjMatrix_sub_le`](FeigeOfek.lean): for all `c, a > 0`
there is `C` such that, whenever `0 < p ≤ 1` and `pn ≥ c log n`, `‖A − E A‖ ≤ C √(pn)` with
probability at least `1 − n^(−a)`. It is stated with Mathlib's definitions only: `G(n, p)` is
`SimpleGraph.binomialRandom (Fin n)` (with `p` clamped into `[0, 1]`), `A` is `G.adjMatrix ℝ` (for
the classical decidability of adjacency), `E A` is the matrix with `p` off the diagonal and `0` on
it, and `‖·‖` is the operator norm on `ℓ²` (of `Matrix.toEuclideanCLM`). This is the sparse paper's
Lemma A.7. The papers' library proves Lemma A.7 from it (`PowerOfFew.Sparse.lemmaA_7`, in
`PowerOfFew/Sparse/MatrixNorm.lean`), where the paper's `gnpProb`, `adjMat`, `meanAdj` and
`specNorm` unfold to these terms, in place of the paper's derivation from two cited results
([`../BenaychGeorgesBordenaveKnowles/`](../BenaychGeorgesBordenaveKnowles/README.md) and
[`../BoucheronLugosiMassart/`](../BoucheronLugosiMassart/README.md)).

**Proof**, one file per step:

| Step | File | Result |
| --- | --- | --- |
| `G(n, p)` as independent Bernoulli edge indicators | [`Basic/Probability/Combinatorics/BinomialRandomGraph/EdgeVariables.lean`](../../Basic/Probability/Combinatorics/BinomialRandomGraph/EdgeVariables.lean) | `SimpleGraph.binomialRandom_eq_map_edgeLaw`, `SimpleGraph.isBernoulliFamily_edgeInd` |
| a net of the unit ball with at most `(33e)ⁿ` points; the operator norm is at most twice the largest value of the bilinear form on it | [`Basic/Analysis/GridNet.lean`](../../Basic/Analysis/GridNet.lean) | `card_gridNet_le`, `Matrix.norm_toEuclideanCLM_le_of_gridNet` |
| exponential moments of weighted Bernoulli sums (Bernstein type) | [`Basic/Probability/WeightedBernoulli.lean`](../../Basic/Probability/WeightedBernoulli.lean) | `IsBernoulliFamily.measureReal_le_sum_mul_le` |
| the binomial tail `P(Z ≥ k) ≤ (e p m / k)^k` | [`Basic/Probability/Chernoff.lean`](../../Basic/Probability/Chernoff.lean) | `IsBernoulliFamily.measureReal_sum_ge_le_exp_mul_log` |
| probabilities under `G(n, p)` and their rules; edge counts, bounded degrees, discrepancy, light and heavy parts | [`Defs.lean`](Defs.lean) | `prob`, `prob_eq`, `prob_exists_le`; definitions |
| the light pairs, for all points of the net at once | [`Light.lean`](Light.lean) | `lightSum_le` |
| bounded degrees and discrepancy of `G(n, p)` | [`Properties.lean`](Properties.lean) | `exists_degreeBound_discrepancy` |
| the six cases of the heavy pairs, on block data | [`SixCases.lean`](SixCases.lean) | `sum_blocks_le` |
| the heavy pairs | [`Heavy.lean`](Heavy.lean) | `heavySum_le` |
| the assembly | [`FeigeOfek.lean`](FeigeOfek.lean) | `opNorm_adjMatrix_sub_le` |

**One correction to the presentation followed.** Chin, Rao and Vu state the discrepancy alternative
`e(S, T) log(e(S, T)/μ(S, T)) ≤ c₃ |T| log(n/|T|)` for all sets `S, T`; the union bound that proves
it controls only `m = max(|S|, |T|)` in place of `|T|`, as Hoffman, Kahle and Paquette state it. The
formalization uses `m`, and treats the block pairs with `|S_i| ≤ |T_j|` and those with
`|T_j| ≤ |S_i|` separately, exchanging the roles of the two vectors (the pairs with `|S_i| = |T_j|`
are counted in both, which only enlarges the bound). Chin, Rao and Vu's constant
`max(16, 8c₁, 32c₂, 32c₃)` should be a sum; the formalization's is `2(24 + 8c₁ + 16c₂ + 64c₃)`.
