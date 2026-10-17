# Feige and Ofek's bound on the spectral norm of `G(n, p)` (proved)

**Source.** U. Feige, E. Ofek, *Spectral techniques applied to sparse random graphs*, Random
Structures & Algorithms 27 (2005) 251–275, Section 2: for `pn ≥ c log n`, the adjacency matrix `A`
of `G(n, p)` satisfies `‖A − E A‖ = O(√(pn))` with high probability. The argument goes back to Kahn
and Szemerédi's bound for random regular graphs (Friedman, Kahn, Szemerédi, STOC 1989). The
formalization follows the presentation of P. Chin, A. Rao, V. Vu, *Stochastic block model and
community detection in sparse graphs: a spectral algorithm with optimal rate of recovery*, COLT
2015 (arXiv:1501.05021, Appendix A.1 and the appendix that proves their heavy-pair lemma); C.
Hoffman, M. Kahle, E. Paquette, *Spectral gaps of random graphs and applications*
(arXiv:1201.0425, the proof of their bound for the adjacency matrix) is a second write-up.

**Statement.** [`feigeOfek`](FeigeOfek.lean): for all `c, a > 0` there is `C` such that, whenever
`pn ≥ c log n`, `‖A − E A‖_op ≤ C √(pn)` with probability at least `1 − n^(−a)`. This is exactly the
sparse paper's Lemma A.7, which the library proves from it (`PowerOfFew.Sparse.lemmaA_7`), in place
of the paper's derivation from two cited results (`../RandomMatrix/`).

**Proof**, one file per step:

| Step | File | Result |
| --- | --- | --- |
| a net of the unit ball with at most `(33e)ⁿ` points; the operator norm is at most twice the largest value of the bilinear form on it | [`Basic/Analysis/GridNet.lean`](../../../Basic/Analysis/GridNet.lean) | `card_gridNet_le`, `Matrix.norm_toEuclideanCLM_le_of_gridNet` |
| exponential moments of weighted Bernoulli sums (Bernstein type) | [`Basic/Probability/WeightedBernoulli.lean`](../../../Basic/Probability/WeightedBernoulli.lean) | `IsBernoulliFamily.measureReal_le_sum_mul_le` |
| the binomial tail `P(Z ≥ k) ≤ (e p m / k)^k` | [`Basic/Probability/Chernoff.lean`](../../../Basic/Probability/Chernoff.lean) | `IsBernoulliFamily.measureReal_sum_ge_le_exp_mul_log` |
| edge counts, bounded degrees, discrepancy, light and heavy parts | [`Defs.lean`](Defs.lean) | definitions |
| the light pairs, for all points of the net at once | [`Light.lean`](Light.lean) | `lightSum_le` |
| bounded degrees and discrepancy of `G(n, p)` | [`Properties.lean`](Properties.lean) | `exists_degreeBound_discrepancy` |
| the six cases of the heavy pairs, on block data | [`SixCases.lean`](SixCases.lean) | `sum_blocks_le` |
| the heavy pairs | [`Heavy.lean`](Heavy.lean) | `heavySum_le` |
| the assembly | [`FeigeOfek.lean`](FeigeOfek.lean) | `feigeOfek` |

**One correction to the presentation followed.** Chin, Rao and Vu state the discrepancy alternative
`e(S, T) log(e(S, T)/μ(S, T)) ≤ c₃ |T| log(n/|T|)` for all sets `S, T`; the union bound that proves
it controls only `m = max(|S|, |T|)` in place of `|T|`, as Hoffman, Kahle and Paquette state it. The
formalization uses `m`, and treats the block pairs with `|S_i| ≤ |T_j|` and those with `|S_i| > |T_j|`
separately, exchanging the roles of the two vectors.
