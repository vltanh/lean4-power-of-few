# `Basic`: general mathematics used by the formalization

These files import only Mathlib and each other, never the libraries `External` and `PowerOfFew`, and
are named as Mathlib would name them, so that they can be contributed upstream.

| File | Contents | Where it could go |
| --- | --- | --- |
| `Analysis/SpecialFunctions/CubeRoot.lean` | `Real.one_sub_two_mul_sq_div_three_le`: `(1 − 2b)²/3 ≤ 1 − b/2 − (3/2) b^(1/3) (1 − b)^(2/3)` on `[0, 1/2]` (the sparse paper's Lemma 2.4), via a polynomial factorization | specific to the paper; stays here |
| `Analysis/SpecialFunctions/ExpLog.lean` | `Real.log_natCast_le_two_mul_sqrt`, `Real.mul_exp_neg_div_le` | small consequences of Mathlib's `Real.log_le_sub_one_of_pos` and `Real.quadratic_le_exp_of_nonneg`; stay here |
| `Combinatorics/Choose.lean` | `Nat.centralBinom_lt_four_pow_div_sqrt` (`C(2m, m) < 4^m/√(2m)`, Matoušek–Nešetřil's proof) and `Nat.choose_le_exp_mul_binEntropy` (`C(n, k) ≤ e^(n H(k/n))`, via Stirling's bounds) | Mathlib's `Data/Nat/Choose/Central` has the lower bounds `Nat.four_pow_lt_mul_centralBinom`, `Nat.four_pow_le_two_mul_add_one_mul_central_binom` but not this upper bound; the entropy bound fits next to `Real.binEntropy` |
| `Probability/Combinatorics/BinomialRandomGraph/EdgeVariables.lean` | Mathlib's binomial random graph `SimpleGraph.binomialRandom` on `Fin n` as the image of independent edge variables (`SimpleGraph.edgeLaw`, `graphOfEdges`, `binomialRandom_eq_map_edgeLaw`); the edge indicators form a Bernoulli family (`isBernoulliFamily_edgeInd`) | Mathlib's `Probability/Combinatorics/BinomialRandomGraph`, next to `binomialRandom_eq_map` |
| `Probability/BernoulliFamily.lean` | the predicate `ProbabilityTheory.IsBernoulliFamily` (independent `{0, 1}`-valued variables with `P(X = 1) = p`), its moments and the binomial law of its sums | Mathlib's `Probability/Distributions`, next to the binomial distribution |
| `Probability/Concentration.lean` | Chebyshev's inequality for both tails, and Hoeffding's inequality for sums of independent bounded variables (the dense paper's Theorem 3.1), from Mathlib's sub-Gaussian bounds | thin wrappers of Mathlib's `ProbabilityTheory.meas_ge_le_variance_div_sq` and `HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`; stay here |
| `Probability/Chernoff.lean` | Chernoff bounds for sums of a Bernoulli family: the relative-entropy form `P(Z ≤ am) ≤ e^(−m D(a‖p))` and the forms `exp(−(T − pm)²/(2T))`, `exp(−(pm − T)²/(2pm))` (the sparse paper's (29), (30)) | Mathlib has no Chernoff bound in relative-entropy form; a candidate for `Probability/Moments` |
