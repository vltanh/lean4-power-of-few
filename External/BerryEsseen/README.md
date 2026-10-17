# Berry–Esseen inequality with Shevtsova's constant (assumed)

**Source.** I. G. Shevtsova, *An improvement of convergence rate estimates in the Lyapunov
theorem*, Doklady Mathematics 82(3) (2010), 862–864: for independent real random variables
`X₁, …, Xₘ` (`m ≥ 1`) with zero means, finite absolute third moments and `B² = ∑ E Xᵢ² > 0`,
`sup_x |P(X₁ + ⋯ + Xₘ ≤ x B) − Φ(x)| ≤ C₀ ∑ E|Xᵢ|³ / B³` with `C₀ ≤ 0.5600`.

**How the papers use it.** The dense paper (Theorem 2.2) and the sparse paper (Theorem A.1) quote
it with `C₀ = 0.56` and apply it to sums of `±Bernoulli(p)` variables (differences of two
independent binomial variables): dense Lemmas 2.3 and 2.4, sparse Corollary A.2 and Lemma A.3.
Their explicit constants (the dense paper's `P₁`, the `0.6` and `0.7` of its Claims 2.5 and 2.6,
the sparse paper's `D_c`) depend on the value `0.56`.

Both papers omit the word "independent" from the statement; Shevtsova's theorem and both papers'
applications have it. Shevtsova states the bound for `P(Sₘ < x B)`; since `Φ` is continuous, the
two forms are equivalent.

**In the formalization.** `PowerOfFew.ShevtsovaBerryEsseen` is the proposition
`PowerOfFew.BerryEsseenInequality 0.56`, a hypothesis of every theorem whose proof uses it. It is
defined in `PowerOfFew/Defs.lean`, not in this directory, because the Challenge's statements use it:
every definition of the Challenge lives in the one module of shared definitions that
`Challenge.lean` copies. It is restricted to probability spaces in `Type` and to summands
with positive variances, which makes it weaker, not stronger, than Shevtsova's theorem.
`PowerOfFew.berryEsseen_signedBernoulli` (`PowerOfFew/Model/BerryEsseen.lean`) derives the form for
signed Bernoulli sums.

**What Lean lacks.** Mathlib has characteristic functions, Lévy's continuity theorem and the central
limit theorem for i.i.d. variables (`Mathlib/Probability/CentralLimitTheorem.lean`), but no rate of
convergence, so no Berry–Esseen inequality. Shevtsova's constant rests on Prawitz's smoothing inequality and extensive
computer-assisted estimates of characteristic functions. The Lean library
[ProbabilityApproximation](https://reservoir.lean-lang.org/@Polarnova/ProbabilityApproximation)
proves Chen and Shao's non-uniform bound by Stein's method, with a much larger constant, which
does not give the papers' numbers.
