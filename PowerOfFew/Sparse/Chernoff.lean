module

public import Basic.Probability.Chernoff

/-!
# Sparse paper, Appendix A: a Chernoff bound for a binomial variable of random size

Lemma A.6 of the sparse paper. A variable `X ∼ Bin(Y, p)` with a random size `Y` (independent
coins) is represented as `X = ∑_{i < Y} ξᵢ`, with `ξ` a Bernoulli(`p`) family independent of `Y`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- **Lemma A.6** (`S:lem:gen-chernoff`). Let `p ∈ (0, 1)` and `m > 0`. If `Y` takes values in
`[0, m] ∩ ℤ` and `X ∼ Bin(Y, p)`, then for every `t > 0`,
`P(X ≥ pm + t) ≤ exp(−max{t² / (2(pm + t)), t² / (2(1 − p)m)})`. -/
theorem lemmaA_6 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {m : ℝ} (hm : 0 < m) {Y : Ω → ℕ} (hYm : Measurable Y)
    (hY : ∀ ω, (Y ω : ℝ) ≤ m) {ξ : ℕ → Ω → ℝ} (hξ : IsBernoulliFamily μ p ξ)
    (hindep : IndepFun Y (fun ω i => ξ i ω) μ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | p * m + t ≤ ∑ i ∈ Finset.range (Y ω), ξ i ω} ≤
      Real.exp (-max (t ^ 2 / (2 * (p * m + t))) (t ^ 2 / (2 * (1 - p) * m))) := by
  sorry

end PowerOfFew.Sparse

end
