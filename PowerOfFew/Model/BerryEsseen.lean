module

public import PowerOfFew.Model.Normal
public import Basic.Probability.BernoulliFamily

/-!
# The Berry–Esseen inequality for sums of signed Bernoulli variables

Both papers apply the Berry–Esseen inequality to sums `∑ sᵢ Xᵢ` of independent Bernoulli(`p`)
variables with signs `sᵢ = ±1` (the difference of two independent binomial variables). Each
centred summand `sᵢ (Xᵢ − p)` has variance `σ² = p(1 − p)` and third absolute moment
`σ²(1 − 2σ²)`, so the bound becomes `C (1 − 2σ²) / (σ √m)` for `m` summands
(`berryEsseen_signedBernoulli`). This is the computation of the dense paper's Lemma 2.3 and the
sparse paper's Corollary A.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew

/-- The Berry–Esseen inequality with constant `C`, applied to `∑_{i ∈ S} sᵢ (Xᵢ − p)` for a
Bernoulli(`p`) family `X` and signs `sᵢ = ±1`: for every `x`,
`|P(∑ sᵢ (Xᵢ − p) ≤ x) − Φ(x / (σ √#S))| ≤ C (1 − 2σ²) / (σ √#S)`, `σ = √(p(1 − p))`. -/
theorem berryEsseen_signedBernoulli {C : ℝ} (hBE : BerryEsseenInequality C) {Ω : Type}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) {X : ι → Ω → ℝ} (hX : IsBernoulliFamily μ p X) (s : ι → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) {S : Finset ι} (hS : S.Nonempty) (x : ℝ) :
    |μ.real {ω | ∑ i ∈ S, s i * (X i ω - p) ≤ x} -
        Φ (x / (Real.sqrt (p * (1 - p)) * Real.sqrt S.card))| ≤
      C * (1 - 2 * (p * (1 - p))) / (Real.sqrt (p * (1 - p)) * Real.sqrt S.card) := by
  sorry

end PowerOfFew

end
