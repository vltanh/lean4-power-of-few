module

public import Basic.Probability.BernoulliFamily

/-!
# Weighted sums of independent Bernoulli variables

An exponential-moment bound of Bernstein type for `∑ aᵢ (Xᵢ − p)`, where `X` is a family of
independent Bernoulli(`p`) variables and the weights are small: if `θ |aᵢ| ≤ 1` for every `i`, then
`E exp(θ ∑ aᵢ (Xᵢ − p)) ≤ exp(p θ² ∑ aᵢ²)`. Each factor is
`E exp(θ aᵢ (Xᵢ − p)) = e^(−θ aᵢ p) (1 − p + p e^(θ aᵢ)) ≤ exp(p (e^(θ aᵢ) − 1 − θ aᵢ))`, and
`eˢ − 1 − s ≤ s²` for `|s| ≤ 1`.

Feige and Ofek use this bound, in the form of Bernstein's inequality, for the light pairs of their
bound on the spectral norm of a random graph (`PowerOfFew.FeigeOfek.lightSum_le`).
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

namespace IsBernoulliFamily

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ℝ}
  {X : ι → Ω → ℝ}

/-- The exponential moment of a weighted centred sum: if `θ ≥ 0` and `θ |aᵢ| ≤ 1` for `i ∈ s`,
then `E exp(θ ∑_{i ∈ s} aᵢ (Xᵢ − p)) ≤ exp(p θ² ∑_{i ∈ s} aᵢ²)`. -/
theorem integral_exp_mul_sum_le (hX : IsBernoulliFamily μ p X) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Finset ι) (a : ι → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) (ha : ∀ i ∈ s, θ * |a i| ≤ 1) :
    ∫ ω, Real.exp (θ * ∑ i ∈ s, a i * (X i ω - p)) ∂μ ≤
      Real.exp (p * θ ^ 2 * ∑ i ∈ s, a i ^ 2) := by
  sorry

/-- The upper tail (Markov's inequality for the exponential moment): under the same conditions,
`P(t ≤ ∑_{i ∈ s} aᵢ (Xᵢ − p)) ≤ exp(p θ² ∑_{i ∈ s} aᵢ² − θ t)` for every `t`. -/
theorem measureReal_le_sum_mul_le (hX : IsBernoulliFamily μ p X) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Finset ι) (a : ι → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) (ha : ∀ i ∈ s, θ * |a i| ≤ 1) (t : ℝ) :
    μ.real {ω | t ≤ ∑ i ∈ s, a i * (X i ω - p)} ≤
      Real.exp (p * θ ^ 2 * ∑ i ∈ s, a i ^ 2 - θ * t) := by
  sorry

end IsBernoulliFamily

end ProbabilityTheory
