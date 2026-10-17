module

public import Basic.Probability.BernoulliFamily

/-!
# Chernoff bounds for sums of independent Bernoulli variables

The Chernoff bounds that the sparse paper uses without proof, for `Z = ∑ i ∈ s, X i` with `X` a
family of independent Bernoulli(`p`) variables and `m = #s` (so `Z ∼ Bin(m, p)`):

* `IsBernoulliFamily.measureReal_sum_le_le_exp_klBern`: the lower tail
  `P(Z ≤ a m) ≤ exp(−m D(a ‖ p))` for `0 ≤ a ≤ p`, with the relative entropy
  `D(a ‖ p) = a log(a / p) + (1 − a) log((1 − a) / (1 − p))` (sparse paper, proof of Lemma A.4);
* `IsBernoulliFamily.measureReal_sum_ge_le_exp`, `IsBernoulliFamily.measureReal_sum_le_le_exp`:
  `P(Z ≥ T) ≤ exp(−(T − pm)² / (2T))` for `T > pm` and `P(Z ≤ T) ≤ exp(−(pm − T)² / (2pm))` for
  `T < pm` (sparse paper, proof of Lemma A.6, its equations (29) and (30)).
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- The relative entropy `D(a ‖ p) = a log(a / p) + (1 − a) log((1 − a) / (1 − p))` of two
Bernoulli laws (with `0 log 0 = 0`). -/
noncomputable def klBern (a p : ℝ) : ℝ :=
  a * Real.log (a / p) + (1 - a) * Real.log ((1 - a) / (1 - p))

namespace IsBernoulliFamily

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ℝ}
  {X : ι → Ω → ℝ}

/-- **Chernoff's bound** for the lower tail, in relative-entropy form:
`P(∑ i ∈ s, X i ≤ a #s) ≤ exp(−#s · D(a ‖ p))` for `0 ≤ a ≤ p < 1`. -/
theorem measureReal_sum_le_le_exp_klBern (hX : IsBernoulliFamily μ p X) (hp0 : 0 < p)
    (hp1 : p < 1) (s : Finset ι) {a : ℝ} (ha0 : 0 ≤ a) (hap : a ≤ p) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ a * s.card} ≤ Real.exp (-(s.card * klBern a p)) := by
  sorry

/-- **Chernoff's bound** for the upper tail: `P(Z ≥ T) ≤ exp(−(T − pm)² / (2T))` for `T > pm`,
where `Z = ∑ i ∈ s, X i` and `m = #s` (sparse paper, equation (29)). -/
theorem measureReal_sum_ge_le_exp (hX : IsBernoulliFamily μ p X) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Finset ι) {T : ℝ} (hT : p * s.card < T) :
    μ.real {ω | T ≤ ∑ i ∈ s, X i ω} ≤ Real.exp (-((T - p * s.card) ^ 2 / (2 * T))) := by
  sorry

/-- **Chernoff's bound** for the lower tail: `P(Z ≤ T) ≤ exp(−(pm − T)² / (2pm))` for `T < pm`,
where `Z = ∑ i ∈ s, X i` and `m = #s` (sparse paper, equation (30)). -/
theorem measureReal_sum_le_le_exp (hX : IsBernoulliFamily μ p X) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Finset ι) {T : ℝ} (hT : T < p * s.card) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ T} ≤ Real.exp (-((p * s.card - T) ^ 2 / (2 * (p * s.card)))) := by
  sorry

end IsBernoulliFamily

end ProbabilityTheory
