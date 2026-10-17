module

public import Mathlib

/-!
# One-sided Chebyshev and Hoeffding bounds

The forms of Chebyshev's and Hoeffding's inequalities that the two papers use.

* `measureReal_le_le_variance_div_sq`, `measureReal_ge_le_variance_div_sq`: Chebyshev's inequality
  for a lower and an upper tail beyond the mean.
* `measureReal_sum_ge_add_le_exp`, `measureReal_sum_le_sub_le_exp`: **Hoeffding's inequality**
  for sums of independent bounded random variables (dense paper, Theorem 3.1), from Mathlib's
  sub-Gaussian version (`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`) and Hoeffding's
  lemma (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`).
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Chebyshev's inequality below the mean: `P(X ≤ t) ≤ Var X / (E X − t)²` for `t < E X`. -/
theorem measureReal_le_le_variance_div_sq {X : Ω → ℝ} (hX : MemLp X 2 μ) {t : ℝ}
    (ht : t < μ[X]) : μ.real {ω | X ω ≤ t} ≤ variance X μ / (μ[X] - t) ^ 2 := by
  sorry

/-- Chebyshev's inequality above the mean: `P(X ≥ t) ≤ Var X / (t − E X)²` for `t > E X`. -/
theorem measureReal_ge_le_variance_div_sq {X : Ω → ℝ} (hX : MemLp X 2 μ) {t : ℝ}
    (ht : μ[X] < t) : μ.real {ω | t ≤ X ω} ≤ variance X μ / (t - μ[X]) ^ 2 := by
  sorry

/-- **Hoeffding's inequality** (dense paper, Theorem 3.1, `D:thm:hoeffding`), upper tail: if
`X i`, `i ∈ s`, are independent with values in `[a i, b i]`, then
`P(∑ X i ≥ E ∑ X i + t) ≤ exp(−2t² / ∑ (b i − a i)²)` for `t ≥ 0`. -/
theorem measureReal_sum_ge_add_le_exp {X : ι → Ω → ℝ} (hX : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (s : Finset ι) (a b : ι → ℝ)
    (hab : ∀ i ∈ s, ∀ ω, X i ω ∈ Set.Icc (a i) (b i)) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | (∫ ω', ∑ i ∈ s, X i ω' ∂μ) + t ≤ ∑ i ∈ s, X i ω} ≤
      Real.exp (-2 * t ^ 2 / ∑ i ∈ s, (b i - a i) ^ 2) := by
  sorry

/-- **Hoeffding's inequality** (dense paper, Theorem 3.1), lower tail:
`P(∑ X i ≤ E ∑ X i − t) ≤ exp(−2t² / ∑ (b i − a i)²)` for `t ≥ 0`. -/
theorem measureReal_sum_le_sub_le_exp {X : ι → Ω → ℝ} (hX : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (s : Finset ι) (a b : ι → ℝ)
    (hab : ∀ i ∈ s, ∀ ω, X i ω ∈ Set.Icc (a i) (b i)) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ (∫ ω', ∑ i ∈ s, X i ω' ∂μ) - t} ≤
      Real.exp (-2 * t ^ 2 / ∑ i ∈ s, (b i - a i) ^ 2) := by
  sorry

end ProbabilityTheory
