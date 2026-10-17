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
  have hc : 0 < μ[X] - t := sub_pos.mpr ht
  have hsub : {ω | X ω ≤ t} ⊆ {ω | μ[X] - t ≤ |X ω - μ[X]|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [abs_sub_comm]
    exact le_trans (by linarith) (le_abs_self _)
  calc μ.real {ω | X ω ≤ t} ≤ μ.real {ω | μ[X] - t ≤ |X ω - μ[X]|} := measureReal_mono hsub
    _ = (μ {ω | μ[X] - t ≤ |X ω - μ[X]|}).toReal := rfl
    _ ≤ (ENNReal.ofReal (variance X μ / (μ[X] - t) ^ 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (meas_ge_le_variance_div_sq hX hc)
    _ = variance X μ / (μ[X] - t) ^ 2 :=
        ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))

/-- Chebyshev's inequality above the mean: `P(X ≥ t) ≤ Var X / (t − E X)²` for `t > E X`. -/
theorem measureReal_ge_le_variance_div_sq {X : Ω → ℝ} (hX : MemLp X 2 μ) {t : ℝ}
    (ht : μ[X] < t) : μ.real {ω | t ≤ X ω} ≤ variance X μ / (t - μ[X]) ^ 2 := by
  have hc : 0 < t - μ[X] := sub_pos.mpr ht
  have hsub : {ω | t ≤ X ω} ⊆ {ω | t - μ[X] ≤ |X ω - μ[X]|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact le_trans (by linarith) (le_abs_self _)
  calc μ.real {ω | t ≤ X ω} ≤ μ.real {ω | t - μ[X] ≤ |X ω - μ[X]|} := measureReal_mono hsub
    _ = (μ {ω | t - μ[X] ≤ |X ω - μ[X]|}).toReal := rfl
    _ ≤ (ENNReal.ofReal (variance X μ / (t - μ[X]) ^ 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (meas_ge_le_variance_div_sq hX hc)
    _ = variance X μ / (t - μ[X]) ^ 2 :=
        ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))

/-- **Hoeffding's inequality** (dense paper, Theorem 3.1, `D:thm:hoeffding`), upper tail: if
`X i`, `i ∈ s`, are independent with values in `[a i, b i]`, then
`P(∑ X i ≥ E ∑ X i + t) ≤ exp(−2t² / ∑ (b i − a i)²)` for `t ≥ 0`. -/
theorem measureReal_sum_ge_add_le_exp {X : ι → Ω → ℝ} (hX : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (s : Finset ι) (a b : ι → ℝ)
    (hab : ∀ i ∈ s, ∀ ω, X i ω ∈ Set.Icc (a i) (b i)) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | (∫ ω', ∑ i ∈ s, X i ω' ∂μ) + t ≤ ∑ i ∈ s, X i ω} ≤
      Real.exp (-2 * t ^ 2 / ∑ i ∈ s, (b i - a i) ^ 2) := by
  -- The centred variables `X i − E X i` are independent and, by Hoeffding's lemma,
  -- sub-Gaussian with parameter `((b i − a i) / 2)²`.
  have hYind : iIndepFun (fun i ω => X i ω - μ[X i]) μ :=
    hX.comp (fun i (x : ℝ) => x - ∫ ω, X i ω ∂μ) (fun i => measurable_id.sub_const _)
  have hint : ∀ i ∈ s, Integrable (X i) μ := fun i hi =>
    Integrable.of_mem_Icc (a i) (b i) (hm i).aemeasurable (ae_of_all _ (hab i hi))
  have hsub : ∀ i ∈ s,
      HasSubgaussianMGF (fun ω => X i ω - μ[X i]) ((‖b i - a i‖₊ / 2) ^ 2) μ := fun i hi =>
    hasSubgaussianMGF_of_mem_Icc (hm i).aemeasurable (ae_of_all _ (hab i hi))
  have key := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hYind hsub ht
  -- The mean of the sum is the sum of the means.
  have hset : {ω | (∫ ω', ∑ i ∈ s, X i ω' ∂μ) + t ≤ ∑ i ∈ s, X i ω} =
      {ω | t ≤ ∑ i ∈ s, (X i ω - μ[X i])} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.sum_sub_distrib]
    rw [integral_finsetSum s hint]
    constructor <;> intro h <;> linarith
  have hc : ((∑ i ∈ s, (‖b i - a i‖₊ / 2) ^ 2 : NNReal) : ℝ) =
      (∑ i ∈ s, (b i - a i) ^ 2) / 4 := by
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, div_pow, sq_abs]
    ring
  -- `2 ∑ ((b i − a i) / 2)² = ∑ (b i − a i)² / 2`, so the exponents agree (also when the sum
  -- vanishes, both sides being `exp 0 = 1` with `x / 0 = 0`).
  rw [hset]
  refine key.trans (le_of_eq ?_)
  rw [hc]
  congr 1
  ring

/-- **Hoeffding's inequality** (dense paper, Theorem 3.1), lower tail:
`P(∑ X i ≤ E ∑ X i − t) ≤ exp(−2t² / ∑ (b i − a i)²)` for `t ≥ 0`. -/
theorem measureReal_sum_le_sub_le_exp {X : ι → Ω → ℝ} (hX : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (s : Finset ι) (a b : ι → ℝ)
    (hab : ∀ i ∈ s, ∀ ω, X i ω ∈ Set.Icc (a i) (b i)) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ (∫ ω', ∑ i ∈ s, X i ω' ∂μ) - t} ≤
      Real.exp (-2 * t ^ 2 / ∑ i ∈ s, (b i - a i) ^ 2) := by
  -- The upper tail applied to `−X i ∈ [−b i, −a i]`.
  have h := measureReal_sum_ge_add_le_exp (μ := μ) (X := fun i ω => -X i ω)
    (hX.comp (fun _ x => -x) (fun _ => measurable_neg)) (fun i => (hm i).neg) s
    (fun i => -b i) (fun i => -a i)
    (fun i hi ω => ⟨neg_le_neg (hab i hi ω).2, neg_le_neg (hab i hi ω).1⟩) ht
  have hS : ∑ i ∈ s, (-a i - -b i) ^ 2 = ∑ i ∈ s, (b i - a i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hS] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, Finset.sum_neg_distrib, integral_neg]
  constructor <;> intro h <;> linarith

end ProbabilityTheory
