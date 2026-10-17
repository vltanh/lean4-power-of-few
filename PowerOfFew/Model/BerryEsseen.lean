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
  classical
  set m := S.card with hm
  set σ2 := p * (1 - p) with hσ2
  have hσ2pos : 0 < σ2 := mul_pos hp0 (by linarith)
  have hmpos : 0 < m := Finset.card_pos.2 hS
  -- Reindex the summands by `Fin m`.
  let e : Fin m ≃ S := S.equivFin.symm
  let idx : Fin m → ι := fun j => (e j).1
  have hidx : Function.Injective idx := fun a b h => e.injective (Subtype.ext h)
  let Y : Fin m → Ω → ℝ := fun j ω => s (idx j) * (X (idx j) ω - p)
  have hY_meas : ∀ j, Measurable (Y j) := fun j =>
    measurable_const.mul ((hX.measurable _).sub measurable_const)
  have hY_indep : iIndepFun Y μ :=
    (hX.comp hidx).indep.comp (fun j x => s (idx j) * (x - p)) (fun j => by fun_prop)
  have hsq : ∀ j, s (idx j) ^ 2 = 1 := fun j => by
    rcases hs (idx j) with h | h <;> rw [h] <;> norm_num
  have habs : ∀ j, |s (idx j)| = 1 := fun j => by
    rcases hs (idx j) with h | h <;> rw [h] <;> norm_num
  have hY_int : ∀ j, ∫ ω, Y j ω ∂μ = 0 := by
    intro j
    simp only [Y]
    rw [integral_const_mul, integral_sub (hX.integrable _) (integrable_const _),
      hX.integral_eq, integral_const]
    simp
  have hY_sq : ∀ j, ∫ ω, Y j ω ^ 2 ∂μ = σ2 := by
    intro j
    have h : ∀ ω, Y j ω ^ 2 = (X (idx j) ω - p) ^ 2 := fun ω => by
      simp only [Y]
      rw [mul_pow, hsq, one_mul]
    simp_rw [h]
    exact hX.integral_sq_sub _
  have hY_abs : ∀ j, ∫ ω, |Y j ω| ^ 3 ∂μ = σ2 * (1 - 2 * σ2) := by
    intro j
    have h : ∀ ω, |Y j ω| ^ 3 = |X (idx j) ω - p| ^ 3 := fun ω => by
      simp only [Y]
      rw [abs_mul, habs, one_mul]
    simp_rw [h]
    rw [hX.integral_abs_pow_three_sub hp0.le hp1.le]
    ring
  have hY_abs_int : ∀ j, Integrable (fun ω => |Y j ω| ^ 3) μ := by
    intro j
    refine Integrable.of_bound
      ((continuous_abs.measurable.comp (hY_meas j)).pow_const 3).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => ?_)
    have h : |Y j ω| ≤ 1 := by
      simp only [Y]
      rw [abs_mul, habs, one_mul, abs_le]
      rcases hX.zero_or_one (idx j) ω with h | h <;> rw [h] <;> constructor <;> linarith
    rw [Real.norm_eq_abs, abs_pow, abs_abs]
    exact pow_le_one₀ (abs_nonneg _) h
  -- Apply the Berry–Esseen inequality at `x / (σ √m)`.
  have key := hBE Ω μ m Y hmpos hY_meas hY_indep hY_abs_int hY_int
    (fun j => by rw [hY_sq]; exact hσ2pos) (x / (Real.sqrt σ2 * Real.sqrt m))
  have hsum_sq : ∑ j, ∫ ω, Y j ω ^ 2 ∂μ = m * σ2 := by simp [hY_sq]
  have hsum_abs : ∑ j, ∫ ω, |Y j ω| ^ 3 ∂μ = m * (σ2 * (1 - 2 * σ2)) := by simp [hY_abs]
  have hsumY : ∀ ω, ∑ j, Y j ω = ∑ i ∈ S, s i * (X i ω - p) := by
    intro ω
    rw [← Finset.sum_coe_sort S]
    exact Equiv.sum_comp e (fun i : S => s i * (X i ω - p))
  have hsqrt : Real.sqrt (m * σ2) = Real.sqrt σ2 * Real.sqrt m := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), mul_comm]
  have hpos : 0 < Real.sqrt σ2 * Real.sqrt m := by
    have : (0 : ℝ) < m := by exact_mod_cast hmpos
    positivity
  have hx : x / (Real.sqrt σ2 * Real.sqrt m) * (Real.sqrt σ2 * Real.sqrt m) = x :=
    div_mul_cancel₀ _ hpos.ne'
  simp_rw [hsumY] at key
  rw [hsum_sq, hsum_abs, hsqrt, hx] at key
  refine key.trans (le_of_eq ?_)
  have hs2 : Real.sqrt σ2 ^ 2 = σ2 := Real.sq_sqrt hσ2pos.le
  have hm2 : Real.sqrt (m : ℝ) ^ 2 = m := Real.sq_sqrt (Nat.cast_nonneg _)
  have h3 : (Real.sqrt σ2 * Real.sqrt m) ^ 3 = (m * σ2) * (Real.sqrt σ2 * Real.sqrt m) := by
    rw [show (Real.sqrt σ2 * Real.sqrt m) ^ 3 =
      (Real.sqrt σ2 ^ 2 * Real.sqrt m ^ 2) * (Real.sqrt σ2 * Real.sqrt m) by ring, hs2, hm2]
    ring
  have hmσ : (m : ℝ) * σ2 ≠ 0 := by
    have : (0 : ℝ) < m := by exact_mod_cast hmpos
    positivity
  rw [h3]
  field_simp

end PowerOfFew

end
