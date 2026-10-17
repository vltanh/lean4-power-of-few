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

/-- One variable: `E e^(c (Xᵢ − p)) = e^(−cp) (1 − p + p eᶜ) ≤ e^(−cp) e^(p (eᶜ − 1))
= e^(p (eᶜ − 1 − c)) ≤ e^(p c²)` for `|c| ≤ 1`. -/
private lemma integral_exp_mul_sub_le (hX : IsBernoulliFamily μ p X) (hp0 : 0 ≤ p) (i : ι)
    {c : ℝ} (hc : |c| ≤ 1) :
    ∫ ω, Real.exp (c * (X i ω - p)) ∂μ ≤ Real.exp (p * c ^ 2) := by
  -- `e^(c (Xᵢ − p)) = e^(−cp) + (e^(c (1 − p)) − e^(−cp)) Xᵢ` since `Xᵢ ∈ {0, 1}`.
  have hfun : (fun ω => Real.exp (c * (X i ω - p))) =
      fun ω => Real.exp (-(c * p)) + (Real.exp (c * (1 - p)) - Real.exp (-(c * p))) * X i ω := by
    ext ω
    rcases hX.zero_or_one i ω with h | h <;> rw [h]
    · rw [zero_sub, mul_neg, mul_zero, add_zero]
    · ring
  rw [hfun, integral_add (integrable_const _) ((hX.integrable i).const_mul _), integral_const,
    integral_const_mul, hX.integral_eq i, probReal_univ, one_smul]
  have h1 : Real.exp (c * (1 - p)) = Real.exp (-(c * p)) * Real.exp c := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : p * (Real.exp c - 1) + 1 ≤ Real.exp (p * (Real.exp c - 1)) := Real.add_one_le_exp _
  have h3 : Real.exp c - 1 - c ≤ c ^ 2 := (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le hc)
  calc Real.exp (-(c * p)) + (Real.exp (c * (1 - p)) - Real.exp (-(c * p))) * p
      = Real.exp (-(c * p)) * (p * (Real.exp c - 1) + 1) := by rw [h1]; ring
    _ ≤ Real.exp (-(c * p)) * Real.exp (p * (Real.exp c - 1)) := by gcongr
    _ = Real.exp (p * (Real.exp c - 1 - c)) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (p * c ^ 2) := by gcongr

/-- The exponential moment of a weighted centred sum: if `θ ≥ 0` and `θ |aᵢ| ≤ 1` for `i ∈ s`,
then `E exp(θ ∑_{i ∈ s} aᵢ (Xᵢ − p)) ≤ exp(p θ² ∑_{i ∈ s} aᵢ²)`. -/
theorem integral_exp_mul_sum_le (hX : IsBernoulliFamily μ p X) (hp0 : 0 ≤ p) (s : Finset ι)
    (a : ι → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) (ha : ∀ i ∈ s, θ * |a i| ≤ 1) :
    ∫ ω, Real.exp (θ * ∑ i ∈ s, a i * (X i ω - p)) ∂μ ≤
      Real.exp (p * θ ^ 2 * ∑ i ∈ s, a i ^ 2) := by
  -- The centred weighted variables `Yᵢ = aᵢ (Xᵢ − p)` are independent, so the exponential
  -- moment of their sum is the product of theirs.
  set Y : ι → Ω → ℝ := fun i => (fun x => a i * (x - p)) ∘ X i with hY
  have hYmeas : ∀ i, Measurable (Y i) := fun i =>
    (measurable_const.mul (measurable_id.sub_const p)).comp (hX.measurable i)
  have hYind : iIndepFun Y μ :=
    hX.indep.comp _ fun i => measurable_const.mul (measurable_id.sub_const p)
  have hint : ∫ ω, Real.exp (θ * ∑ i ∈ s, a i * (X i ω - p)) ∂μ = mgf (∑ i ∈ s, Y i) μ θ := by
    simp only [mgf, Finset.sum_apply, hY, Function.comp_apply]
  rw [hint, hYind.mgf_sum hYmeas s]
  calc ∏ i ∈ s, mgf (Y i) μ θ ≤ ∏ i ∈ s, Real.exp (p * (θ * a i) ^ 2) := by
        refine Finset.prod_le_prod₀ (fun i _ => mgf_nonneg) fun i hi => ?_
        have hc : |θ * a i| ≤ 1 := by rw [abs_mul, abs_of_nonneg hθ]; exact ha i hi
        have h := integral_exp_mul_sub_le hX hp0 i hc
        simp only [mgf, hY, Function.comp_apply]
        convert h using 3 with ω
        rw [mul_assoc]
    _ = Real.exp (p * θ ^ 2 * ∑ i ∈ s, a i ^ 2) := by
        rw [← Real.exp_sum, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring

/-- The upper tail (Markov's inequality for the exponential moment): under the same conditions,
`P(t ≤ ∑_{i ∈ s} aᵢ (Xᵢ − p)) ≤ exp(p θ² ∑_{i ∈ s} aᵢ² − θ t)` for every `t`. -/
theorem measureReal_le_sum_mul_le (hX : IsBernoulliFamily μ p X) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Finset ι) (a : ι → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) (ha : ∀ i ∈ s, θ * |a i| ≤ 1) (t : ℝ) :
    μ.real {ω | t ≤ ∑ i ∈ s, a i * (X i ω - p)} ≤
      Real.exp (p * θ ^ 2 * ∑ i ∈ s, a i ^ 2 - θ * t) := by
  -- The sum lies in `[−∑ |aᵢ|, ∑ |aᵢ|]`, since `|Xᵢ − p| ≤ 1`; so its exponential is integrable.
  have hbd : ∀ ω, ∑ i ∈ s, a i * (X i ω - p) ∈
      Set.Icc (-∑ i ∈ s, |a i|) (∑ i ∈ s, |a i|) := by
    intro ω
    have h : |∑ i ∈ s, a i * (X i ω - p)| ≤ ∑ i ∈ s, |a i| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      have hx : |X i ω - p| ≤ 1 := by
        rcases hX.zero_or_one i ω with h | h <;> rw [h] <;> rw [abs_le] <;>
          constructor <;> linarith
      rw [abs_mul]
      calc |a i| * |X i ω - p| ≤ |a i| * 1 := by gcongr
        _ = |a i| := mul_one _
    exact abs_le.mp h
  have hmeas : Measurable fun ω => ∑ i ∈ s, a i * (X i ω - p) :=
    Finset.measurable_sum s fun i _ => measurable_const.mul ((hX.measurable i).sub_const p)
  have hint : Integrable (fun ω => Real.exp (θ * ∑ i ∈ s, a i * (X i ω - p))) μ :=
    integrable_exp_mul_of_mem_Icc hmeas.aemeasurable (ae_of_all _ hbd)
  refine (measure_ge_le_exp_mul_mgf (X := fun ω => ∑ i ∈ s, a i * (X i ω - p)) t hθ hint).trans ?_
  calc Real.exp (-θ * t) * mgf (fun ω => ∑ i ∈ s, a i * (X i ω - p)) μ θ
      ≤ Real.exp (-θ * t) * Real.exp (p * θ ^ 2 * ∑ i ∈ s, a i ^ 2) := by
        gcongr
        exact integral_exp_mul_sum_le hX hp0 s a hθ ha
    _ = Real.exp (p * θ ^ 2 * ∑ i ∈ s, a i ^ 2 - θ * t) := by
        rw [← Real.exp_add]
        congr 1
        ring

end IsBernoulliFamily

end ProbabilityTheory
