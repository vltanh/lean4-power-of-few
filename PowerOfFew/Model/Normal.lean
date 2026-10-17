module

public import PowerOfFew.Defs

/-!
# The normal distribution function

Facts about `Φ₀(a) = (2π)^(-1/2) ∫₀^a e^(-x²/2) dx` and `Φ = 1/2 + Φ₀`:

* `Φ_eq_cdf_gaussianReal`: `Φ` is the distribution function of Mathlib's standard Gaussian
  `gaussianReal 0 1` (so `Φ` is the `Φ` of both papers);
* oddness, monotonicity, `|Φ₀| < 1/2`, the derivative, the bound `Φ₀(a) ≤ a / √(2π)`;
* concavity on `[0, ∞)` and its consequence `Φ₀(x) ≥ min{1, x/y} Φ₀(y)` (used in both papers);
* `monotoneOn_mul_Φ₀_div`: `x ↦ x Φ₀(a / x)` is increasing on `(0, ∞)` for `a ≥ 0`, so that the
  condition `F(n, p, c) > 0` of the dense paper's Theorem 1.6 persists for larger `n`.
-/

@[expose] public section

noncomputable section

namespace PowerOfFew

/-- The integrand `x ↦ e^(-x²/2)` of `Φ₀` is continuous. -/
private lemma continuous_exp_neg_sq_div_two : Continuous fun x : ℝ => Real.exp (-x ^ 2 / 2) := by
  fun_prop

/-- The standard Gaussian density is `(2π)^(-1/2) e^(-x²/2)`. -/
private lemma gaussianPDFReal_zero_one (x : ℝ) :
    ProbabilityTheory.gaussianPDFReal 0 1 x =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  simp [ProbabilityTheory.gaussianPDFReal]

/-- `Φ` is the distribution function of the standard Gaussian law.

Proof: `cdf (gaussianReal 0 1) a = ∫_{-∞}^a φ = ∫_{-∞}^0 φ + ∫₀^a φ`, where `φ` is the standard
Gaussian density; `∫_{-∞}^0 φ = ∫_0^∞ φ` by symmetry, and the two halves add up to the total mass
`1`, so `∫_{-∞}^0 φ = 1/2`, while `∫₀^a φ = Φ₀ a`. -/
theorem Φ_eq_cdf_gaussianReal (a : ℝ) :
    Φ a = ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) a := by
  set g := ProbabilityTheory.gaussianPDFReal 0 1 with hg
  have hint : MeasureTheory.Integrable g := ProbabilityTheory.integrable_gaussianPDFReal 0 1
  -- the distribution function as an integral of the density
  have hcdf : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) a =
      ∫ x in Set.Iic a, g x := by
    rw [ProbabilityTheory.cdf_eq_real, MeasureTheory.measureReal_def,
      ProbabilityTheory.gaussianReal_apply_eq_integral 0 one_ne_zero,
      ENNReal.toReal_ofReal (MeasureTheory.setIntegral_nonneg measurableSet_Iic
        fun x _ => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x)]
  -- the two half-lines carry the same mass, by symmetry
  have hsym : ∫ x in Set.Iic (0 : ℝ), g x = ∫ x in Set.Ioi (0 : ℝ), g x := by
    calc ∫ x in Set.Iic (0 : ℝ), g x = ∫ x in Set.Iic (-0 : ℝ), g x := by rw [neg_zero]
      _ = ∫ x in Set.Ioi (0 : ℝ), g (-x) := (integral_comp_neg_Ioi 0 g).symm
      _ = ∫ x in Set.Ioi (0 : ℝ), g x := by
        congr 1; ext x; simp only [hg, gaussianPDFReal_zero_one, neg_sq]
  -- and the total mass is `1`
  have htotal : (∫ x in Set.Iic (0 : ℝ), g x) + ∫ x in Set.Ioi (0 : ℝ), g x = 1 := by
    rw [intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn,
      ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero]
  have hsplit : (∫ x in Set.Iic a, g x) - ∫ x in Set.Iic (0 : ℝ), g x = ∫ x in (0 : ℝ)..a, g x :=
    intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn
  have hΦ₀ : ∫ x in (0 : ℝ)..a, g x = Φ₀ a := by
    simp only [hg, gaussianPDFReal_zero_one, intervalIntegral.integral_const_mul, Φ₀]
  rw [hcdf, Φ]
  linarith

@[simp] theorem Φ₀_zero : Φ₀ 0 = 0 := by
  simp [Φ₀]

theorem Φ₀_neg (a : ℝ) : Φ₀ (-a) = -Φ₀ a := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := a)
    (fun x : ℝ => Real.exp (-x ^ 2 / 2))
  simp only [neg_sq, neg_zero] at h
  -- `h : ∫ x in 0..a, e^(-x²/2) = ∫ x in -a..0, e^(-x²/2)`
  rw [Φ₀, Φ₀, h, intervalIntegral.integral_symm 0 (-a), mul_neg, neg_neg]

theorem hasDerivAt_Φ₀ (a : ℝ) :
    HasDerivAt Φ₀ ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-a ^ 2 / 2)) a :=
  ((continuous_exp_neg_sq_div_two.integral_hasStrictDerivAt 0 a).hasDerivAt).const_mul _

theorem continuous_Φ₀ : Continuous Φ₀ :=
  continuous_iff_continuousAt.2 fun a => (hasDerivAt_Φ₀ a).continuousAt

theorem strictMono_Φ₀ : StrictMono Φ₀ :=
  strictMono_of_hasDerivAt_pos hasDerivAt_Φ₀ fun _ => by positivity

theorem Φ₀_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ Φ₀ a :=
  Φ₀_zero ▸ strictMono_Φ₀.monotone ha

theorem Φ₀_lt_half (a : ℝ) : Φ₀ a < 1 / 2 := by
  have h1 := ProbabilityTheory.cdf_le_one (μ := ProbabilityTheory.gaussianReal 0 1) (a + 1)
  rw [← Φ_eq_cdf_gaussianReal, Φ] at h1
  have h2 := strictMono_Φ₀ (lt_add_one a)
  linarith

theorem neg_half_lt_Φ₀ (a : ℝ) : -(1 / 2) < Φ₀ a := by
  have h := Φ₀_lt_half (-a)
  rw [Φ₀_neg] at h
  linarith

/-- `∫_a^b e^(-x²/2) dx ≤ b − a` for `a ≤ b`, since the integrand is at most `1`. -/
private lemma integral_exp_neg_sq_div_two_le {a b : ℝ} (hab : a ≤ b) :
    ∫ x in a..b, Real.exp (-x ^ 2 / 2) ≤ b - a := by
  have h : ∫ x in a..b, Real.exp (-x ^ 2 / 2) ≤ ∫ _ in a..b, (1 : ℝ) :=
    intervalIntegral.integral_mono_on hab
      (continuous_exp_neg_sq_div_two.intervalIntegrable a b) intervalIntegrable_const
      fun x _ => Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
  simpa using h

theorem Φ₀_le_div {a : ℝ} (ha : 0 ≤ a) : Φ₀ a ≤ a / Real.sqrt (2 * Real.pi) := by
  have h := integral_exp_neg_sq_div_two_le ha
  rw [sub_zero] at h
  rw [Φ₀, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem Φ₀_sub_le {a b : ℝ} (hab : a ≤ b) : Φ₀ b - Φ₀ a ≤ (b - a) / Real.sqrt (2 * Real.pi) := by
  rw [Φ₀, Φ₀, ← mul_sub,
    intervalIntegral.integral_interval_sub_left
      (continuous_exp_neg_sq_div_two.intervalIntegrable 0 b)
      (continuous_exp_neg_sq_div_two.intervalIntegrable 0 a), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (integral_exp_neg_sq_div_two_le hab) (by positivity)

/-- `Φ₀` is concave on `[0, ∞)`: its derivative `(2π)^(-1/2) e^(-x²/2)` is decreasing there. -/
theorem concaveOn_Φ₀ : ConcaveOn ℝ (Set.Ici 0) Φ₀ := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici 0) continuous_Φ₀.continuousOn
    (fun x _ => (hasDerivAt_Φ₀ x).differentiableAt.differentiableWithinAt) ?_
  rw [interior_Ici]
  intro x hx y hy hxy
  have hx' : 0 ≤ x := le_of_lt hx
  rw [(hasDerivAt_Φ₀ x).deriv, (hasDerivAt_Φ₀ y).deriv]
  gcongr

/-- `x ↦ Φ₀(x)/x` is decreasing on `(0, ∞)`. This follows from the concavity of `Φ₀` on
`[0, ∞)` and `Φ₀(0) = 0`: for `0 < x ≤ y`, `Φ₀(x) ≥ (x/y) Φ₀(y) + (1 − x/y) Φ₀(0)`. -/
private lemma antitoneOn_Φ₀_div : AntitoneOn (fun x => Φ₀ x / x) (Set.Ioi 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  have h := concaveOn_Φ₀.2 (Set.mem_Ici.2 hy.le) (Set.mem_Ici.2 le_rfl)
    (div_nonneg hx.le hy.le) (sub_nonneg.2 ((div_le_one hy).2 hxy)) (add_sub_cancel _ 1)
  simp only [smul_eq_mul, mul_zero, add_zero, Φ₀_zero, div_mul_cancel₀ x hy.ne'] at h
  -- `h : x / y * Φ₀ y ≤ Φ₀ x`
  show Φ₀ y / y ≤ Φ₀ x / x
  rw [div_le_div_iff₀ hy hx]
  calc Φ₀ y * x = x / y * Φ₀ y * y := by field_simp
    _ ≤ Φ₀ x * y := mul_le_mul_of_nonneg_right h hy.le

/-- `Φ₀(x) ≥ min{1, x/y} Φ₀(y)` for `x ≥ 0` and `y > 0` (both papers use it).

Proof (the dense paper's, in its proof of Theorem 1.3): `Φ₀` is increasing, while
`x ↦ Φ₀(x)/x` is decreasing. -/
theorem min_mul_Φ₀_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) : min 1 (x / y) * Φ₀ y ≤ Φ₀ x := by
  rcases le_total x y with hxy | hyx
  · rcases hx.eq_or_lt with rfl | hx'
    · simp
    -- `x ≤ y`: `Φ₀(x)/x ≥ Φ₀(y)/y`
    have h := antitoneOn_Φ₀_div (Set.mem_Ioi.2 hx') (Set.mem_Ioi.2 hy) hxy
    simp only at h
    calc min 1 (x / y) * Φ₀ y ≤ x / y * Φ₀ y :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (Φ₀_nonneg hy.le)
      _ = x * (Φ₀ y / y) := by ring
      _ ≤ x * (Φ₀ x / x) := mul_le_mul_of_nonneg_left h hx
      _ = Φ₀ x := by field_simp
  · -- `y ≤ x`: `Φ₀(x) ≥ Φ₀(y)`
    calc min 1 (x / y) * Φ₀ y ≤ 1 * Φ₀ y :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (Φ₀_nonneg hy.le)
      _ = Φ₀ y := one_mul _
      _ ≤ Φ₀ x := strictMono_Φ₀.monotone hyx

/-- `x ↦ x Φ₀(a / x)` is increasing on `(0, ∞)` for `a ≥ 0`.

Proof: for `a > 0`, `x Φ₀(a/x) = a · Φ₀(u)/u` with `u = a/x`, which decreases as `x` increases,
and `u ↦ Φ₀(u)/u` is decreasing (`antitoneOn_Φ₀_div`); for `a = 0` the function is `0`. -/
theorem monotoneOn_mul_Φ₀_div {a : ℝ} (ha : 0 ≤ a) :
    MonotoneOn (fun x => x * Φ₀ (a / x)) (Set.Ioi 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  simp only
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  have hu : 0 < a / y := div_pos ha' hy
  have huv : a / y ≤ a / x := div_le_div_of_nonneg_left ha'.le hx hxy
  have h := antitoneOn_Φ₀_div (Set.mem_Ioi.2 hu) (Set.mem_Ioi.2 (hu.trans_le huv)) huv
  simp only at h
  -- `h : Φ₀(a/x) / (a/x) ≤ Φ₀(a/y) / (a/y)`
  have e1 : x * Φ₀ (a / x) = a * (Φ₀ (a / x) / (a / x)) := by field_simp
  have e2 : y * Φ₀ (a / y) = a * (Φ₀ (a / y) / (a / y)) := by field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left h ha'.le

end PowerOfFew

end
