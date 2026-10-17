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

/-- `Φ` is the distribution function of the standard Gaussian law. -/
theorem Φ_eq_cdf_gaussianReal (a : ℝ) :
    Φ a = ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) a := by
  sorry

@[simp] theorem Φ₀_zero : Φ₀ 0 = 0 := by
  sorry

theorem Φ₀_neg (a : ℝ) : Φ₀ (-a) = -Φ₀ a := by
  sorry

theorem hasDerivAt_Φ₀ (a : ℝ) :
    HasDerivAt Φ₀ ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-a ^ 2 / 2)) a := by
  sorry

theorem continuous_Φ₀ : Continuous Φ₀ := by
  sorry

theorem strictMono_Φ₀ : StrictMono Φ₀ := by
  sorry

theorem Φ₀_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ Φ₀ a := by
  sorry

theorem Φ₀_lt_half (a : ℝ) : Φ₀ a < 1 / 2 := by
  sorry

theorem neg_half_lt_Φ₀ (a : ℝ) : -(1 / 2) < Φ₀ a := by
  sorry

theorem Φ₀_le_div {a : ℝ} (ha : 0 ≤ a) : Φ₀ a ≤ a / Real.sqrt (2 * Real.pi) := by
  sorry

theorem Φ₀_sub_le {a b : ℝ} (hab : a ≤ b) : Φ₀ b - Φ₀ a ≤ (b - a) / Real.sqrt (2 * Real.pi) := by
  sorry

theorem concaveOn_Φ₀ : ConcaveOn ℝ (Set.Ici 0) Φ₀ := by
  sorry

/-- `Φ₀(x) ≥ min{1, x/y} Φ₀(y)` for `x ≥ 0` and `y > 0` (both papers use it). -/
theorem min_mul_Φ₀_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) : min 1 (x / y) * Φ₀ y ≤ Φ₀ x := by
  sorry

/-- `x ↦ x Φ₀(a / x)` is increasing on `(0, ∞)` for `a ≥ 0`. -/
theorem monotoneOn_mul_Φ₀_div {a : ℝ} (ha : 0 ≤ a) :
    MonotoneOn (fun x => x * Φ₀ (a / x)) (Set.Ioi 0) := by
  sorry

end PowerOfFew

end
