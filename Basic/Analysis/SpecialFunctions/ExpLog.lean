module

public import Mathlib

/-!
# Two elementary estimates for the exponential and the logarithm

* `Real.log_natCast_le_two_mul_sqrt`: `log n ≤ 2 √n` for natural numbers `n`.
* `Real.mul_exp_neg_div_le`: `x e^(−x/a) ≤ 2a²/x` for `a, x > 0`.
-/

@[expose] public section

namespace Real

/-- `log n ≤ 2 √n` for natural numbers `n`, from `log y ≤ y − 1` at `y = √n`. -/
theorem log_natCast_le_two_mul_sqrt (n : ℕ) : log n ≤ 2 * √n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := log_le_sub_one_of_pos (sqrt_pos.mpr hn')
  rw [log_sqrt hn'.le] at h1
  linarith

/-- `x e^(−x/a) ≤ 2a²/x` for `a, x > 0`, from `e^y ≥ 1 + y + y²/2 ≥ y²/2` at `y = x/a`. -/
theorem mul_exp_neg_div_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    x * exp (-(x / a)) ≤ 2 * a ^ 2 / x := by
  have hy : 0 ≤ x / a := (div_pos hx ha).le
  have hE : (x / a) ^ 2 / 2 ≤ exp (x / a) := by
    have := quadratic_le_exp_of_nonneg hy
    nlinarith
  have hexp : 0 < exp (x / a) := exp_pos _
  rw [exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hexp hx]
  have hxa : (x / a) ^ 2 * a ^ 2 = x ^ 2 := by field_simp
  nlinarith [hE, sq_nonneg a]

end Real
