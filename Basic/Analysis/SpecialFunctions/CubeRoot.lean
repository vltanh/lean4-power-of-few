module

public import Mathlib

/-!
# An inequality between `b^(1/3)(1 − b)^(2/3)` and a polynomial

`one_sub_two_mul_sq_div_three_le`: for `0 ≤ b ≤ 1/2`,
`(1 − 2b)² / 3 ≤ 1 − b/2 − (3/2) b^(1/3) (1 − b)^(2/3)`.

This is the "routine Taylor expansion around 1/2" in the proof of the sparse paper's Lemma 2.4.
The paper expands only near `b = 1/2`, where the two sides agree to second order (their
difference is `(1 − 2b)³/27 + O((1 − 2b)⁴)`). With `x = (b / (1 − b))^(1/3)` the inequality is
equivalent to `(1 − x)³ (4 + 3x − 3x² − x³) ≥ 0` on `[0, 1]`.
-/

@[expose] public section

namespace Real

/-- The polynomial form of `one_sub_two_mul_sq_div_three_le`: if `0 ≤ s ≤ t` and `s³ + t³ = 1`,
then `(1 − 2s³)² / 3 ≤ 1 − s³/2 − (3/2) s t²`. Homogenising with `s³ + t³ = 1`, six times the
difference of the two sides is `(t − s)³ (4t³ + 3st² − 3s²t − s³)` (that is, `t⁶ P(s/t)` with
`P(x) = x⁶ − 9x⁴ + 13x³ − 9x + 4 = (1 − x)³ (4 + 3x − 3x² − x³)`), and the second factor is at
least `3t³ ≥ 0`. -/
private lemma one_sub_two_mul_cube_sq_div_three_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (h : s ^ 3 + t ^ 3 = 1) :
    (1 - 2 * s ^ 3) ^ 2 / 3 ≤ 1 - s ^ 3 / 2 - 3 / 2 * s * t ^ 2 := by
  have key : 1 - s ^ 3 / 2 - 3 / 2 * s * t ^ 2 - (1 - 2 * s ^ 3) ^ 2 / 3
      = (t - s) ^ 3 * (4 * t ^ 3 + 3 * s * t ^ 2 - 3 * s ^ 2 * t - s ^ 3) / 6 := by
    linear_combination (-(2 / 3 + 3 / 2 * s ^ 3 + 2 / 3 * t ^ 3 - 3 / 2 * s * t ^ 2)) * h
  have ht : 0 ≤ t := hs.trans hst
  have h1 : 0 ≤ (t - s) ^ 3 := pow_nonneg (sub_nonneg.2 hst) 3
  -- `4t³ + 3st² − 3s²t − s³ = 3t³ + (t³ − s³) + 3st(t − s) ≥ 0`
  have h2 : 0 ≤ 4 * t ^ 3 + 3 * s * t ^ 2 - 3 * s ^ 2 * t - s ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg hs ht) (sub_nonneg.2 hst), pow_le_pow_left₀ hs hst 3,
      pow_nonneg ht 3]
  have := div_nonneg (mul_nonneg h1 h2) (by norm_num : (0 : ℝ) ≤ 6)
  linarith

/-- For `0 ≤ b ≤ 1/2`: `(1 − 2b)² / 3 ≤ 1 − b/2 − (3/2) b^(1/3) (1 − b)^(2/3)`.

Departure from the paper: the sparse paper (proof of Lemma 2.4) obtains this by "a routine Taylor
expansion around 1/2", which only gives the inequality for `b` close to `1/2`; the statement here
holds on all of `[0, 1/2]`, so we prove it exactly instead. With `s = b^(1/3)` and
`t = (1 − b)^(1/3)` we have `s³ + t³ = 1` and `0 ≤ s ≤ t`, and the inequality becomes the
polynomial inequality `one_sub_two_mul_cube_sq_div_three_le`. -/
theorem one_sub_two_mul_sq_div_three_le {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2) :
    (1 - 2 * b) ^ 2 / 3 ≤ 1 - b / 2 - 3 / 2 * b ^ (1 / 3 : ℝ) * (1 - b) ^ (2 / 3 : ℝ) := by
  have h1b : 0 ≤ 1 - b := by linarith
  have hs3 : (b ^ (1 / 3 : ℝ)) ^ 3 = b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0]; norm_num
  have ht3 : ((1 - b) ^ (1 / 3 : ℝ)) ^ 3 = 1 - b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h1b]; norm_num
  have ht2 : (1 - b) ^ (2 / 3 : ℝ) = ((1 - b) ^ (1 / 3 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h1b]; norm_num
  have hst : b ^ (1 / 3 : ℝ) ≤ (1 - b) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow hb0 (by linarith) (by norm_num)
  have h := one_sub_two_mul_cube_sq_div_three_le (Real.rpow_nonneg hb0 _) hst
    (by rw [hs3, ht3]; ring)
  rw [hs3] at h
  rw [ht2]
  exact h

end Real
