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

/-- For `0 ≤ b ≤ 1/2`: `(1 − 2b)² / 3 ≤ 1 − b/2 − (3/2) b^(1/3) (1 − b)^(2/3)`. -/
theorem one_sub_two_mul_sq_div_three_le {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2) :
    (1 - 2 * b) ^ 2 / 3 ≤ 1 - b / 2 - 3 / 2 * b ^ (1 / 3 : ℝ) * (1 - b) ^ (2 / 3 : ℝ) := by
  sorry

end Real
