module

public import Mathlib

/-!
# A grid net of the Euclidean unit ball

`gridNet n` is the set of points `z / (4√n)` with `z ∈ ℤⁿ` and `∑ zᵢ² ≤ 16 n`. It lies in the unit
ball of `ℝⁿ`, it has at most `(33 e)ⁿ` points, and every point `x` of the unit ball lies within
`1/4` of one of its points (round each coordinate of `4√n x` toward zero). Hence the operator norm of
a square matrix is at most twice the largest value of its bilinear form on the net.

Feige and Ofek bound the spectral norm of a random graph through such a net
(`PowerOfFew.FeigeOfek.feigeOfek`). The bound on the number of points is the exponential-moment
count `#{z : ∑ zᵢ² ≤ 16 n} ≤ e^(t · 16 n) (∑_{m ∈ ℤ} e^(−t m²))ⁿ` with `t = 1/16`, and
`∑_{m ∈ ℤ} e^(−m²/16) ≤ 1 + 2 / (e^(1/16) − 1) ≤ 33`.
-/

@[expose] public section

noncomputable section

/-- The grid net of the unit ball of `ℝⁿ`: the points `z / (4√n)` with `z ∈ ℤⁿ` and
`∑ zᵢ² ≤ 16 n` (the coordinates of such `z` lie in `[−4n, 4n]`). -/
def gridNet (n : ℕ) : Finset (Fin n → ℝ) := by
  classical
  exact ((Fintype.piFinset fun _ : Fin n => Finset.Icc (-(4 * n : ℤ)) (4 * n)).filter
      fun z => ∑ i, z i ^ 2 ≤ 16 * (n : ℤ)).image fun z i => (z i : ℝ) / (4 * Real.sqrt n)

/-- Every point of the net lies in the unit ball. -/
theorem sum_sq_le_one_of_mem_gridNet {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ gridNet n) :
    ∑ i, x i ^ 2 ≤ 1 := by
  sorry

/-- The net has at most `(33 e)ⁿ` points. -/
theorem card_gridNet_le (n : ℕ) : ((gridNet n).card : ℝ) ≤ (33 * Real.exp 1) ^ n := by
  sorry

/-- The operator norm of a square matrix is at most twice the largest value of its bilinear form
on the net. -/
theorem Matrix.norm_toEuclideanCLM_le_of_gridNet {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) {B : ℝ}
    (h : ∀ x ∈ gridNet n, ∀ y ∈ gridNet n, |∑ u, ∑ v, x u * W u v * y v| ≤ B) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) W‖ ≤ 2 * B := by
  sorry

end
