module

public import PowerOfFew.External.FeigeOfek.Defs
public import PowerOfFew.External.FeigeOfek.SixCases

/-!
# Feige and Ofek's bound for the heavy pairs

If every degree of `G` is at most `c₁ d` and `G` has the discrepancy property with constants
`c₂, c₃`, then for all `x, y` in the unit ball the heavy pairs (`|xᵤ y_v| > √d / n`) contribute
`∑ |xᵤ| A_{uv} |y_v| ≤ 2 (24 + 8 c₁ + 16 c₂ + 64 c₃) √d` (Feige–Ofek 2005, Section 2.2; Chin–Rao–Vu
2015, their heavy-pair lemma). The proof groups the coordinates into dyadic blocks
`S_i = {u : xᵤ ≠ 0, 2^(i−1) < √n |xᵤ| ≤ 2^i}` (the integer `i` is `Int.clog 2 (√n |xᵤ|)`) and `T_j`
for `y`, bounds the heavy pairs by `∑_{2^(i+j) > √d} e(S_i, T_j) 2^(i+j) / n`, and applies the six
cases (`sum_blocks_le`).
-/

@[expose] public section

noncomputable section

namespace PowerOfFew.FeigeOfek

/-- **Feige–Ofek, the heavy pairs.** If every degree is at most `c₁ d` and the discrepancy property
holds with `c₂ ≥ e` and `c₃ ≥ 0`, then for all `x, y` with `∑ xᵤ² ≤ 1` and `∑ y_v² ≤ 1`,
`∑_{|xᵤ y_v| > √d/n} |xᵤ| A_{uv} |y_v| ≤ 2 (24 + 8 c₁ + 16 c₂ + 64 c₃) √d`. -/
theorem heavySum_le {n : ℕ} (G : SimpleGraph (Fin n)) {d c₁ c₂ c₃ : ℝ} (hd : 0 < d)
    (hc₁ : 0 ≤ c₁) (hc₂ : Real.exp 1 ≤ c₂) (hc₃ : 0 ≤ c₃) (hdeg : DegreeBound G d c₁)
    (hdisc : Discrepancy G d c₂ c₃) (x y : Fin n → ℝ) (hx : ∑ u, x u ^ 2 ≤ 1)
    (hy : ∑ v, y v ^ 2 ≤ 1) :
    heavySum G d x y ≤ 2 * (24 + 8 * c₁ + 16 * c₂ + 64 * c₃) * Real.sqrt d := by
  sorry

end PowerOfFew.FeigeOfek
