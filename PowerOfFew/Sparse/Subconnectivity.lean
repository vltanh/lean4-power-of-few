module

public import PowerOfFew.Sparse.Main
public import PowerOfFew.External.GolesOlivos.GolesOlivos

/-!
# Sparse paper, Section 3: below the connectivity threshold

Theorem 3.1 of the sparse paper: for `p = (1 − λ) n⁻¹ log n`, the process becomes periodic, and
the Blue camp ends with at most `(log n)^(O_λ(√(log n))) n^λ` vertices, of average degree
`O_λ(√(pn))`.

Reading: the constants hidden in `O(·)` and `O_λ(·)` may depend on `λ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- **Theorem 3.1** (`S:thm:subcon-main`). Let `0 < λ < 1` and consider majority dynamics on
`G(n, p)` with `p = (1 − λ) n⁻¹ log n` and an initial gap `Δ` (`|R₀| = n/2 + Δ`) with `pΔ ≥ 10`.
With probability at least `1 − O(1/min{n, pΔ²} + n^(−(1−λ)))` there is a day `t*` such that
`B_t = B_{t*}` or `B_t = B_{t*+1}` for all `t ≥ t*`,
`|B_{t*+1}| ≤ |B_{t*}| ≤ (log n)^(O_λ(log^(1/2) n)) n^λ`, and the average degree of the vertices of
`B_{t*}` is `O_λ(√(pn))`. -/
theorem theorem3_1 (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ C K : ℝ, ∀ (n : ℕ) (B₀ : Set (Fin n)),
      10 ≤ (1 - lam) * Real.log n / n * ((n : ℝ) / 2 - B₀.ncard) →
      1 - C * (1 / min (n : ℝ) ((1 - lam) * Real.log n / n * ((n : ℝ) / 2 - B₀.ncard) ^ 2) +
          (n : ℝ) ^ (-(1 - lam))) ≤
        gnpProb n ((1 - lam) * Real.log n / n) (fun G => ∃ t₀ : ℕ,
          (∀ t ≥ t₀, blueAfter G B₀ t = blueAfter G B₀ t₀ ∨
            blueAfter G B₀ t = blueAfter G B₀ (t₀ + 1)) ∧
          (blueAfter G B₀ (t₀ + 1)).ncard ≤ (blueAfter G B₀ t₀).ncard ∧
          ((blueAfter G B₀ t₀).ncard : ℝ) ≤
            Real.log n ^ (K * Real.sqrt (Real.log n)) * (n : ℝ) ^ lam ∧
          ∑ᶠ v ∈ blueAfter G B₀ t₀, (degree G v : ℝ) ≤
            K * Real.sqrt ((1 - lam) * Real.log n) * (blueAfter G B₀ t₀).ncard) := by
  sorry

end PowerOfFew.Sparse

end
