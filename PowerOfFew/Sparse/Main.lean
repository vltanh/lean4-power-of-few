module

public import PowerOfFew.Sparse.DayOne
public import PowerOfFew.Sparse.DayTwo
public import PowerOfFew.Sparse.DayThree

/-!
# Sparse paper: Theorem 1.2, the power of few for sparse graphs

Reading of the asymptotic notation: `λ > 0` is a constant, and the constants hidden in `O(·)` (the
time bound and the failure probability) may depend on it, as they do in the paper's proof
(Lemmas 2.6 and A.4 take `n` large in terms of `λ`). `Δ = n/2 − |B₀|`, so that `|R₀| = n/2 + Δ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- **Theorem 1.2** (`S:thm:main-nonlazy`, the power of few for sparse graphs). Consider a set
`V` of `n` vertices with a partition `V = R ∪ B`, `|R| = n/2 + Δ`, and draw `G ∼ G(n, p)` on `V`.
If `n − 10 ≥ pn ≥ (1 + λ) log n` and `pΔ ≥ 10`, where `λ > 0` is a constant, then majority
dynamics on `G` from `(R, B)` reaches a Red unanimity within time `O(log_{pn} n)` with probability
at least `1 − O(1 / min{n, pΔ²} + n^(−λ/2))`. -/
theorem theorem1_2 (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10)
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ C K : ℝ, ∀ (n : ℕ) (p : ℝ) (B₀ : Set (Fin n)), 0 < p →
      p * n ≤ (n : ℝ) - 10 → (1 + lam) * Real.log n ≤ p * n →
      10 ≤ p * ((n : ℝ) / 2 - B₀.ncard) →
      1 - C * (1 / min (n : ℝ) (p * ((n : ℝ) / 2 - B₀.ncard) ^ 2) + (n : ℝ) ^ (-(lam / 2))) ≤
        gnpProb n p (fun G => ∃ t : ℕ,
          (t : ℝ) ≤ K * (Real.log n / Real.log (p * n)) ∧ blueAfter G B₀ t = ∅) := by
  sorry

end PowerOfFew.Sparse

end
