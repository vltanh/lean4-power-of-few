module

public import PowerOfFew.Sparse.Main
public import PowerOfFew.Sparse.BerryEsseen

/-!
# Dense paper: Theorem 1.5 and Appendix A

The dense paper states its Theorem 1.5 (the power of few above the connectivity threshold) without
proof, for its "upcoming paper" (the sparse paper), and in Appendix A derives from it a delayed
version of the theorem of Fountoulakis, Kang and Makai (its Theorem 1.4, cited for context only).

Here Theorem 1.5 is proved from the sparse paper's Theorem 1.2 (and a direct argument when
`p > 1 − 10/n`, a case that Theorem 1.2 excludes), and Appendix A follows the dense paper's
argument from Theorem 1.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Dense

/-- **Theorem 1.5** (`D:thm:general-sparse`). For any `0 < ε ≤ 1` and `λ > 0` there is
`c = c(ε, λ)` such that, for `p ≥ (1 + λ)(log n)/n`, if Red starts with `n/2 + c/p` members then it
wins with probability at least `1 − ε`.

Reading: "starts with `n/2 + c/p` members" is read as "at least", and "wins" as "is unanimous at
some day". -/
theorem theorem1_5 (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {lam : ℝ} (hlam : 0 < lam) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (p : ℝ), 0 < p → p ≤ 1 → (1 + lam) * Real.log n / n ≤ p →
      ∀ B₀ : Set (Fin n), (B₀.ncard : ℝ) ≤ n / 2 - c / p →
        1 - ε ≤ gnpProb n p (fun G => ∃ t, blueAfter G B₀ t = ∅) := by
  sorry

/-- **Appendix A** (`D:appx:FKM-proof`): the dense paper's proof of a delayed version of the
theorem of Fountoulakis, Kang and Makai (Theorem 1.4) from Theorem 1.5. For any `0 < ε ≤ 1` there
is `λ` such that, for `p ≥ λ n^(−1/2)`, with probability at least `1 − ε` over the random graph
`G(n, p)` and the random `1/2` initial colouring, the dominating colour wins.

Reading: the appendix proves that the dominating colour wins, without the four-day bound of
Theorem 1.4 ("a delayed version", Section 1.4); `p ≥ λ n^(−1/2)` is written `λ ≤ p √n`; a tie
counts as a failure. -/
theorem appendixA (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ (n : ℕ) (p : ℝ), lam ≤ p * Real.sqrt n → p ≤ 1 →
      1 - ε ≤ coloredProb n p (1 / 2) (fun G B₀ =>
        ((B₀.ncard : ℝ) < n / 2 ∧ ∃ t, blueAfter G B₀ t = ∅) ∨
          ((n : ℝ) / 2 < B₀.ncard ∧ ∃ t, blueAfter G B₀ t = Set.univ)) := by
  sorry

end PowerOfFew.Dense

end
