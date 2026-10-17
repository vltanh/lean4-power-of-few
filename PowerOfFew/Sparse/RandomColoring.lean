module

public import PowerOfFew.Sparse.Main

/-!
# Sparse paper, Section 1.4: random initial colourings

* `theorem1_4`: a "delayed" version of the theorem of Fountoulakis, Kang and Makai: with a random
  balanced colouring and `p ≥ λ n^(−1/2)`, the larger side wins in `O(1)` days.
* `theorem1_5`: with a biased random colouring, Red wins with probability `1 − o(1)`. As printed,
  the bias condition `p_r = 1/2 + ω((pn)⁻¹)` is too weak when `p ≫ n^(−1/2)`
  (`theorem1_5_printed_false`): with `p = 1` and `p_r = 1/2 + (log n)/n`, Blue has the majority
  with probability tending to `1/2`. The corrected statement (agreed with the user) asks for
  `p_r = 1/2 + ω(max{(pn)⁻¹, n^(−1/2)})`, which is what the paper's proof uses ("with probability
  `1 − o(1)`, `|R| > |B|`").

Both theorems are unlabelled in the paper; the labels `S:thm:delayed-FKM` and
`S:thm:biased-coloring` are the formalization's.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

namespace PowerOfFew.Sparse

/-- **Theorem 1.4** (`S:thm:delayed-FKM`). For every fixed `ε > 0` there is a constant `λ > 0`
such that, for majority dynamics on `G(n, p)` with `p ≥ λ n^(−1/2)` and a random `1/2` initial
colouring, the larger side wins in `O(1)` days with probability at least `1 − ε`.

Reading: `p ≥ λ n^(−1/2)` is written `λ ≤ p √n`; "wins in `O(1)` days" means within `T` days for
some `T` depending on `ε`; a tie (no larger side) counts as a failure. -/
theorem theorem1_4 (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ T : ℕ, ∀ (n : ℕ) (p : ℝ), lam ≤ p * Real.sqrt n → p ≤ 1 →
      1 - ε ≤ coloredProb n p (1 / 2) (fun G B₀ =>
        ((B₀.ncard : ℝ) < n / 2 ∧ blueAfter G B₀ T = ∅) ∨
          ((n : ℝ) / 2 < B₀.ncard ∧ blueAfter G B₀ T = Set.univ)) := by
  sorry

/-- **Theorem 1.5** (`S:thm:biased-coloring`), corrected. On `G(n, p)` with
`p ≥ (1 + λ) n⁻¹ log n` for a constant `λ > 0`, majority dynamics from a random colouring in which
each vertex is Red with probability `p_r = 1/2 + ω(max{(pn)⁻¹, n^(−1/2)})` ends in a Red unanimity
with probability `1 − o(1)`.

Correction: the paper asks only for `p_r = 1/2 + ω((pn)⁻¹)`, which is false
(`theorem1_5_printed_false`). Here `p = p n` and `p_r = q n` are sequences. -/
theorem theorem1_5 (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10)
    {lam : ℝ} (hlam : 0 < lam) {p q : ℕ → ℝ} (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n ≤ 1)
    (hlog : ∀ n : ℕ, (1 + lam) * Real.log n / n ≤ p n) (hq : ∀ n, q n ≤ 1)
    (hbias : Tendsto (fun n : ℕ => (q n - 1 / 2) * min (p n * n) (Real.sqrt n)) atTop atTop) :
    Tendsto (fun n : ℕ =>
      coloredProb n (p n) (q n) (fun G B₀ => ∃ t, blueAfter G B₀ t = ∅)) atTop (𝓝 1) := by
  sorry

/-- Theorem 1.5 as printed (bias `ω((pn)⁻¹)`) is false: take `λ = 1`, `p = 1` and
`p_r = 1/2 + (log n)/n`. On the complete graph, if Blue has at least two more vertices than Red,
every vertex is Blue after one day; this happens with probability tending to `1/2`. -/
theorem theorem1_5_printed_false :
    ¬ ∀ (lam : ℝ), 0 < lam → ∀ (p q : ℕ → ℝ), (∀ n, 0 < p n) → (∀ n, p n ≤ 1) →
      (∀ n : ℕ, (1 + lam) * Real.log n / n ≤ p n) → (∀ n, q n ≤ 1) →
      Tendsto (fun n : ℕ => (q n - 1 / 2) * (p n * n)) atTop atTop →
      Tendsto (fun n : ℕ =>
        coloredProb n (p n) (q n) (fun G B₀ => ∃ t, blueAfter G B₀ t = ∅)) atTop (𝓝 1) := by
  sorry

end PowerOfFew.Sparse

end
