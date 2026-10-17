module

public import PowerOfFew.Model.Gnp

/-!
# Sparse paper, Appendix A: the spectral norm of `A − E A`

Lemma A.7 of the sparse paper, derived as the paper does from two cited results that the
formalization assumes: Theorem 3.2 of Benaych-Georges–Bordenave–Knowles for the expectation
(`BBKTheorem3_2`) and Theorem 6.10 of Boucheron–Lugosi–Massart for the concentration
(`BLMTheorem6_10`).

Reading: the paper quotes the first with `d = p(1 − p)(n − 1)` and `η = √(log n)/min{√d, n^0.1}`;
the cited theorem has `d = p(n − 1)` (the maximal expected degree) and
`q = √d ∧ n^(1/10) κ^(-1/9)`, `κ = n/(n − 1)`. The difference only changes constants.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- **Lemma A.7** (`S:lem:matrix-norm-bound`). Let `c, a > 0` be constants and assume
`pn ≥ c log n`. With probability at least `1 − n^(−a)`, the adjacency matrix `A` of
`G ∼ G(n, p)` satisfies `‖A − E A‖_op ≤ C_{c,a} √(pn)`, for a constant `C_{c,a}` depending only
on `c` and `a`. -/
theorem lemmaA_7 (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10) {c a : ℝ} (hc : 0 < c)
    (ha : 0 < a) :
    ∃ C : ℝ, ∀ (n : ℕ) (p : ℝ), 0 < p → p ≤ 1 → c * Real.log n ≤ p * n →
      1 - (n : ℝ) ^ (-a) ≤
        gnpProb n p (fun G => specNorm (adjMat G - meanAdj n p) ≤ C * Real.sqrt (p * n)) := by
  sorry

end PowerOfFew.Sparse

end
