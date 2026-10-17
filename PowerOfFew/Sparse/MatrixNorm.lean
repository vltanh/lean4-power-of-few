module

public import PowerOfFew.Model.Gnp
public import External.FeigeOfek.FeigeOfek

/-!
# Sparse paper, Appendix A: the spectral norm of `A − E A`

Lemma A.7 of the sparse paper, proved by Feige and Ofek's argument
(`External.FeigeOfek.opNorm_adjMatrix_sub_le`, stated with Mathlib's binomial random graph,
adjacency matrix and operator norm, to which the paper's `gnpProb`, `adjMat`, `meanAdj` and
`specNorm` unfold). The paper derives it from two cited results instead (Theorem 3.2 of
Benaych-Georges–Bordenave–Knowles and Theorem 6.10 of Boucheron–Lugosi–Massart); that derivation is
formalized, with the two results as hypotheses, in `PowerOfFew/Sparse/MatrixNormDerivation.lean`
(`lemmaA_7_of_bbk_blm`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- **Lemma A.7** (`S:lem:matrix-norm-bound`). Let `c, a > 0` be constants and assume
`pn ≥ c log n`. With probability at least `1 − n^(−a)`, the adjacency matrix `A` of
`G ∼ G(n, p)` satisfies `‖A − E A‖_op ≤ C_{c,a} √(pn)`, for a constant `C_{c,a}` depending only
on `c` and `a`.

Departure from the paper (the whole argument, at the author's request): the paper derives the
bound from Theorem 3.2 of Benaych-Georges–Bordenave–Knowles (the expectation) and Theorem 6.10 of
Boucheron–Lugosi–Massart (Talagrand's concentration inequality); that derivation is
`lemmaA_7_of_bbk_blm`, with the two results as hypotheses. Their proofs need mathematics that Lean
lacks (a moment method for the non-backtracking matrix with an Ihara–Bass type formula; the entropy
method for separately convex Lipschitz functions), so the formalization proves the bound by Feige
and Ofek's argument (`External.FeigeOfek.opNorm_adjMatrix_sub_le`: a net of the unit ball, the
light pairs by an exponential-moment bound, the heavy pairs by bounded degrees and discrepancy, all
from Chernoff bounds). -/
theorem lemmaA_7 {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ∃ C : ℝ, ∀ (n : ℕ) (p : ℝ), 0 < p → p ≤ 1 → c * Real.log n ≤ p * n →
      1 - (n : ℝ) ^ (-a) ≤
        gnpProb n p (fun G => specNorm (adjMat G - meanAdj n p) ≤ C * Real.sqrt (p * n)) := by
  obtain ⟨C, hC⟩ := External.FeigeOfek.opNorm_adjMatrix_sub_le hc ha
  refine ⟨C, fun n p hp0 hp1 hpn => ?_⟩
  -- `adjMat G` is Mathlib's `G.adjMatrix ℝ`, for the classical decidability of adjacency.
  have hadj : ∀ G : SimpleGraph (Fin n), adjMat G = by classical exact G.adjMatrix ℝ :=
    fun G => rfl
  -- `gnpProb`, `toUnit`, `specNorm` and `meanAdj` unfold to the terms of the External statement.
  simpa only [gnpProb, toUnit, specNorm, meanAdj, hadj] using hC n p hp0 hp1 hpn

end PowerOfFew.Sparse

end
