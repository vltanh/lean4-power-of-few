module

public import PowerOfFew.External.FeigeOfek.Heavy
public import PowerOfFew.External.FeigeOfek.Properties
public import PowerOfFew.External.FeigeOfek.Light

/-!
# Feige and Ofek's bound on the spectral norm of `G(n, p)`

U. Feige and E. Ofek, *Spectral techniques applied to sparse random graphs*, Random Structures &
Algorithms 27 (2005) 251–275, Section 2: for `pn ≥ c log n`, the adjacency matrix `A` of `G(n, p)`
satisfies `‖A − E A‖ = O(√(pn))` with high probability. The proof:

* the operator norm is at most twice the largest value of `xᵀ (A − E A) y` over the grid net
  (`Matrix.norm_toEuclideanCLM_le_of_gridNet`);
* `xᵀ (A − E A) y` is the sum of its light part (`lightSum`) and its heavy part; the light part is
  at most `21 √(pn)` for all points of the net at once, except with probability `2e^(−n)`
  (`lightSum_le`);
* the heavy part is at most `heavySum G (pn) x y + p ∑_{heavy} |xᵤ y_v|`, and
  `p ∑_{heavy} |xᵤ y_v| ≤ p (n / √(pn)) ∑ xᵤ² y_v² ≤ √(pn)`; on the event of bounded degrees and
  discrepancy (`exists_degreeBound_discrepancy`), `heavySum ≤ K √(pn)` (`heavySum_le`);
* for `n` below a threshold `N`, `‖A − E A‖ ≤ ‖A − E A‖_F ≤ n < N ≤ (N / √(c log 2)) √(pn)`
  (and `n ≤ 1` is trivial).

The sparse paper's Lemma A.7 has exactly this statement; the formalization proves it from this
theorem (`PowerOfFew.Sparse.lemmaA_7`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.FeigeOfek

/-- **Feige–Ofek (2005)**: for all `c, a > 0` there is a constant `C` such that, whenever
`pn ≥ c log n`, the adjacency matrix `A` of `G ∼ G(n, p)` satisfies `‖A − E A‖_op ≤ C √(pn)` with
probability at least `1 − n^(−a)`. -/
theorem feigeOfek {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ∃ C : ℝ, ∀ (n : ℕ) (p : ℝ), 0 < p → p ≤ 1 → c * Real.log n ≤ p * n →
      1 - (n : ℝ) ^ (-a) ≤
        gnpProb n p (fun G => specNorm (adjMat G - meanAdj n p) ≤ C * Real.sqrt (p * n)) := by
  sorry

end PowerOfFew.FeigeOfek
