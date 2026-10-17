module

public import PowerOfFew.Sparse.Degrees
public import PowerOfFew.Sparse.MatrixNorm

/-!
# Sparse paper, Section 2.4: Step 3, the third day onwards

Lemma 2.5 (deterministic, spectral) and Lemma 2.6 of the sparse paper. Lemma 2.6 uses the spectral
bound of Lemma A.7, hence the assumed results `BBKTheorem3_2` and `BLMTheorem6_10`, and the minimum
degree bound of Lemma A.4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- The all-ones `n × n` matrix `𝟏𝟏ᵀ`. -/
def onesMat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun _ _ => 1

/-- **Lemma 2.5** (`S:lem:hypo-blue-bound-2`). For any Blue set `B_t` and any
`1/2 > b ≥ |B_t| / n`, either `B_{t+1} = ∅` or
`|B_{t+1}| (avg_{v ∈ B_{t+1}} d(v))² ≤ inf_x ‖A_G − x 𝟏𝟏ᵀ‖²_op (1 − b)/(1/2 − b)² |B_t|`. -/
theorem lemma2_5 {n : ℕ} (G : SimpleGraph (Fin n)) (B : Set (Fin n)) {b : ℝ} (hb : b < 1 / 2)
    (hBb : (B.ncard : ℝ) ≤ b * n) :
    majorityStep G B = ∅ ∨
      (∑ᶠ v ∈ majorityStep G B, (degree G v : ℝ)) ^ 2 / (majorityStep G B).ncard ≤
        (⨅ x : ℝ, specNorm (adjMat G - x • onesMat n) ^ 2) * ((1 - b) / (1 / 2 - b) ^ 2) *
          B.ncard := by
  sorry

/-- **Lemma 2.6** (`S:lem:step3`). Consider majority dynamics on `G ∼ G(n, p)` with
`pn ≥ (1 + λ) log n`, and assume `|B₂| ≤ b n` for a constant `b < 1/2`. Then with probability at
least `1 − 2 n^(−λ/2)` there is a time `t* = O(log_{pn} n)` with `B_{t*} = ∅`.

Reading: the event is that of the proof: the graph empties every Blue set of at most `b n`
vertices within `K log n / log(pn)` days; `K` and the threshold `N` for `n` depend on `λ` and `b`
(the proof takes `n` large enough). -/
theorem lemma2_6 (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10) {lam b : ℝ} (hlam : 0 < lam)
    (hb0 : 0 ≤ b) (hb : b < 1 / 2) :
    ∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ p : ℝ, 0 < p → p ≤ 1 → (1 + lam) * Real.log n ≤ p * n →
      1 - 2 * (n : ℝ) ^ (-(lam / 2)) ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
        (B.ncard : ℝ) ≤ b * n →
          ∃ t : ℕ, (t : ℝ) ≤ K * (Real.log n / Real.log (p * n)) ∧ blueAfter G B t = ∅) := by
  sorry

end PowerOfFew.Sparse

end
