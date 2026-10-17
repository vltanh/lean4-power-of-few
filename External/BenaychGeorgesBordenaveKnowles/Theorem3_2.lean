module

public import Mathlib

/-!
# Benaych-Georges, Bordenave and Knowles, Theorem 3.2 (stated, not proved)

F. Benaych-Georges, C. Bordenave, A. Knowles, *Spectral radii of sparse random matrices*, Ann.
Inst. H. Poincaré Probab. Statist. 56 (2020), arXiv:1704.02945, Theorem 3.2, for the
inhomogeneous Erdős–Rényi graph. It is stated here in the homogeneous case `p_ij = p` (`i ≠ j`),
which is the case the sparse paper uses, with Mathlib's binomial random graph and adjacency matrix.

The sparse paper uses it in its proof of Lemma A.7. The formalization proves Lemma A.7 by Feige and
Ofek's argument instead (`External.FeigeOfek`), so this proposition is a hypothesis only of the
paper's own derivation, `PowerOfFew.Sparse.lemmaA_7_of_bbk_blm`.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace External.BenaychGeorgesBordenaveKnowles

open Classical in
/-- **Theorem 3.2** for `G(n, p)`: there is a universal constant `C > 0` such that, with
`d = p(n − 1)` (the maximal expected degree), `κ = p / (d / n)`, `q = √d ∧ n^(1/10) κ^(−1/9)` and
`η = √(log n) / q`, if `q ≥ 1` then `E‖A − E A‖ / √d ≤ 2 + C η / √(1 ∨ log η)`, where `A` is the
adjacency matrix of `G(n, p)`, `E A` has `p` off the diagonal and `0` on it, and `‖·‖` is the
operator norm on `ℓ²`. -/
def theorem3_2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (p : ℝ), 0 < p → p ≤ 1 →
    let d : ℝ := p * (n - 1)
    let κ : ℝ := p / (d / n)
    let q : ℝ := min (Real.sqrt d) ((n : ℝ) ^ (1 / 10 : ℝ) * κ ^ (-(1 / 9 : ℝ)))
    let η : ℝ := Real.sqrt (Real.log n) / q
    1 ≤ q →
      (∫ G, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)
            (G.adjMatrix ℝ - Matrix.of fun u v => if u = v then 0 else p)‖
          ∂(SimpleGraph.binomialRandom (Fin n) (Set.projIcc 0 1 zero_le_one p))) /
          Real.sqrt d ≤
        2 + C * η / Real.sqrt (max 1 (Real.log η))

end External.BenaychGeorgesBordenaveKnowles

end
