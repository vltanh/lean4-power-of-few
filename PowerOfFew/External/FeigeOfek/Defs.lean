module

public import PowerOfFew.Defs

/-!
# Feige and Ofek's bound on the spectral norm of a random graph: definitions

U. Feige and E. Ofek, *Spectral techniques applied to sparse random graphs*, Random Structures &
Algorithms 27 (2005) 251–275, Section 2, bound the spectral norm of `A − E A` for the adjacency
matrix `A` of `G(n, p)` with `pn ≥ c log n` by splitting the bilinear form `xᵀ (A − E A) y` on a net
of the unit ball into *light* pairs `(u, v)`, with `|xᵤ y_v| ≤ √d / n` (`d = pn`), and *heavy* pairs,
the others. The light pairs are handled by a Bernstein-type bound and a union bound over the net;
the heavy pairs by two properties of the graph: bounded degrees, and the *discrepancy property*
for the edge counts `e(S, T)`.

This file defines these quantities for a graph `G` on `Fin n`, with `adjMat G` as the adjacency
matrix. The proof follows the presentation of Chin, Rao and Vu (*Stochastic block model and
community detection in sparse graphs: a spectral algorithm with optimal rate of recovery*, COLT
2015, arXiv:1501.05021: Appendix A.1, and the appendix that proves their heavy-pair lemma), which
is Feige and Ofek's argument.
-/

@[expose] public section

noncomputable section

namespace PowerOfFew.FeigeOfek

/-- `e(S, T)`: the number of ordered pairs `(u, v) ∈ S × T` with `u ~ v`, as a real number (an edge
with both ends in `S ∩ T` counts twice). -/
def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n)) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ T, adjMat G u v

/-- Bounded degrees: every vertex has at most `c₁ d` neighbours. -/
def DegreeBound {n : ℕ} (G : SimpleGraph (Fin n)) (d c₁ : ℝ) : Prop :=
  ∀ u : Fin n, ∑ v, adjMat G u v ≤ c₁ * d

/-- The discrepancy property with constants `c₂, c₃` and expected degree `d`: for all sets `S, T`
of vertices, with `μ(S, T) = |S| |T| d / n` and `m = max(|S|, |T|)`, either `e(S, T) ≤ c₂ μ(S, T)` or
`e(S, T) log(e(S, T) / μ(S, T)) ≤ c₃ m log(n / m)`. -/
def Discrepancy {n : ℕ} (G : SimpleGraph (Fin n)) (d c₂ c₃ : ℝ) : Prop :=
  ∀ S T : Finset (Fin n),
    edgeCount G S T ≤ c₂ * (S.card * T.card * d / n) ∨
      edgeCount G S T * Real.log (edgeCount G S T / (S.card * T.card * d / n)) ≤
        c₃ * max (S.card : ℝ) T.card * Real.log (n / max (S.card : ℝ) T.card)

/-- The heavy pairs of `∑ |xᵤ| A_{uv} |y_v|`: the pairs with `|xᵤ y_v| > √d / n`. -/
def heavySum {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∑ u, ∑ v, if Real.sqrt d / n < |x u * y v| then |x u| * adjMat G u v * |y v| else 0

/-- The light pairs of `xᵀ (A − E A) y`, where `E A` has `p` off the diagonal and `0` on it: the
pairs `u ≠ v` with `|xᵤ y_v| ≤ √d / n`. -/
def lightSum {n : ℕ} (G : SimpleGraph (Fin n)) (p d : ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∑ u, ∑ v, if u ≠ v ∧ |x u * y v| ≤ Real.sqrt d / n then x u * (adjMat G u v - p) * y v else 0

end PowerOfFew.FeigeOfek
