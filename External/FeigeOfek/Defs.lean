module

public import Basic.Probability.Combinatorics.BinomialRandomGraph.EdgeVariables

/-!
# Feige and Ofek's bound on the spectral norm of a random graph: definitions

U. Feige and E. Ofek, *Spectral techniques applied to sparse random graphs*, Random Structures &
Algorithms 27 (2005) 251–275, Section 2, bound the second eigenvalue of `G(n, p)` with
`pn ≥ c log n` through the bilinear form `xᵀ A y` on a net of the unit ball, for `x ⊥ 1`, split into
*light* pairs `(u, v)`, with `|xᵤ y_v| ≤ √d / n` (`d = pn`), and *heavy* pairs, the others. Chin, Rao
and Vu run the same argument on the centred form `xᵀ (A − E A) y`, which bounds `‖A − E A‖`; this is
the form formalized here. The light pairs are handled by a Bernstein-type bound and a union bound over the net;
the heavy pairs by two properties of the graph: bounded degrees, and the *discrepancy property*
for the edge counts `e(S, T)`.

This file defines these quantities for a graph `G` on `Fin n`, with Mathlib's adjacency matrix
`G.adjMatrix ℝ` (for the classical decidability of adjacency) as `A`. It also defines the
probability `prob n p P` that `G(n, p)`, Mathlib's `SimpleGraph.binomialRandom (Fin n)` with `p`
clamped into `[0, 1]`, has the property `P`, with the rules the proof uses: the transfer to the
independent edge variables of `SimpleGraph.edgeLaw` (`prob_eq`), complements, monotonicity and
union bounds. The proof follows the presentation of Chin, Rao and Vu (*Stochastic block model and
community detection in sparse graphs: a spectral algorithm with optimal rate of recovery*, COLT
2015, arXiv:1501.05021: Appendix A.1, and the appendix that proves their heavy-pair lemma), which
is Feige and Ofek's argument.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace External.FeigeOfek

/-! ### The random graph `G(n, p)` -/

/-- The probability that the binomial random graph `G(n, p)` on `Fin n` has the property `P`. The
law is Mathlib's `SimpleGraph.binomialRandom (Fin n)`, with `p` clamped into `[0, 1]`: each pair of
distinct vertices is an edge with probability `p`, independently of the other pairs. -/
def prob (n : ℕ) (p : ℝ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  (SimpleGraph.binomialRandom (Fin n) (Set.projIcc 0 1 zero_le_one p)).real {G | P G}

section Rules

variable {n : ℕ} {p : ℝ}

/-- A probability under `G(n, p)` is a probability under the independent edge variables. -/
theorem prob_eq (n : ℕ) (p : ℝ) (P : SimpleGraph (Fin n) → Prop) :
    prob n p P = (SimpleGraph.edgeLaw n p).real {ω | P (SimpleGraph.graphOfEdges ω)} := by
  rw [prob, SimpleGraph.binomialRandom_eq_map_edgeLaw,
    map_measureReal_apply SimpleGraph.measurable_graphOfEdges
      (SimpleGraph.measurableSet_of_fin _)]
  rfl

theorem prob_nonneg (P : SimpleGraph (Fin n) → Prop) : 0 ≤ prob n p P :=
  measureReal_nonneg

theorem prob_true : prob n p (fun _ => True) = 1 := by
  simp [prob]

theorem prob_mono {P Q : SimpleGraph (Fin n) → Prop} (h : ∀ G, P G → Q G) :
    prob n p P ≤ prob n p Q :=
  measureReal_mono fun G hG => h G hG

theorem prob_not (P : SimpleGraph (Fin n) → Prop) :
    prob n p (fun G => ¬ P G) = 1 - prob n p P :=
  probReal_compl_eq_one_sub (SimpleGraph.measurableSet_of_fin {G | P G})

theorem prob_or_le (P Q : SimpleGraph (Fin n) → Prop) :
    prob n p (fun G => P G ∨ Q G) ≤ prob n p P + prob n p Q :=
  measureReal_union_le {G | P G} {G | Q G}

/-- The union bound over a finite family. -/
theorem prob_exists_le {ι : Type*} (s : Finset ι) (P : ι → SimpleGraph (Fin n) → Prop) :
    prob n p (fun G => ∃ i ∈ s, P i G) ≤ ∑ i ∈ s, prob n p (P i) := by
  unfold prob
  have h : {G | ∃ i ∈ s, P i G} = ⋃ i ∈ s, {G | P i G} := by
    ext G
    simp
  rw [h]
  exact measureReal_biUnion_finset_le _ _

/-- A random graph has property `P` with probability `1 - x` or more when the complement has
probability at most `x`. -/
theorem le_prob_of_not_le {P : SimpleGraph (Fin n) → Prop} {x : ℝ}
    (h : prob n p (fun G => ¬ P G) ≤ x) : 1 - x ≤ prob n p P := by
  rw [prob_not] at h
  linarith

end Rules

/-! ### Edge counts, bounded degrees, discrepancy, light and heavy pairs -/

open Classical in
/-- `e(S, T)`: the number of ordered pairs `(u, v) ∈ S × T` with `u ~ v`, as a real number (an edge
with both ends in `S ∩ T` counts twice). -/
def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n)) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ T, G.adjMatrix ℝ u v

open Classical in
/-- Bounded degrees: every vertex has at most `c₁ d` neighbours. -/
def DegreeBound {n : ℕ} (G : SimpleGraph (Fin n)) (d c₁ : ℝ) : Prop :=
  ∀ u : Fin n, ∑ v, G.adjMatrix ℝ u v ≤ c₁ * d

/-- The discrepancy property with constants `c₂, c₃` and expected degree `d`: for all sets `S, T`
of vertices, with `μ(S, T) = |S| |T| d / n` and `m = max(|S|, |T|)`, either `e(S, T) ≤ c₂ μ(S, T)` or
`e(S, T) log(e(S, T) / μ(S, T)) ≤ c₃ m log(n / m)`. -/
def Discrepancy {n : ℕ} (G : SimpleGraph (Fin n)) (d c₂ c₃ : ℝ) : Prop :=
  ∀ S T : Finset (Fin n),
    edgeCount G S T ≤ c₂ * (S.card * T.card * d / n) ∨
      edgeCount G S T * Real.log (edgeCount G S T / (S.card * T.card * d / n)) ≤
        c₃ * max (S.card : ℝ) T.card * Real.log (n / max (S.card : ℝ) T.card)

open Classical in
/-- The heavy pairs of `∑ |xᵤ| A_{uv} |y_v|`: the pairs with `|xᵤ y_v| > √d / n`. -/
def heavySum {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∑ u, ∑ v, if Real.sqrt d / n < |x u * y v| then |x u| * G.adjMatrix ℝ u v * |y v| else 0

open Classical in
/-- The light pairs of `xᵀ (A − E A) y`, where `E A` has `p` off the diagonal and `0` on it: the
pairs `u ≠ v` with `|xᵤ y_v| ≤ √d / n`. -/
def lightSum {n : ℕ} (G : SimpleGraph (Fin n)) (p d : ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∑ u, ∑ v, if u ≠ v ∧ |x u * y v| ≤ Real.sqrt d / n then
    x u * (G.adjMatrix ℝ u v - p) * y v else 0

end External.FeigeOfek
