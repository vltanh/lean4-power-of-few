module

public import PowerOfFew.Model.Gnp
public import PowerOfFew.Model.Majority

/-!
# Conditioning on edges of `G(n, p)`

The tools of the papers' "Day One" arguments (dense paper, Claims 2.5 and 2.6; sparse paper,
Proposition 2.2):

* `nbrCount_graphOfEdges`: the number of neighbours of `v` in `S` is the sum of the indicators of
  the edges `vu`, `u ∈ S \ {v}`; these indicators form a Bernoulli family
  (`isBernoulliFamily_edgesAt`), so neighbour counts in disjoint sets are independent binomials;
* `dependsOn_mem_majorityStep`: whether `v` is Blue the next day depends only on the edges at `v`;
* `integral_mul_of_dependsOn_disjoint`: functions of disjoint sets of edges are independent;
* `edgeCondExp`, `integral_eq_edgeCondExp`: expectations with one edge variable fixed, and the law
  of total expectation over that edge;
* `covariance_shared_edge`: if `f` and `g` depend on disjoint sets of edges plus one common edge
  `e`, then `Cov(f, g) = p(1 − p)(a_f − b_f)(a_g − b_g)`, where `a` and `b` are the expectations
  with `e` present and absent (the dense paper's equation (2.3); the sparse paper's covariance
  identity in the proof of Proposition 2.2).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew

variable {n : ℕ} {p : ℝ}

/-- The pairs `{v, u}`, `u ≠ v`: the possible edges at `v`. -/
def edgesAt (v : Fin n) : Set (Sym2 (Fin n)) := {e | ∃ u, u ≠ v ∧ e = s(v, u)}

/-- The expectation of `f` under `G(n, p)` with the edge variable `e` set to `b`. -/
def edgeCondExp (n : ℕ) (p : ℝ) (e : Sym2 (Fin n)) (b : Prop) (f : EdgeVars n → ℝ) : ℝ :=
  ∫ ω, f (Function.update ω e b) ∂(edgeLaw n p)

open Classical in
/-- The number of neighbours of `v` in `S` is the sum of the indicators of the edges `vu`,
`u ∈ S \ {v}`. -/
theorem nbrCount_graphOfEdges (ω : EdgeVars n) (S : Set (Fin n)) (v : Fin n) :
    (nbrCount (graphOfEdges ω) S v : ℝ) =
      ∑ u ∈ Finset.univ.filter (fun u => u ∈ S ∧ u ≠ v), edgeInd s(v, u) ω := by
  sorry

/-- The indicators of the edges at `v` form a Bernoulli(`p`) family. -/
theorem isBernoulliFamily_edgesAt (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : Fin n) :
    IsBernoulliFamily (edgeLaw n p) p (fun u : {u : Fin n // u ≠ v} => edgeInd s(v, u.1)) := by
  sorry

/-- Whether `v` is Blue the next day depends only on the edges at `v`. -/
theorem dependsOn_mem_majorityStep (B : Set (Fin n)) (v : Fin n) :
    DependsOn (fun ω : EdgeVars n => v ∈ majorityStep (graphOfEdges ω) B) (edgesAt v) := by
  sorry

theorem edgesAt_inter_edgesAt {v w : Fin n} (hvw : v ≠ w) :
    edgesAt v ∩ edgesAt w = {s(v, w)} := by
  sorry

/-- Bounded functions of disjoint sets of edge variables are independent. -/
theorem integral_mul_of_dependsOn_disjoint {f g : EdgeVars n → ℝ} {s t : Set (Sym2 (Fin n))}
    (hf : DependsOn f s) (hg : DependsOn g t) (hst : Disjoint s t) {C : ℝ}
    (hfC : ∀ ω, |f ω| ≤ C) (hgC : ∀ ω, |g ω| ≤ C) :
    ∫ ω, f ω * g ω ∂(edgeLaw n p) = (∫ ω, f ω ∂(edgeLaw n p)) * ∫ ω, g ω ∂(edgeLaw n p) := by
  sorry

/-- The law of total expectation over one edge variable. -/
theorem integral_eq_edgeCondExp (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {e : Sym2 (Fin n)} (he : ¬ e.IsDiag)
    {f : EdgeVars n → ℝ} {C : ℝ} (hfC : ∀ ω, |f ω| ≤ C) :
    ∫ ω, f ω ∂(edgeLaw n p) = p * edgeCondExp n p e True f + (1 - p) * edgeCondExp n p e False f := by
  sorry

/-- **The covariance of two functions sharing one edge.** If `f` depends only on the edges in
`s ∪ {e}` and `g` only on those in `t ∪ {e}`, with `s`, `t` disjoint and `e ∉ s ∪ t`, then
`Cov(f, g) = p(1 − p)(a_f − b_f)(a_g − b_g)`, where `a` and `b` are the expectations with the edge
`e` present and absent. -/
theorem covariance_shared_edge (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {e : Sym2 (Fin n)} (he : ¬ e.IsDiag)
    {f g : EdgeVars n → ℝ} {s t : Set (Sym2 (Fin n))} (hf : DependsOn f (insert e s))
    (hg : DependsOn g (insert e t)) (hst : Disjoint s t) (hes : e ∉ s) (het : e ∉ t) {C : ℝ}
    (hfC : ∀ ω, |f ω| ≤ C) (hgC : ∀ ω, |g ω| ≤ C) :
    ∫ ω, f ω * g ω ∂(edgeLaw n p) - (∫ ω, f ω ∂(edgeLaw n p)) * ∫ ω, g ω ∂(edgeLaw n p) =
      p * (1 - p) * (edgeCondExp n p e True f - edgeCondExp n p e False f) *
        (edgeCondExp n p e True g - edgeCondExp n p e False g) := by
  sorry

end PowerOfFew

end
