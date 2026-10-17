module

public import Basic.Probability.BernoulliFamily

/-!
# The binomial random graph as independent edge variables

Mathlib defines the binomial random graph `G(n, p)` (`SimpleGraph.binomialRandom`) as the image of
a product of Bernoulli laws, one for each unordered pair `e : Sym2 (Fin n)` (identically `False` on
the diagonal). This file works with that product directly (`SimpleGraph.edgeLaw`), where the edge
indicators are independent by `ProbabilityTheory.iIndepFun_pi`, and identifies `G(n, p)` with its
image under `SimpleGraph.graphOfEdges` (`SimpleGraph.binomialRandom_eq_map_edgeLaw`). The edge
indicators of the pairs of distinct vertices form a Bernoulli family
(`SimpleGraph.isBernoulliFamily_edgeInd`). The parameter `p` is a real number, clamped into the
unit interval.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace SimpleGraph

variable {n : ℕ} {p : ℝ}

/-- The clamped parameter is `p` itself when `0 ≤ p ≤ 1`. -/
theorem projIcc_coe {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (Set.projIcc (0 : ℝ) 1 zero_le_one p : ℝ) = p := by
  rw [Set.projIcc_of_mem _ ⟨hp0, hp1⟩]

/-- The edge variables: one proposition for each unordered pair of vertices. -/
abbrev EdgeVars (n : ℕ) : Type := Sym2 (Fin n) → Prop

/-- The unordered pairs of distinct vertices. -/
abbrev OffDiag (n : ℕ) : Type := {e : Sym2 (Fin n) // ¬ e.IsDiag}

/-- The product law of the edge variables of `G(n, p)`, as in Mathlib's construction of
`binomialRandom`: Bernoulli(`p`) on each pair of distinct vertices, `False` on the
diagonal. -/
def edgeLaw (n : ℕ) (p : ℝ) : Measure (EdgeVars n) :=
  Measure.pi fun e : Sym2 (Fin n) =>
    bernoulliMeasure (¬ e.IsDiag) False (Set.projIcc (0 : ℝ) 1 zero_le_one p)

instance : IsProbabilityMeasure (edgeLaw n p) := by
  unfold edgeLaw; infer_instance

/-- The graph whose edges are the pairs whose edge variable holds. -/
def graphOfEdges (ω : EdgeVars n) : SimpleGraph (Fin n) := fromEdgeSet {e | ω e}

/-- The indicator of the edge variable `e`, as a real random variable. -/
def edgeInd (e : Sym2 (Fin n)) (ω : EdgeVars n) : ℝ := by
  classical exact if ω e then 1 else 0

/-- Singletons of `SimpleGraph (Fin n)` are measurable for Mathlib's σ-algebra `comap Adj`. -/
theorem measurableSingletonClass_fin :
    MeasurableSingletonClass (SimpleGraph (Fin n)) := by
  refine ⟨fun G => ?_⟩
  have h : ({G} : Set (SimpleGraph (Fin n))) = SimpleGraph.Adj ⁻¹' {G.Adj} := by
    ext H
    simp [SimpleGraph.adj_inj]
  rw [h]
  exact SimpleGraph.measurable_adj (measurableSet_singleton _)

theorem measurableSet_of_fin (S : Set (SimpleGraph (Fin n))) : MeasurableSet S := by
  have := measurableSingletonClass_fin (n := n)
  exact S.to_countable.measurableSet

theorem measurableSet_edgeVars (S : Set (EdgeVars n)) : MeasurableSet S :=
  S.to_countable.measurableSet

/-- Every function of a graph on `Fin n` is measurable. -/
theorem measurable_of_fin {β : Type*} [MeasurableSpace β]
    (f : SimpleGraph (Fin n) → β) : Measurable f :=
  fun _ _ => measurableSet_of_fin _

/-- Every function of the edge variables is measurable. -/
theorem measurable_of_edgeVars {β : Type*} [MeasurableSpace β]
    (f : EdgeVars n → β) : Measurable f :=
  fun _ _ => measurableSet_edgeVars _

theorem measurable_graphOfEdges : Measurable (graphOfEdges (n := n)) :=
  measurable_of_edgeVars _

/-- Mathlib's `G(n, p)` is the image of `edgeLaw n p` under `graphOfEdges`. -/
theorem binomialRandom_eq_map_edgeLaw (n : ℕ) (p : ℝ) :
    binomialRandom (Fin n) (Set.projIcc (0 : ℝ) 1 zero_le_one p) =
      (edgeLaw n p).map graphOfEdges := by
  rw [binomialRandom_eq_map, setBernoulli_eq_map,
    Measure.map_map measurable_fromEdgeSet measurable_setOfPred,
    Measure.infinitePi_eq_pi]
  rfl

theorem adj_graphOfEdges {ω : EdgeVars n} {u v : Fin n} :
    (graphOfEdges ω).Adj u v ↔ u ≠ v ∧ ω s(u, v) := by
  simp [graphOfEdges, fromEdgeSet_adj, and_comm]

theorem measurable_edgeInd (e : Sym2 (Fin n)) : Measurable (edgeInd (n := n) e) :=
  measurable_of_edgeVars _

/-- The edge indicators are independent under `edgeLaw`. -/
theorem iIndepFun_edgeInd (n : ℕ) (p : ℝ) :
    iIndepFun (fun e : Sym2 (Fin n) => edgeInd e) (edgeLaw n p) := by
  classical
  exact iIndepFun_pi
    (μ := fun e : Sym2 (Fin n) =>
      bernoulliMeasure (¬ e.IsDiag) False (Set.projIcc (0 : ℝ) 1 zero_le_one p))
    (X := fun _ (b : Prop) => if b then (1 : ℝ) else 0)
    (fun _ => Measurable.of_discrete.aemeasurable)

/-- The indicators of the pairs of distinct vertices form a Bernoulli(`p`) family. -/
theorem isBernoulliFamily_edgeInd (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsBernoulliFamily (edgeLaw n p) p (fun e : OffDiag n => edgeInd e.1) := by
  refine ⟨fun e => measurable_edgeInd e.1,
    (iIndepFun_edgeInd n p).precomp Subtype.val_injective, fun e ω => ?_, fun e => ?_⟩
  · unfold edgeInd
    split_ifs <;> simp
  · have h1 : {ω : EdgeVars n | edgeInd e.1 ω = 1} =
        (Function.eval e.1 : EdgeVars n → Prop) ⁻¹' ({True} : Set Prop) := by
      ext ω
      simp [edgeInd]
    have h2 := (measurePreserving_eval
      (fun e : Sym2 (Fin n) =>
        bernoulliMeasure (¬ e.IsDiag) False (Set.projIcc (0 : ℝ) 1 zero_le_one p)) e.1).map_eq
    rw [h1, edgeLaw, ← map_measureReal_apply (measurable_pi_apply _) (measurableSet_singleton _),
      h2]
    have h3 : (¬ e.1.IsDiag) = True := eq_true e.2
    simp only [h3]
    rw [bernoulliMeasure_real_apply_of_mem_of_notMem _ (measurableSet_singleton _) rfl (by simp),
      projIcc_coe hp0 hp1]

/-- On the diagonal, the edge variable is almost surely false. -/
theorem ae_not_diag_edgeLaw {e : Sym2 (Fin n)} (he : e.IsDiag) :
    ∀ᵐ ω ∂(edgeLaw n p), ¬ ω e := by
  have h : ∀ᵐ b ∂(bernoulliMeasure (¬ e.IsDiag) False (Set.projIcc (0 : ℝ) 1 zero_le_one p)),
      ¬ b := by
    have h2 : (¬ e.IsDiag) = False := eq_false (not_not.2 he)
    rw [h2, bernoulliMeasure_self_eq_dirac]
    simp
  have h2 := (measurePreserving_eval
    (fun e : Sym2 (Fin n) =>
      bernoulliMeasure (¬ e.IsDiag) False (Set.projIcc (0 : ℝ) 1 zero_le_one p)) e).map_eq
  rw [← h2] at h
  exact ae_of_ae_map (measurable_pi_apply e).aemeasurable h

end SimpleGraph

end
