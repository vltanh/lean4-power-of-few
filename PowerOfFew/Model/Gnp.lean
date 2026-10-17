module

public import PowerOfFew.Defs
public import Basic.Probability.BernoulliFamily

/-!
# The random graph `G(n, p)` as independent edge indicators

Mathlib defines `G(n, p)` (`SimpleGraph.binomialRandom`) as the image of a product of Bernoulli
laws, one for each unordered pair `e : Sym2 (Fin n)` (identically `False` on the diagonal). This
file works with that product directly (`edgeLaw`), where the edge indicators are independent by
`ProbabilityTheory.iIndepFun_pi`, and transfers probabilities and expectations along
`graphOfEdges` (`binomialRandom_eq_map_edgeLaw`, `gnpProb_eq`, `gnpExp_eq`).

It also collects the elementary rules for `gnpProb`: complements, monotonicity, union bounds.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew

variable {n : ℕ} {p : ℝ}

/-- The edge variables: one proposition for each unordered pair of vertices. -/
abbrev EdgeVars (n : ℕ) : Type := Sym2 (Fin n) → Prop

/-- The unordered pairs of distinct vertices. -/
abbrev OffDiag (n : ℕ) : Type := {e : Sym2 (Fin n) // ¬ e.IsDiag}

/-- The product law of the edge variables of `G(n, p)`, as in Mathlib's construction of
`SimpleGraph.binomialRandom`: Bernoulli(`p`) on each pair of distinct vertices, `False` on the
diagonal. -/
def edgeLaw (n : ℕ) (p : ℝ) : Measure (EdgeVars n) :=
  Measure.pi fun e : Sym2 (Fin n) => bernoulliMeasure (¬ e.IsDiag) False (toUnit p)

instance : IsProbabilityMeasure (edgeLaw n p) := by
  unfold edgeLaw; infer_instance

/-- The graph whose edges are the pairs whose edge variable holds. -/
def graphOfEdges (ω : EdgeVars n) : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet {e | ω e}

/-- The indicator of the edge variable `e`, as a real random variable. -/
def edgeInd (e : Sym2 (Fin n)) (ω : EdgeVars n) : ℝ := by
  classical exact if ω e then 1 else 0

/-- The expectation of a real function of `G ∼ G(n, p)`. -/
def gnpExp (n : ℕ) (p : ℝ) (f : SimpleGraph (Fin n) → ℝ) : ℝ :=
  ∫ G, f G ∂(SimpleGraph.binomialRandom (Fin n) (toUnit p))

/-- The variance of a real function of `G ∼ G(n, p)`. -/
def gnpVar (n : ℕ) (p : ℝ) (f : SimpleGraph (Fin n) → ℝ) : ℝ :=
  variance f (SimpleGraph.binomialRandom (Fin n) (toUnit p))

theorem toUnit_coe {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : (toUnit p : ℝ) = p := by
  rw [toUnit, Set.projIcc_of_mem _ ⟨hp0, hp1⟩]

/-- Singletons of `SimpleGraph (Fin n)` are measurable for Mathlib's σ-algebra `comap Adj`. -/
private lemma gnpAux_measurableSingletonClass_simpleGraph :
    MeasurableSingletonClass (SimpleGraph (Fin n)) := by
  refine ⟨fun G => ?_⟩
  have h : ({G} : Set (SimpleGraph (Fin n))) = SimpleGraph.Adj ⁻¹' {G.Adj} := by
    ext H
    simp [SimpleGraph.adj_inj]
  rw [h]
  exact SimpleGraph.measurable_adj (measurableSet_singleton _)

theorem measurableSet_simpleGraph (S : Set (SimpleGraph (Fin n))) : MeasurableSet S := by
  have := gnpAux_measurableSingletonClass_simpleGraph (n := n)
  exact S.to_countable.measurableSet

theorem measurableSet_edgeVars (S : Set (EdgeVars n)) : MeasurableSet S :=
  S.to_countable.measurableSet

/-- Every function of a graph on `Fin n` is measurable. -/
private lemma gnpAux_measurable_of_simpleGraph {β : Type*} [MeasurableSpace β]
    (f : SimpleGraph (Fin n) → β) : Measurable f :=
  fun _ _ => measurableSet_simpleGraph _

/-- Every function of the edge variables is measurable. -/
private lemma gnpAux_measurable_of_edgeVars {β : Type*} [MeasurableSpace β]
    (f : EdgeVars n → β) : Measurable f :=
  fun _ _ => measurableSet_edgeVars _

theorem measurable_graphOfEdges : Measurable (graphOfEdges (n := n)) :=
  gnpAux_measurable_of_edgeVars _

/-- Mathlib's `G(n, p)` is the image of `edgeLaw n p` under `graphOfEdges`. -/
theorem binomialRandom_eq_map_edgeLaw (n : ℕ) (p : ℝ) :
    SimpleGraph.binomialRandom (Fin n) (toUnit p) = (edgeLaw n p).map graphOfEdges := by
  rw [SimpleGraph.binomialRandom_eq_map, setBernoulli_eq_map,
    Measure.map_map SimpleGraph.measurable_fromEdgeSet measurable_setOfPred,
    Measure.infinitePi_eq_pi]
  rfl

theorem gnpProb_eq (n : ℕ) (p : ℝ) (P : SimpleGraph (Fin n) → Prop) :
    gnpProb n p P = (edgeLaw n p).real {ω | P (graphOfEdges ω)} := by
  rw [gnpProb, binomialRandom_eq_map_edgeLaw,
    map_measureReal_apply measurable_graphOfEdges (measurableSet_simpleGraph _)]
  rfl

theorem gnpExp_eq (n : ℕ) (p : ℝ) (f : SimpleGraph (Fin n) → ℝ) :
    gnpExp n p f = ∫ ω, f (graphOfEdges ω) ∂(edgeLaw n p) := by
  rw [gnpExp, binomialRandom_eq_map_edgeLaw,
    integral_map measurable_graphOfEdges.aemeasurable
      (gnpAux_measurable_of_simpleGraph f).aestronglyMeasurable]

theorem gnpVar_eq (n : ℕ) (p : ℝ) (f : SimpleGraph (Fin n) → ℝ) :
    gnpVar n p f = variance (fun ω => f (graphOfEdges ω)) (edgeLaw n p) := by
  rw [gnpVar, binomialRandom_eq_map_edgeLaw,
    variance_map (gnpAux_measurable_of_simpleGraph f).aemeasurable
      measurable_graphOfEdges.aemeasurable]
  rfl

theorem adj_graphOfEdges {ω : EdgeVars n} {u v : Fin n} :
    (graphOfEdges ω).Adj u v ↔ u ≠ v ∧ ω s(u, v) := by
  simp [graphOfEdges, SimpleGraph.fromEdgeSet_adj, and_comm]

theorem measurable_edgeInd (e : Sym2 (Fin n)) : Measurable (edgeInd (n := n) e) :=
  gnpAux_measurable_of_edgeVars _

/-- The edge indicators are independent under `edgeLaw`. -/
theorem iIndepFun_edgeInd (n : ℕ) (p : ℝ) :
    iIndepFun (fun e : Sym2 (Fin n) => edgeInd e) (edgeLaw n p) := by
  classical
  exact iIndepFun_pi
    (μ := fun e : Sym2 (Fin n) => bernoulliMeasure (¬ e.IsDiag) False (toUnit p))
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
      (fun e : Sym2 (Fin n) => bernoulliMeasure (¬ e.IsDiag) False (toUnit p)) e.1).map_eq
    rw [h1, edgeLaw, ← map_measureReal_apply (measurable_pi_apply _) (measurableSet_singleton _),
      h2]
    have h3 : (¬ e.1.IsDiag) = True := eq_true e.2
    simp only [h3]
    rw [bernoulliMeasure_real_apply_of_mem_of_notMem _ (measurableSet_singleton _) rfl (by simp),
      toUnit_coe hp0 hp1]

/-- On the diagonal, the edge variable is almost surely false. -/
theorem ae_not_diag {e : Sym2 (Fin n)} (he : e.IsDiag) : ∀ᵐ ω ∂(edgeLaw n p), ¬ ω e := by
  have h : ∀ᵐ b ∂(bernoulliMeasure (¬ e.IsDiag) False (toUnit p)), ¬ b := by
    have h2 : (¬ e.IsDiag) = False := eq_false (not_not.2 he)
    rw [h2, bernoulliMeasure_self_eq_dirac]
    simp
  have h2 := (measurePreserving_eval
    (fun e : Sym2 (Fin n) => bernoulliMeasure (¬ e.IsDiag) False (toUnit p)) e).map_eq
  rw [← h2] at h
  exact ae_of_ae_map (measurable_pi_apply e).aemeasurable h

/-! ### Rules for `gnpProb` -/

theorem gnpProb_nonneg (P : SimpleGraph (Fin n) → Prop) : 0 ≤ gnpProb n p P :=
  measureReal_nonneg

theorem gnpProb_le_one (P : SimpleGraph (Fin n) → Prop) : gnpProb n p P ≤ 1 :=
  measureReal_le_one

theorem gnpProb_true : gnpProb n p (fun _ => True) = 1 := by
  simp [gnpProb]

theorem gnpProb_mono {P Q : SimpleGraph (Fin n) → Prop} (h : ∀ G, P G → Q G) :
    gnpProb n p P ≤ gnpProb n p Q :=
  measureReal_mono fun G hG => h G hG

theorem gnpProb_not (P : SimpleGraph (Fin n) → Prop) :
    gnpProb n p (fun G => ¬ P G) = 1 - gnpProb n p P :=
  probReal_compl_eq_one_sub (measurableSet_simpleGraph {G | P G})

theorem gnpProb_or_le (P Q : SimpleGraph (Fin n) → Prop) :
    gnpProb n p (fun G => P G ∨ Q G) ≤ gnpProb n p P + gnpProb n p Q :=
  measureReal_union_le {G | P G} {G | Q G}

theorem gnpProb_and_ge (P Q : SimpleGraph (Fin n) → Prop) :
    gnpProb n p P + gnpProb n p Q - 1 ≤ gnpProb n p (fun G => P G ∧ Q G) := by
  have h := measureReal_union_add_inter (μ := SimpleGraph.binomialRandom (Fin n) (toUnit p))
    (s := {G | P G}) (measurableSet_simpleGraph {G | Q G})
  have h1 : gnpProb n p (fun G => P G ∨ Q G) ≤ 1 := gnpProb_le_one _
  change _ ≤ (SimpleGraph.binomialRandom (Fin n) (toUnit p)).real ({G | P G} ∩ {G | Q G})
  change (SimpleGraph.binomialRandom (Fin n) (toUnit p)).real ({G | P G} ∪ {G | Q G}) ≤ 1 at h1
  unfold gnpProb
  linarith

/-- The union bound over a finite family. -/
theorem gnpProb_exists_le {ι : Type*} (s : Finset ι) (P : ι → SimpleGraph (Fin n) → Prop) :
    gnpProb n p (fun G => ∃ i ∈ s, P i G) ≤ ∑ i ∈ s, gnpProb n p (P i) := by
  unfold gnpProb
  have h : {G | ∃ i ∈ s, P i G} = ⋃ i ∈ s, {G | P i G} := by
    ext G
    simp
  rw [h]
  exact measureReal_biUnion_finset_le _ _

/-- A random graph has property `P` with probability `1 - x` or more when the complement has
probability at most `x`. -/
theorem le_gnpProb_of_not_le {P : SimpleGraph (Fin n) → Prop} {x : ℝ}
    (h : gnpProb n p (fun G => ¬ P G) ≤ x) : 1 - x ≤ gnpProb n p P := by
  rw [gnpProb_not] at h
  linarith

/-! ### Random initial colourings -/

/-- Under `coloredGnp`, the colouring is independent of the graph: the probability of an event is
the average over the colourings of its probability under `G(n, p)`. -/
theorem coloredProb_eq_sum (n : ℕ) (p q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (P : SimpleGraph (Fin n) → Set (Fin n) → Prop) :
    coloredProb n p q P =
      ∑ χ : Fin n → Bool,
        (∏ v, if χ v then q else 1 - q) * gnpProb n p (fun G => P G {v | χ v = false}) := by
  have := gnpAux_measurableSingletonClass_simpleGraph (n := n)
  have hS : MeasurableSet
      {x : SimpleGraph (Fin n) × (Fin n → Bool) | P x.1 {v | x.2 v = false}} :=
    (Set.to_countable _).measurableSet
  have hν : ∀ χ : Fin n → Bool,
      (Measure.pi fun _ : Fin n => bernoulliMeasure true false (toUnit q)).real {χ} =
        ∏ v, if χ v then q else 1 - q := by
    intro χ
    rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← measureReal_def]
    cases χ v
    · simp [toUnit_coe hq0 hq1]
    · simp [toUnit_coe hq0 hq1]
  rw [coloredProb, coloredGnp, measureReal_def, Measure.prod_apply_symm hS, lintegral_fintype,
    ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun χ _ => ?_
    rw [ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def, hν, mul_comm]
    rfl
  · intro χ _
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

end PowerOfFew

end
