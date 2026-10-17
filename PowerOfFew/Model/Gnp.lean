module

public import PowerOfFew.Defs
public import Basic.Probability.Combinatorics.BinomialRandomGraph.EdgeVariables

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

-- The edge variables of `G(n, p)` and their law, from `Basic` (where they are in the namespace
-- `SimpleGraph`), under the names this library uses.
export SimpleGraph (EdgeVars OffDiag edgeLaw graphOfEdges edgeInd measurableSet_edgeVars
  measurable_graphOfEdges adj_graphOfEdges measurable_edgeInd iIndepFun_edgeInd
  isBernoulliFamily_edgeInd)

/-- The expectation of a real function of `G ∼ G(n, p)`. -/
def gnpExp (n : ℕ) (p : ℝ) (f : SimpleGraph (Fin n) → ℝ) : ℝ :=
  ∫ G, f G ∂(SimpleGraph.binomialRandom (Fin n) (toUnit p))

/-- The variance of a real function of `G ∼ G(n, p)`. -/
def gnpVar (n : ℕ) (p : ℝ) (f : SimpleGraph (Fin n) → ℝ) : ℝ :=
  variance f (SimpleGraph.binomialRandom (Fin n) (toUnit p))

theorem toUnit_coe {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : (toUnit p : ℝ) = p := by
  rw [toUnit, Set.projIcc_of_mem _ ⟨hp0, hp1⟩]

theorem measurableSet_simpleGraph (S : Set (SimpleGraph (Fin n))) : MeasurableSet S :=
  SimpleGraph.measurableSet_of_fin S

/-- Mathlib's `G(n, p)` is the image of `edgeLaw n p` under `graphOfEdges`. -/
theorem binomialRandom_eq_map_edgeLaw (n : ℕ) (p : ℝ) :
    SimpleGraph.binomialRandom (Fin n) (toUnit p) = (edgeLaw n p).map graphOfEdges :=
  SimpleGraph.binomialRandom_eq_map_edgeLaw n p

theorem gnpProb_eq (n : ℕ) (p : ℝ) (P : SimpleGraph (Fin n) → Prop) :
    gnpProb n p P = (edgeLaw n p).real {ω | P (graphOfEdges ω)} := by
  rw [gnpProb, binomialRandom_eq_map_edgeLaw,
    map_measureReal_apply measurable_graphOfEdges (measurableSet_simpleGraph _)]
  rfl

theorem gnpExp_eq (n : ℕ) (p : ℝ) (f : SimpleGraph (Fin n) → ℝ) :
    gnpExp n p f = ∫ ω, f (graphOfEdges ω) ∂(edgeLaw n p) := by
  rw [gnpExp, binomialRandom_eq_map_edgeLaw,
    integral_map measurable_graphOfEdges.aemeasurable
      (SimpleGraph.measurable_of_fin f).aestronglyMeasurable]

theorem gnpVar_eq (n : ℕ) (p : ℝ) (f : SimpleGraph (Fin n) → ℝ) :
    gnpVar n p f = variance (fun ω => f (graphOfEdges ω)) (edgeLaw n p) := by
  rw [gnpVar, binomialRandom_eq_map_edgeLaw,
    variance_map (SimpleGraph.measurable_of_fin f).aemeasurable
      measurable_graphOfEdges.aemeasurable]
  rfl


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
  have := SimpleGraph.measurableSingletonClass_fin (n := n)
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
