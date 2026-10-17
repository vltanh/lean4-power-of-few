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
  sorry

theorem measurableSet_simpleGraph (S : Set (SimpleGraph (Fin n))) : MeasurableSet S := by
  sorry

theorem measurableSet_edgeVars (S : Set (EdgeVars n)) : MeasurableSet S := by
  sorry

theorem measurable_graphOfEdges : Measurable (graphOfEdges (n := n)) := by
  sorry

/-- Mathlib's `G(n, p)` is the image of `edgeLaw n p` under `graphOfEdges`. -/
theorem binomialRandom_eq_map_edgeLaw (n : ℕ) (p : ℝ) :
    SimpleGraph.binomialRandom (Fin n) (toUnit p) = (edgeLaw n p).map graphOfEdges := by
  sorry

theorem gnpProb_eq (n : ℕ) (p : ℝ) (P : SimpleGraph (Fin n) → Prop) :
    gnpProb n p P = (edgeLaw n p).real {ω | P (graphOfEdges ω)} := by
  sorry

theorem gnpExp_eq (n : ℕ) (p : ℝ) (f : SimpleGraph (Fin n) → ℝ) :
    gnpExp n p f = ∫ ω, f (graphOfEdges ω) ∂(edgeLaw n p) := by
  sorry

theorem gnpVar_eq (n : ℕ) (p : ℝ) (f : SimpleGraph (Fin n) → ℝ) :
    gnpVar n p f = variance (fun ω => f (graphOfEdges ω)) (edgeLaw n p) := by
  sorry

theorem adj_graphOfEdges {ω : EdgeVars n} {u v : Fin n} :
    (graphOfEdges ω).Adj u v ↔ u ≠ v ∧ ω s(u, v) := by
  sorry

theorem measurable_edgeInd (e : Sym2 (Fin n)) : Measurable (edgeInd (n := n) e) := by
  sorry

/-- The edge indicators are independent under `edgeLaw`. -/
theorem iIndepFun_edgeInd (n : ℕ) (p : ℝ) :
    iIndepFun (fun e : Sym2 (Fin n) => edgeInd e) (edgeLaw n p) := by
  sorry

/-- The indicators of the pairs of distinct vertices form a Bernoulli(`p`) family. -/
theorem isBernoulliFamily_edgeInd (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsBernoulliFamily (edgeLaw n p) p (fun e : OffDiag n => edgeInd e.1) := by
  sorry

/-- On the diagonal, the edge variable is almost surely false. -/
theorem ae_not_diag {e : Sym2 (Fin n)} (he : e.IsDiag) : ∀ᵐ ω ∂(edgeLaw n p), ¬ ω e := by
  sorry

/-! ### Rules for `gnpProb` -/

theorem gnpProb_nonneg (P : SimpleGraph (Fin n) → Prop) : 0 ≤ gnpProb n p P := by
  sorry

theorem gnpProb_le_one (P : SimpleGraph (Fin n) → Prop) : gnpProb n p P ≤ 1 := by
  sorry

theorem gnpProb_true : gnpProb n p (fun _ => True) = 1 := by
  sorry

theorem gnpProb_mono {P Q : SimpleGraph (Fin n) → Prop} (h : ∀ G, P G → Q G) :
    gnpProb n p P ≤ gnpProb n p Q := by
  sorry

theorem gnpProb_not (P : SimpleGraph (Fin n) → Prop) :
    gnpProb n p (fun G => ¬ P G) = 1 - gnpProb n p P := by
  sorry

theorem gnpProb_or_le (P Q : SimpleGraph (Fin n) → Prop) :
    gnpProb n p (fun G => P G ∨ Q G) ≤ gnpProb n p P + gnpProb n p Q := by
  sorry

theorem gnpProb_and_ge (P Q : SimpleGraph (Fin n) → Prop) :
    gnpProb n p P + gnpProb n p Q - 1 ≤ gnpProb n p (fun G => P G ∧ Q G) := by
  sorry

/-- The union bound over a finite family. -/
theorem gnpProb_exists_le {ι : Type*} (s : Finset ι) (P : ι → SimpleGraph (Fin n) → Prop) :
    gnpProb n p (fun G => ∃ i ∈ s, P i G) ≤ ∑ i ∈ s, gnpProb n p (P i) := by
  sorry

/-- A random graph has property `P` with probability `1 - x` or more when the complement has
probability at most `x`. -/
theorem le_gnpProb_of_not_le {P : SimpleGraph (Fin n) → Prop} {x : ℝ}
    (h : gnpProb n p (fun G => ¬ P G) ≤ x) : 1 - x ≤ gnpProb n p P := by
  sorry

/-! ### Random initial colourings -/

/-- Under `coloredGnp`, the colouring is independent of the graph: the probability of an event is
the average over the colourings of its probability under `G(n, p)`. -/
theorem coloredProb_eq_sum (n : ℕ) (p q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (P : SimpleGraph (Fin n) → Set (Fin n) → Prop) :
    coloredProb n p q P =
      ∑ χ : Fin n → Bool,
        (∏ v, if χ v then q else 1 - q) * gnpProb n p (fun G => P G {v | χ v = false}) := by
  sorry

end PowerOfFew

end
