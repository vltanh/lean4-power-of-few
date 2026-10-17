module

public import PowerOfFew.Defs

/-!
# The two results on random matrices that the sparse paper cites for Lemma A.7

The sparse paper bounds `‖A − E A‖` for `G(n, p)` with `pn ≥ c log n` (its Lemma A.7) by combining
Theorem 3.2 of Benaych-Georges, Bordenave and Knowles (the expectation) with Theorem 6.10 of
Boucheron, Lugosi and Massart (the concentration). Both are stated here, in their sources' terms,
as propositions. The paper's derivation of Lemma A.7 from them is formalized as
`PowerOfFew.Sparse.lemmaA_7_of_bbk_blm`. The library proves Lemma A.7 itself by Feige and Ofek's
argument instead (`PowerOfFew.FeigeOfek.feigeOfek`), so no result of the library assumes them.
See `PowerOfFew/External/RandomMatrix/README.md`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew

/-- **Benaych-Georges–Bordenave–Knowles**, *Spectral radii of sparse random matrices*
(Ann. Inst. H. Poincaré Probab. Statist. 56, 2020; arXiv:1704.02945), Theorem 3.2, for the
homogeneous Erdős–Rényi graph `G(n, p)` (`p_ij = p` for `i ≠ j`): there is a universal constant
`C > 0` such that, with `d = p(n − 1)` (the maximal expected degree),
`κ = p / (d / n)`, `q = √d ∧ n^(1/10) κ^(-1/9)` and `η = √(log n) / q`, if `q ≥ 1` then
`E‖A − EA‖ / √d ≤ 2 + C η / √(1 ∨ log η)`. Not proved; only the paper's derivation of Lemma
A.7 (`PowerOfFew.Sparse.lemmaA_7_of_bbk_blm`) takes it as a hypothesis. -/
def BBKTheorem3_2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (p : ℝ), 0 < p → p ≤ 1 →
    let d : ℝ := p * (n - 1)
    let κ : ℝ := p / (d / n)
    let q : ℝ := min (Real.sqrt d) ((n : ℝ) ^ (1 / 10 : ℝ) * κ ^ (-(1 / 9 : ℝ)))
    let η : ℝ := Real.sqrt (Real.log n) / q
    1 ≤ q →
      (∫ G, specNorm (adjMat G - meanAdj n p) ∂(SimpleGraph.binomialRandom (Fin n) (toUnit p))) /
          Real.sqrt d ≤
        2 + C * η / Real.sqrt (max 1 (Real.log η))

/-- **Boucheron–Lugosi–Massart**, *Concentration Inequalities* (Oxford, 2013), Theorem 6.10: let
`X₁, …, X_N` be independent random variables with values in `[0, 1]`, and `f : [0, 1]^N → ℝ` a
separately convex function with `|f(x) − f(y)| ≤ ‖x − y‖` (Euclidean norm) on `[0, 1]^N`. Then
`Z = f(X₁, …, X_N)` satisfies `P{Z > EZ + t} ≤ e^(−t²/2)` for all `t > 0`. Not proved; only
the paper's derivation of Lemma A.7 (`PowerOfFew.Sparse.lemmaA_7_of_bbk_blm`) takes it as a
hypothesis. -/
def BLMTheorem6_10 : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ)
    (X : Fin N → Ω → ℝ) (f : (Fin N → ℝ) → ℝ),
    (∀ i, Measurable (X i)) → iIndepFun X μ → (∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) →
    (∀ (x : Fin N → ℝ) (i : Fin N), (∀ j, x j ∈ Set.Icc (0 : ℝ) 1) →
      ConvexOn ℝ (Set.Icc (0 : ℝ) 1) fun s => f (Function.update x i s)) →
    (∀ x y : Fin N → ℝ, (∀ j, x j ∈ Set.Icc (0 : ℝ) 1) → (∀ j, y j ∈ Set.Icc (0 : ℝ) 1) →
      |f x - f y| ≤ Real.sqrt (∑ j, (x j - y j) ^ 2)) →
    ∀ t : ℝ, 0 < t →
      μ.real {ω | (∫ ω', f (fun j => X j ω') ∂μ) + t < f (fun j => X j ω)} ≤
        Real.exp (-t ^ 2 / 2)

end PowerOfFew

end
