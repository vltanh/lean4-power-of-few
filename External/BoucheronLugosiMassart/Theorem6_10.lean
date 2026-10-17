module

public import Mathlib

/-!
# Boucheron, Lugosi and Massart, Theorem 6.10 (stated, not proved)

S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities: A Nonasymptotic Theory of
Independence*, Oxford University Press (2013), Theorem 6.10 (first proved by Talagrand): a
separately convex `1`-Lipschitz function of independent `[0, 1]`-valued variables exceeds its mean
by `t` with probability at most `e^(−t²/2)`.

The sparse paper uses it in its proof of Lemma A.7. The formalization proves Lemma A.7 by Feige and
Ofek's argument instead (`External.FeigeOfek`), so this proposition is a hypothesis only of the
paper's own derivation, `PowerOfFew.Sparse.lemmaA_7_of_bbk_blm`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace External.BoucheronLugosiMassart

/-- **Theorem 6.10**: let `X₁, …, X_N` be independent random variables with values in `[0, 1]`, and
`f : [0, 1]^N → ℝ` a separately convex function with `|f(x) − f(y)| ≤ ‖x − y‖` (Euclidean norm) on
`[0, 1]^N`. Then `Z = f(X₁, …, X_N)` satisfies `P{Z > EZ + t} ≤ e^(−t²/2)` for all `t > 0`. -/
def theorem6_10 : Prop :=
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

end External.BoucheronLugosiMassart

end
