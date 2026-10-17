module

public import Mathlib

/-!
# Families of independent Bernoulli random variables

A family `X : ι → Ω → ℝ` of independent random variables, each with values in `{0, 1}` and equal
to `1` with probability `p`. Sums of such variables over disjoint finite index sets are the
independent binomial variables of the two papers: `∑ i ∈ S, X i` has the law `Bin(#S, p)`
(`IsBernoulliFamily.measureReal_sum_eq`).

## Main declarations

* `ProbabilityTheory.IsBernoulliFamily`: the predicate.
* `IsBernoulliFamily.measureReal_sum_eq`: the law of a sum is binomial.
* `IsBernoulliFamily.integral_eq`, `integral_sq_sub`, `integral_abs_pow_three_sub`: the mean `p`,
  the variance `p(1 - p)` and the third absolute central moment `p(1 - p)(1 - 2p + 2p²)`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- `X` is a family of independent random variables with values in `{0, 1}`, each equal to `1`
with probability `p`. -/
structure IsBernoulliFamily (μ : Measure Ω) (p : ℝ) (X : ι → Ω → ℝ) : Prop where
  measurable : ∀ i, Measurable (X i)
  indep : iIndepFun X μ
  zero_or_one : ∀ i ω, X i ω = 0 ∨ X i ω = 1
  prob_one : ∀ i, μ.real {ω | X i ω = 1} = p

namespace IsBernoulliFamily

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ℝ} {X : ι → Ω → ℝ}

/-- The mean of each variable is `p`. -/
theorem integral_eq (hX : IsBernoulliFamily μ p X) (i : ι) : ∫ ω, X i ω ∂μ = p := by
  sorry

/-- The variance of each variable is `p (1 - p)`. -/
theorem integral_sq_sub (hX : IsBernoulliFamily μ p X) (i : ι) :
    ∫ ω, (X i ω - p) ^ 2 ∂μ = p * (1 - p) := by
  sorry

/-- The third absolute central moment of each variable is `p (1 - p) (1 - 2p + 2p²)`. -/
theorem integral_abs_pow_three_sub (hX : IsBernoulliFamily μ p X) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : ι) : ∫ ω, |X i ω - p| ^ 3 ∂μ = p * (1 - p) * (1 - 2 * p + 2 * p ^ 2) := by
  sorry

/-- The sum over a finite set `S` has the binomial law `Bin(#S, p)`. -/
theorem measureReal_sum_eq (hX : IsBernoulliFamily μ p X) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset ι) (k : ℕ) :
    μ.real {ω | ∑ i ∈ S, X i ω = k} = (S.card.choose k : ℝ) * p ^ k * (1 - p) ^ (S.card - k) := by
  sorry

/-- Restricting a Bernoulli family along an injective map gives a Bernoulli family. -/
theorem comp {κ : Type*} (hX : IsBernoulliFamily μ p X) {f : κ → ι}
    (hf : Function.Injective f) : IsBernoulliFamily μ p (fun k => X (f k)) := by
  sorry

end IsBernoulliFamily

end ProbabilityTheory
