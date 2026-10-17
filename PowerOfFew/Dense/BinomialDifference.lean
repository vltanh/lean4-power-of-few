module

public import PowerOfFew.Model.BerryEsseen

/-!
# Dense paper, Section 2.1: the difference of two binomial variables

Lemmas 2.3 and 2.4 of Tran–Vu, *Reaching a consensus on random networks: the power of few*
(Theory of Computing 19 (2023), article 6), which apply the Berry–Esseen inequality with
Shevtsova's constant (the paper's Theorem 2.2, assumed here as `ShevtsovaBerryEsseen`).

Independent binomial variables `Y₁ ∼ Bin(n₁, p)` and `Y₂ ∼ Bin(n₂, p)` are represented as the sums
of a Bernoulli(`p`) family over disjoint finite index sets `S₁` and `S₂` (`#S₁ = n₁`,
`#S₂ = n₂`); `IsBernoulliFamily.measureReal_sum_eq` shows that such sums are binomial.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Dense

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*}
  {p : ℝ} {X : ι → Ω → ℝ}

/-- **Lemma 2.3** (`D:thm:diff-of-binom-r.v.-gen.`). For `p ∈ (0, 1)`, independent
`Y₁ ∼ Bin(n₁, p)` and `Y₂ ∼ Bin(n₂, p)` with `n₁ > n₂`, and every real `d`,
`P(Y₁ > Y₂ + d) ≥ 1/2 + Φ₀((p(n₁ − n₂) − d) / √(p(1 − p)(n₁ + n₂)))
  − 0.56 (1 − 2p + 2p²) / √(p(1 − p)(n₁ + n₂))`. -/
theorem lemma2_3 (hBE : ShevtsovaBerryEsseen) (hp0 : 0 < p) (hp1 : p < 1)
    (hX : IsBernoulliFamily μ p X) {S₁ S₂ : Finset ι} (hS : Disjoint S₁ S₂)
    (h21 : S₂.card < S₁.card) (d : ℝ) :
    1 / 2 + Φ₀ ((p * ((S₁.card : ℝ) - S₂.card) - d) /
          Real.sqrt (p * (1 - p) * (S₁.card + S₂.card))) -
        0.56 * (1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p) * (S₁.card + S₂.card)) ≤
      μ.real {ω | ∑ i ∈ S₂, X i ω + d < ∑ i ∈ S₁, X i ω} := by
  sorry

/-- **Lemma 2.4** (`D:thm:1/sqrt-n`). For `p ∈ (0, 1)`, independent `X₁ ∼ Bin(n₁, p)` and
`X₂ ∼ Bin(n₂, p)`, and every integer `d`,
`P(X₁ = X₂ + d) ≤ 1.12 (1 − 2p + 2p²) / √(p(1 − p)(n₁ + n₂))`.

Reading: the paper's bound is undefined (infinite) when `n₁ + n₂ = 0`, so the statement assumes
`n₁ + n₂ ≥ 1` (in Lean, division by zero gives `0`). -/
theorem lemma2_4 (hBE : ShevtsovaBerryEsseen) (hp0 : 0 < p) (hp1 : p < 1)
    (hX : IsBernoulliFamily μ p X) {S₁ S₂ : Finset ι} (hS : Disjoint S₁ S₂)
    (hne : 0 < S₁.card + S₂.card) (d : ℤ) :
    μ.real {ω | ∑ i ∈ S₁, X i ω = ∑ i ∈ S₂, X i ω + d} ≤
      1.12 * (1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p) * (S₁.card + S₂.card)) := by
  sorry

end PowerOfFew.Dense

end
