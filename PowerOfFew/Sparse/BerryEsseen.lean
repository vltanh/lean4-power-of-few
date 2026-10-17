module

public import PowerOfFew.Model.BerryEsseen

/-!
# Sparse paper, Appendix A: consequences of the Berry–Esseen inequality

Corollary A.2 and Lemma A.3 of B. Tran–Vu, *The "Power of Few" phenomenon: the sparse case*
(Random Structures & Algorithms 66 (2025), e21260; arXiv:2302.05605v2). The paper states that they
"naturally follow" from the Berry–Esseen inequality (its Theorem A.1, assumed here as
`ShevtsovaBerryEsseen`) and gives no proof.

Reading: Corollary A.2 does not say that its Bernoulli variables are independent; the
Berry–Esseen inequality needs it, and the paper applies the corollary to independent variables.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*}
  {p : ℝ} {Y : ι → Ω → ℝ}

/-- **Corollary A.2** (`S:lem:strongesseen`). Let `p ∈ (0, 1)` and let `X₁, …, Xₙ` be independent
variables such that each `Xᵢ ∼ Ber(p)` or `Xᵢ ∼ −Ber(p)`; let `X = ∑ Xᵢ` and `μ_X = E X`. Then
`sup_x |P(X − μ_X ≤ x) − Φ(x / (σ √n))| ≤ 0.56 (1 − 2σ²) / (σ √n)`, `σ = √(p(1 − p))`.
Here `Xᵢ = sᵢ Yᵢ` with signs `sᵢ = ±1` and a Bernoulli(`p`) family `Y`. -/
theorem corollaryA_2 (hBE : ShevtsovaBerryEsseen) (hp0 : 0 < p) (hp1 : p < 1)
    (hY : IsBernoulliFamily μ p Y) (s : ι → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) {S : Finset ι}
    (hS : S.Nonempty) (x : ℝ) :
    |μ.real {ω | ∑ i ∈ S, s i * Y i ω - ∫ ω', ∑ i ∈ S, s i * Y i ω' ∂μ ≤ x} -
        Φ (x / (Real.sqrt (p * (1 - p)) * Real.sqrt S.card))| ≤
      0.56 * (1 - 2 * (p * (1 - p))) / (Real.sqrt (p * (1 - p)) * Real.sqrt S.card) := by
  sorry

/-- **Lemma A.3** (`S:lem:esseen-err-term`). Let `p ∈ (0, 1)`, `σ = √(p(1 − p))`, and let
`X₁ ∼ Bin(n₁, p)` and `X₂ ∼ Bin(n₂, p)` be independent. For every positive integer
`d < (n₁ + n₂)/2`, `P(X₁ = X₂ + d) ≤ 1.12 (1 − 2σ²) / (σ √(n₁ + n₂))`. -/
theorem lemmaA_3 (hBE : ShevtsovaBerryEsseen) (hp0 : 0 < p) (hp1 : p < 1)
    (hY : IsBernoulliFamily μ p Y) {S₁ S₂ : Finset ι} (hS : Disjoint S₁ S₂) {d : ℕ} (hd : 0 < d)
    (hdn : (d : ℝ) < (S₁.card + S₂.card) / 2) :
    μ.real {ω | ∑ i ∈ S₁, Y i ω = ∑ i ∈ S₂, Y i ω + d} ≤
      1.12 * (1 - 2 * (p * (1 - p))) /
        (Real.sqrt (p * (1 - p)) * Real.sqrt (S₁.card + S₂.card)) := by
  sorry

end PowerOfFew.Sparse

end
