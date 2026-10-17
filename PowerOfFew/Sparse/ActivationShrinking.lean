module

public import PowerOfFew.Sparse.DayTwo
public import PowerOfFew.Sparse.DayThree
public import PowerOfFew.Sparse.Chernoff
public import PowerOfFew.Sparse.ActivationLastDays

/-!
# Sparse paper, Section 4: Blue shrinks with random activations and updates

Proposition 4.3 of the sparse paper: from `|B₁| ≤ n/2 − K √(n / (p p_ac))`, Blue shrinks by a
factor `1 − 0.8 p_up p_ac` every day (Lemmas 2.4 and 2.5 on the subgraph induced by the active
vertices, with Lemmas A.4, A.6 and A.7) until it has at most `α_λ (log n)/2` vertices. See
`PowerOfFew/Sparse/Activation.lean` for the setting and the readings of Section 4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- **Proposition 4.3** (`S:prop:main-lazy-details-prop2`). Under the assumptions of Theorem 4.1
and `|B₁| ≤ n/2 − K √(n / (p p_ac))`, for every `K ≥ 8` there is `t*₁ = O(p_up⁻¹ p_ac⁻¹ log n)`
such that, with probability at least `1 − e^(−Ω(K² p⁻¹)) − n^(−Ω(p_up p_ac))`,
`|B_{t*₁}| ≤ α_λ (log n) / 2`.

Readings: the probability that `|B₁|` satisfies the assumption and every `B_t`,
`t ≤ A log n / (p_up p_ac)`, has more than `α_λ (log n)/2` vertices is at most
`e^(−c₁ K² / p) + n^(−c₂ p_up p_ac)`; the statement's "for every `ε > 0`" is unused. -/
theorem proposition4_3 (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10) :
    ∃ A c₁ : ℝ, 0 < c₁ ∧ ∀ K lam : ℝ, 8 ≤ K → 0 < lam →
      ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ pac pup : ℝ, 0 < pac → pac ≤ 1 → 0 < pup → pup ≤ 1 →
      ∃ N : ℕ, ∀ n ≥ N, ∀ (p : ℝ) (B₀ : Set (Fin n)), 0 < p →
        (1 + lam) * Real.log n ≤ p * pac * n → 10 ≤ (1 - p) * pac * n →
        lazyProb n p pac pup (fun G c =>
          ((lazyBlueAfter G c B₀ 1).ncard : ℝ) ≤ n / 2 - K * Real.sqrt (n / (p * pac)) ∧
          ∀ t : ℕ, (t : ℝ) ≤ A * Real.log n / (pup * pac) →
            alphaDeg lam * Real.log n / 2 < (lazyBlueAfter G c B₀ t).ncard) ≤
          Real.exp (-(c₁ * K ^ 2 / p)) + (n : ℝ) ^ (-(c₂ * pup * pac)) := by
  sorry

end PowerOfFew.Sparse

end
