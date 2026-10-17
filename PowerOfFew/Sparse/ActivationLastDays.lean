module

public import PowerOfFew.Sparse.Degrees
public import PowerOfFew.Model.Lazy

/-!
# Sparse paper, Section 4: the last days with random activations and updates

The constant `α_λ` of Lemma A.4 and Proposition 4.4 of the sparse paper (unlabelled there): once
Blue has at most `α_λ (log n)/2` vertices, every Blue vertex that updates turns Red, and within
`O(log n)` more days every one of them has updated. See `PowerOfFew/Sparse/Activation.lean` for
the setting and the readings of Section 4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- `α_λ = exp(−(8/λ + 7))`, the constant of Lemma A.4. -/
def alphaDeg (lam : ℝ) : ℝ := Real.exp (-(8 / lam + 7))

/-- **Proposition 4.4** (`S:prop:lazy-final`; unlabelled in the paper). Under the assumptions of
Theorem 4.1 and `|B_{t*₁}| ≤ α_λ (log n)/2`, where `t*₁ = O(p_up⁻¹ p_ac⁻¹ log n)` comes from
Proposition 4.3, there is `t*₂ = t*₁ + O(log n)` such that Red wins after day `t*₂` with
probability at least `1 − O(n^(−λ/4)) − O(n^(−p_up p_ac / 2))`.

Reading: for every `A₁`, the probability that some day `t₀ ≤ A₁ log n / (p_up p_ac)` has
`|B_{t₀}| ≤ α_λ (log n)/2` while Blue is not empty on day
`⌈A₁ log n / (p_up p_ac)⌉ + ⌈A log n⌉` is at most `C n^(−λ/4) + C n^(−p_up p_ac / 2)`. -/
theorem proposition4_4 :
    ∃ A C : ℝ, ∀ A₁ lam pac pup : ℝ, 0 < A₁ → 0 < lam → 0 < pac → pac ≤ 1 → 0 < pup → pup ≤ 1 →
      ∃ N : ℕ, ∀ n ≥ N, ∀ (p : ℝ) (B₀ : Set (Fin n)), 0 < p → p ≤ 1 →
        (1 + lam) * Real.log n ≤ p * pac * n →
        lazyProb n p pac pup (fun G c =>
          (∃ t₀ : ℕ, (t₀ : ℝ) ≤ A₁ * Real.log n / (pup * pac) ∧
            ((lazyBlueAfter G c B₀ t₀).ncard : ℝ) ≤ alphaDeg lam * Real.log n / 2) ∧
          lazyBlueAfter G c B₀ (⌈A₁ * Real.log n / (pup * pac)⌉₊ + ⌈A * Real.log n⌉₊) ≠ ∅) ≤
          C * (n : ℝ) ^ (-(lam / 4)) + C * (n : ℝ) ^ (-(pup * pac / 2)) := by
  sorry

end PowerOfFew.Sparse

end
