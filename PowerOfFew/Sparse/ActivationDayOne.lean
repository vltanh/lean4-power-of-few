module

public import PowerOfFew.Sparse.DayOne
public import PowerOfFew.Model.Lazy

/-!
# Sparse paper, Section 4: the first day with random activations and updates

Proposition 4.2 of the sparse paper (proved in its Appendix B): the argument of Lemma 2.1 and
Proposition 2.2, run on the subgraph induced by the vertices active on day 1. See
`PowerOfFew/Sparse/Activation.lean` for the setting, the readings and the corrections of Section 4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- **Proposition 4.2** (`S:prop:day1-lazy`). In the setting of Theorem 4.1, for every
`ε ∈ (0, 1)` and `K > 0` there are `M_K`, `S_ε` and `T_ε` such that, when
`p_ac^(1/2) Δ ≥ S_ε n^(1/2)`, `p^(1/2) p_up p_ac Δ ≥ T_ε` and `p p_up p_ac² Δ ≥ M_K`, with
probability at least `1 − ε`, `|B₁| ≤ n/2 − K √(n / (p p_ac))`.

Readings: the paper writes "for every `ε ∈ (0, 1)` and `T > 0`", a misprint for `K > 0`; its proof
takes `n` large (`n ≥ N`) and uses `(1 − p) p_ac n ≥ 10` (module docstring). -/
theorem proposition4_2 (hBE : ShevtsovaBerryEsseen) :
    ∃ M S T : ℝ → ℝ, ∀ ε K lam pac pup : ℝ, 0 < ε → ε < 1 → 0 < K → 0 < lam → 0 < pac →
      pac ≤ 1 → 0 < pup → pup ≤ 1 →
      ∃ N : ℕ, ∀ n ≥ N, ∀ (p : ℝ) (B₀ : Set (Fin n)), 0 < p →
        (1 + lam) * Real.log n ≤ p * pac * n → 10 ≤ (1 - p) * pac * n →
        S ε * Real.sqrt n ≤ Real.sqrt pac * ((n : ℝ) / 2 - B₀.ncard) →
        T ε ≤ Real.sqrt p * pup * pac * ((n : ℝ) / 2 - B₀.ncard) →
        M K ≤ p * pup * pac ^ 2 * ((n : ℝ) / 2 - B₀.ncard) →
        1 - ε ≤ lazyProb n p pac pup (fun G c =>
          ((lazyBlueAfter G c B₀ 1).ncard : ℝ) ≤ n / 2 - K * Real.sqrt (n / (p * pac))) := by
  sorry

end PowerOfFew.Sparse

end
