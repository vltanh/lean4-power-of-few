module

public import PowerOfFew.Sparse.Main
public import PowerOfFew.Sparse.Chernoff

/-!
# Sparse paper, Section 4: random activations and updates

Theorems 1.7 and 4.1 and Propositions 4.2–4.4 of the sparse paper, for majority dynamics with
activation rate `p_ac` and updating rate `p_up` (Definition 1.6; `lazyStep`, `lazyProb`).

**Theorems 1.7 and 4.1 are false as printed** (`theorem1_7_printed_false`,
`theorem4_1_printed_false`): with `p = 1`, `p_ac = 1/2`, `p_up = 1` and `Δ = ⌊n^(1/4)⌋`, the
difference between the active Red and Blue vertices on day 1 is `Δ ± Θ(√n)`, so it is at most
`−2` with probability tending to `1/2`; then every active vertex turns Blue, and Blue only grows
afterwards (each later day fails with probability `e^(−Ω(n))`). So Red wins with probability at
most `1/2 + o(1)`, whereas the theorems claim `1 − o(1)`. The paper's proof of Proposition 4.2
assumes `p_ac^(1/2) Δ ≥ S_ε n^(1/2)`, which the theorems omit.

The corrected statements (agreed with the user) keep that hypothesis, in the form of
Proposition 4.2: for every `ε` there is `S_ε`, and the failure probability of the first day is
`ε`. Theorem 1.7's hypothesis `p p_ac n ≥ (1 + λ) n⁻¹ log n` is a misprint for
`p p_ac n ≥ (1 + λ) log n` (as in Theorem 4.1).

Readings: `Δ = n/2 − |B₀|`. The propositions are stated, as their proofs show them, as bounds on
the probability that the stated assumption holds and the conclusion fails. The constants hidden
in `O(·)` and `Ω(·)`, and the threshold for `n`, may depend on `λ`, `p_ac` and `p_up` (the proofs
take `n` large in terms of them), except where the paper indexes them by `ε` or `K` only.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- `α_λ = exp(−(8/λ + 7))`, the constant of Lemma A.4. -/
def alphaDeg (lam : ℝ) : ℝ := Real.exp (-(8 / lam + 7))

/-- **Proposition 4.2** (`S:prop:day1-lazy`). In the setting of Theorem 4.1, for every
`ε ∈ (0, 1)` and `K > 0` there are `M_K`, `S_ε` and `T_ε` such that, when
`p_ac^(1/2) Δ ≥ S_ε n^(1/2)`, `p^(1/2) p_up p_ac Δ ≥ T_ε` and `p p_up p_ac² Δ ≥ M_K`, with
probability at least `1 − ε`, `|B₁| ≤ n/2 − K √(n / (p p_ac))`.

Readings: the paper writes "for every `ε ∈ (0, 1)` and `T > 0`", a misprint for `K > 0`; its proof
takes `n` large (`n ≥ N`). -/
theorem proposition4_2 (hBE : ShevtsovaBerryEsseen) :
    ∃ M S T : ℝ → ℝ, ∀ ε K lam pac pup : ℝ, 0 < ε → ε < 1 → 0 < K → 0 < lam → 0 < pac →
      pac ≤ 1 → 0 < pup → pup ≤ 1 →
      ∃ N : ℕ, ∀ n ≥ N, ∀ (p : ℝ) (B₀ : Set (Fin n)), 0 < p → p ≤ 1 →
        (1 + lam) * Real.log n ≤ p * pac * n →
        S ε * Real.sqrt n ≤ Real.sqrt pac * ((n : ℝ) / 2 - B₀.ncard) →
        T ε ≤ Real.sqrt p * pup * pac * ((n : ℝ) / 2 - B₀.ncard) →
        M K ≤ p * pup * pac ^ 2 * ((n : ℝ) / 2 - B₀.ncard) →
        1 - ε ≤ lazyProb n p pac pup (fun G c =>
          ((lazyBlueAfter G c B₀ 1).ncard : ℝ) ≤ n / 2 - K * Real.sqrt (n / (p * pac))) := by
  sorry

/-- **Proposition 4.3** (`S:prop:main-lazy-details-prop2`). Under the assumptions of Theorem 4.1
and `|B₁| ≤ n/2 − K √(n / (p p_ac))`, for every `K ≥ 8` there is `t*₁ = O(p_up⁻¹ p_ac⁻¹ log n)`
such that, with probability at least `1 − e^(−Ω(K² p⁻¹)) − n^(−Ω(p_up p_ac))`,
`|B_{t*₁}| ≤ α_λ (log n) / 2`.

Readings: the probability that `|B₁|` satisfies the assumption and every `B_t`,
`t ≤ A log n / (p_up p_ac)`, has more than `α_λ (log n)/2` vertices is at most
`e^(−c₁ K² / p) + n^(−c₂ p_up p_ac)`; the statement's "for every `ε > 0`" is unused. -/
theorem proposition4_3 (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10) :
    ∃ A c₁ : ℝ, 0 < c₁ ∧ ∀ K lam pac pup : ℝ, 8 ≤ K → 0 < lam → 0 < pac → pac ≤ 1 →
      0 < pup → pup ≤ 1 →
      ∃ (c₂ : ℝ) (N : ℕ), 0 < c₂ ∧ ∀ n ≥ N, ∀ (p : ℝ) (B₀ : Set (Fin n)), 0 < p → p ≤ 1 →
        (1 + lam) * Real.log n ≤ p * pac * n →
        lazyProb n p pac pup (fun G c =>
          ((lazyBlueAfter G c B₀ 1).ncard : ℝ) ≤ n / 2 - K * Real.sqrt (n / (p * pac)) ∧
          ∀ t : ℕ, (t : ℝ) ≤ A * Real.log n / (pup * pac) →
            alphaDeg lam * Real.log n / 2 < (lazyBlueAfter G c B₀ t).ncard) ≤
          Real.exp (-(c₁ * K ^ 2 / p)) + (n : ℝ) ^ (-(c₂ * pup * pac)) := by
  sorry

/-- **Proposition 4.4** (`S:prop:lazy-final`; unlabelled in the paper). Under the assumptions of
Theorem 4.1 and `|B_{t*₁}| ≤ α_λ (log n)/2`, there is `t*₂ = t*₁ + O(log n)` such that Red wins
after day `t*₂` with probability at least `1 − O(n^(−λ/4)) − O(n^(−p_up p_ac / 2))`.

Reading: for every day `t₀`, the probability that `|B_{t₀}| ≤ α_λ (log n)/2` and Blue is not empty
`A log n` days later is at most `C n^(−λ/4) + C n^(−p_up p_ac / 2)`. -/
theorem proposition4_4 :
    ∃ A C : ℝ, ∀ lam pac pup : ℝ, 0 < lam → 0 < pac → pac ≤ 1 → 0 < pup → pup ≤ 1 →
      ∃ N : ℕ, ∀ n ≥ N, ∀ (p : ℝ) (B₀ : Set (Fin n)) (t₀ : ℕ), 0 < p → p ≤ 1 →
        (1 + lam) * Real.log n ≤ p * pac * n →
        lazyProb n p pac pup (fun G c =>
          ((lazyBlueAfter G c B₀ t₀).ncard : ℝ) ≤ alphaDeg lam * Real.log n / 2 ∧
          lazyBlueAfter G c B₀ (t₀ + ⌈A * Real.log n⌉₊) ≠ ∅) ≤
          C * (n : ℝ) ^ (-(lam / 4)) + C * (n : ℝ) ^ (-(pup * pac / 2)) := by
  sorry

/-- **Theorem 4.1** (`S:thm:main-lazy-details`), corrected. Assume `|R₀| = n/2 + Δ` and
`p p_ac n ≥ (1 + λ) log n` for a constant `λ > 0`. For every `ε ∈ (0, 1)` and `K ≥ 8` there are
`S_ε`, `T_ε` and `M_K` such that, if `p_ac^(1/2) Δ ≥ S_ε n^(1/2)`, `p^(1/2) p_up p_ac Δ ≥ T_ε` and
`p p_up p_ac² Δ ≥ M_K`, a Red unanimity is reached within time `O(p_up⁻¹ p_ac⁻¹ log n)` with
probability at least `1 − ε − e^(−Ω(K² p⁻¹)) − O(n^(−λ/4)) − n^(−Ω(p_up p_ac))`.

Correction: the printed theorem has no hypothesis on `p_ac^(1/2) Δ / n^(1/2)` and is false
(`theorem4_1_printed_false`); the first-day failure probability, printed
`O(1/(p_up² p_ac² min{n, p p_ac Δ²}))`, is the `ε` of Proposition 4.2, and the printed
`e^(−Ω(p_up² p_ac⁴ p Δ²))` is the `e^(−Ω(K² p⁻¹))` of Proposition 4.3 with `K` free. -/
theorem theorem4_1 (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10) :
    ∃ (M S T : ℝ → ℝ) (A c₁ : ℝ), 0 < c₁ ∧ ∀ ε K lam pac pup : ℝ, 0 < ε → ε < 1 → 8 ≤ K →
      0 < lam → 0 < pac → pac ≤ 1 → 0 < pup → pup ≤ 1 →
      ∃ C c₂ : ℝ, 0 < c₂ ∧ ∀ (n : ℕ) (p : ℝ) (B₀ : Set (Fin n)), 0 < p → p ≤ 1 →
        (1 + lam) * Real.log n ≤ p * pac * n →
        S ε * Real.sqrt n ≤ Real.sqrt pac * ((n : ℝ) / 2 - B₀.ncard) →
        T ε ≤ Real.sqrt p * pup * pac * ((n : ℝ) / 2 - B₀.ncard) →
        M K ≤ p * pup * pac ^ 2 * ((n : ℝ) / 2 - B₀.ncard) →
        1 - ε - Real.exp (-(c₁ * K ^ 2 / p)) - C * (n : ℝ) ^ (-(lam / 4)) -
            (n : ℝ) ^ (-(c₂ * pup * pac)) ≤
          lazyProb n p pac pup (fun G c => ∃ t : ℕ,
            (t : ℝ) ≤ A * Real.log n / (pup * pac) ∧ lazyBlueAfter G c B₀ t = ∅) := by
  sorry

/-- **Theorem 1.7** (`S:thm:main-lazy`), corrected. Consider majority dynamics with fixed
activation rate `p_ac` and updating rate `p_up` on `G(n, p)`, with `n/2 + Δ` initial Red vertices
and `p p_ac n ≥ (1 + λ) log n` for a constant `λ > 0`. For every `ε ∈ (0, 1)` there are constants
`C` and `S`, depending only on `p_ac`, `p_up`, `λ` and `ε`, such that when `pΔ ≥ C` and
`Δ ≥ S n^(1/2)`, a Red unanimity is reached within time `O_{p_ac,p_up}(log n)` with probability at
least `1 − ε − O(n^(−λ/4)) − n^(−Ω_{p_ac,p_up}(1))`.

Correction: the printed theorem (with its misprint `n⁻¹ log n` corrected) has neither the
hypothesis `Δ ≥ S n^(1/2)` nor the term `ε`, and is false (`theorem1_7_printed_false`). -/
theorem theorem1_7 (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10)
    {pac pup : ℝ} (hpac0 : 0 < pac) (hpac1 : pac ≤ 1) (hpup0 : 0 < pup) (hpup1 : pup ≤ 1)
    {lam : ℝ} (hlam : 0 < lam) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C S A C' c : ℝ, 0 < c ∧ ∀ (n : ℕ) (p : ℝ) (B₀ : Set (Fin n)), 0 < p → p ≤ 1 →
      (1 + lam) * Real.log n ≤ p * pac * n → C ≤ p * ((n : ℝ) / 2 - B₀.ncard) →
      S * Real.sqrt n ≤ (n : ℝ) / 2 - B₀.ncard →
      1 - ε - C' * (n : ℝ) ^ (-(lam / 4)) - (n : ℝ) ^ (-c) ≤
        lazyProb n p pac pup (fun G c' => ∃ t : ℕ,
          (t : ℝ) ≤ A * Real.log n ∧ lazyBlueAfter G c' B₀ t = ∅) := by
  sorry

/-- Theorem 1.7 as printed (with `p p_ac n ≥ (1 + λ) log n`) is false, even if its constants may
depend on `p_ac`, `p_up` and `λ`: there are `p_ac`, `p_up`, `λ` such that, whatever the threshold
`C₀` for `pΔ`, the time constant `A` and the constants of the error terms, some `n`, `p`, `B₀`
violate the bound. -/
theorem theorem1_7_printed_false :
    ¬ ∀ pac pup lam : ℝ, 0 < pac → pac ≤ 1 → 0 < pup → pup ≤ 1 → 0 < lam →
      ∃ C₀ A C₁ C₂ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (p : ℝ) (B₀ : Set (Fin n)), 0 < p → p ≤ 1 →
        (1 + lam) * Real.log n ≤ p * pac * n → C₀ ≤ p * ((n : ℝ) / 2 - B₀.ncard) →
        1 - C₁ / min (n : ℝ) (p * ((n : ℝ) / 2 - B₀.ncard) ^ 2) - C₂ * (n : ℝ) ^ (-(lam / 4)) -
            (n : ℝ) ^ (-c) ≤
          lazyProb n p pac pup (fun G c' => ∃ t : ℕ,
            (t : ℝ) ≤ A * Real.log n ∧ lazyBlueAfter G c' B₀ t = ∅) := by
  sorry

/-- Theorem 4.1 as printed is false, even if its constants may depend on `λ`, `p_ac` and
`p_up`. -/
theorem theorem4_1_printed_false :
    ¬ ∀ lam pac pup : ℝ, 0 < lam → 0 < pac → pac ≤ 1 → 0 < pup → pup ≤ 1 →
      ∃ M A C₁ c₁ C₂ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (n : ℕ) (p : ℝ) (B₀ : Set (Fin n)), 0 < p →
        p ≤ 1 → (1 + lam) * Real.log n ≤ p * pac * n →
        M ≤ p * pup * pac ^ 2 * ((n : ℝ) / 2 - B₀.ncard) →
        1 - C₁ / (pup ^ 2 * pac ^ 2 * min (n : ℝ) (p * pac * ((n : ℝ) / 2 - B₀.ncard) ^ 2)) -
            Real.exp (-(c₁ * pup ^ 2 * pac ^ 4 * p * ((n : ℝ) / 2 - B₀.ncard) ^ 2)) -
            C₂ * (n : ℝ) ^ (-(lam / 4)) - (n : ℝ) ^ (-(c₂ * pup * pac)) ≤
          lazyProb n p pac pup (fun G c => ∃ t : ℕ,
            (t : ℝ) ≤ A * Real.log n / (pup * pac) ∧ lazyBlueAfter G c B₀ t = ∅) := by
  sorry

end PowerOfFew.Sparse

end
