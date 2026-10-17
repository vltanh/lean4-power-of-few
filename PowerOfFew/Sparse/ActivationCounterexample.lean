module

public import PowerOfFew.Defs

/-!
# Sparse paper, Section 4: Theorems 1.7 and 4.1 are false as printed

Counterexample (unconditional; it uses none of the assumed cited results): `p = 1` (the complete
graph), `p_ac = 1/2`, `p_up = 1`, and `|B₀| = n/2 − Δ` with `Δ = ⌊n^(1/4)⌋`. The difference between
the active Red and Blue vertices on day 1 is `Δ ± Θ(√n)`, so it is at most `−2` with probability
tending to `1/2`; then every active vertex turns Blue, and afterwards Blue has a linear majority
among the active vertices of every day except with probability `e^(−Ω(n))`, so Blue only grows.
Red wins with probability at most `1/2 + o(1)`, whereas the printed theorems claim `1 − o(1)`.

Two readings of the printed statements are refuted:

* uniform (`theorem1_7_printed_false`, `theorem4_1_printed_false`): the constants may depend on
  `λ`, `p_ac` and `p_up` (the weakest uniform reading), and the bound is claimed for every `n`,
  `p`, `B₀` satisfying the hypotheses;
* per sequence (`theorem1_7_printed_false_seq`, `theorem4_1_printed_false_seq`): "assume `p = p(n)`
  satisfies …" read for one sequence `(p, B₀)` at a time, with constants that may depend on the
  sequence and the bound claimed only for `n` large. Along the counterexample sequence, the
  hypotheses hold for all large `n` (whatever the threshold for `pΔ` or `p p_up p_ac² Δ`) and no
  constants make the bound hold for all large `n`.

Theorem 1.7's hypothesis `p p_ac n ≥ (1 + λ) n⁻¹ log n` is read with its misprint corrected
(`≥ (1 + λ) log n`); the counterexample satisfies both.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace PowerOfFew.Sparse

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

/-- Theorem 1.7 as printed fails along one sequence: with `p = 1`, `p_ac = 1/2`, `p_up = 1`,
`λ = 1/2` and a sequence of initial Blue sets `B n`, the hypotheses hold for all large `n`
(whatever the threshold `C₀` for `pΔ`), and no constants `A`, `C₁`, `C₂`, `c` make the printed bound
hold for all large `n`. -/
theorem theorem1_7_printed_false_seq :
    ∃ B : (n : ℕ) → Set (Fin n),
      (∀ C₀ : ℝ, ∀ᶠ n : ℕ in atTop, (1 + 1 / 2) * Real.log n ≤ 1 * (1 / 2) * n ∧
        C₀ ≤ 1 * ((n : ℝ) / 2 - (B n).ncard)) ∧
      ¬ ∃ A C₁ C₂ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
          1 - C₁ / min (n : ℝ) (1 * ((n : ℝ) / 2 - (B n).ncard) ^ 2) -
              C₂ * (n : ℝ) ^ (-((1 / 2 : ℝ) / 4)) - (n : ℝ) ^ (-c) ≤
            lazyProb n 1 (1 / 2) 1 (fun G c' => ∃ t : ℕ,
              (t : ℝ) ≤ A * Real.log n ∧ lazyBlueAfter G c' (B n) t = ∅) := by
  sorry

/-- Theorem 4.1 as printed fails along one sequence (`p = 1`, `p_ac = 1/2`, `p_up = 1`,
`λ = 1/2`): the hypotheses hold for all large `n` (whatever `M`), and no constants make the
printed bound hold for all large `n`. -/
theorem theorem4_1_printed_false_seq :
    ∃ B : (n : ℕ) → Set (Fin n),
      (∀ M : ℝ, ∀ᶠ n : ℕ in atTop, (1 + 1 / 2) * Real.log n ≤ 1 * (1 / 2) * n ∧
        M ≤ 1 * 1 * (1 / 2) ^ 2 * ((n : ℝ) / 2 - (B n).ncard)) ∧
      ¬ ∃ A C₁ c₁ C₂ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ n : ℕ in atTop,
          1 - C₁ / (1 ^ 2 * (1 / 2) ^ 2 *
                min (n : ℝ) (1 * (1 / 2) * ((n : ℝ) / 2 - (B n).ncard) ^ 2)) -
              Real.exp (-(c₁ * 1 ^ 2 * (1 / 2) ^ 4 * 1 * ((n : ℝ) / 2 - (B n).ncard) ^ 2)) -
              C₂ * (n : ℝ) ^ (-((1 / 2 : ℝ) / 4)) - (n : ℝ) ^ (-(c₂ * 1 * (1 / 2))) ≤
            lazyProb n 1 (1 / 2) 1 (fun G c => ∃ t : ℕ,
              (t : ℝ) ≤ A * Real.log n / (1 * (1 / 2)) ∧ lazyBlueAfter G c (B n) t = ∅) := by
  sorry

end PowerOfFew.Sparse

end
