module

public import PowerOfFew.Sparse.ActivationDayOne
public import PowerOfFew.Sparse.ActivationShrinking

/-!
# Sparse paper, Section 4: random activations and updates

Theorems 1.7 and 4.1 and Propositions 4.2–4.4 of the sparse paper, for majority dynamics with
activation rate `p_ac` and updating rate `p_up` (Definition 1.6; `lazyStep`, `lazyProb`).

**Theorems 1.7 and 4.1 are false as printed** (`theorem1_7_printed_false`,
`theorem4_1_printed_false` and their per-sequence forms, in
`PowerOfFew/Sparse/ActivationCounterexample.lean`): with `p = 1`, `p_ac = 1/2`, `p_up = 1` and
`Δ = ⌊n^(1/4)⌋`, the difference between the active Red and Blue vertices on day 1 is
`Δ ± Θ(√n)`, so it is at most `−2` with probability tending to `1/2`; then every active vertex
turns Blue, and Blue only grows afterwards. The paper's proof of Proposition 4.2 assumes
`p_ac^(1/2) Δ ≥ S_ε n^(1/2)`, which the theorems omit.

The corrected statements (agreed with the user) keep that hypothesis, in the form of
Proposition 4.2: for every `ε` there is `S_ε`, and the first day fails with probability at most
`ε`. Theorem 1.7's hypothesis `p p_ac n ≥ (1 + λ) n⁻¹ log n` is a misprint for
`p p_ac n ≥ (1 + λ) log n` (as in Theorem 4.1).

Further hypotheses the paper's proofs use (decision of the user: state the hypotheses the
argument uses): `(1 − p) p_ac n ≥ 10`, the analogue for the active subgraph of Theorem 1.2's
`n − 10 ≥ pn`. The proofs of Propositions 4.2 and 4.3 apply Lemmas 2.1 and 2.4 to the subgraph
induced on the active vertices (about `p_ac n` of them), which need `p` bounded away from `1`.

The propositions are in `ActivationDayOne.lean` (4.2), `ActivationShrinking.lean` (4.3) and
`ActivationLastDays.lean` (4.4); the model's tools are in `PowerOfFew/Model/Lazy.lean`.

Readings: `Δ = n/2 − |B₀|`. Propositions 4.3 and 4.4 are stated, as their proofs show them, as
bounds on the probability that their assumption holds and their conclusion fails. The proofs take
`n` large in terms of `λ`, `p_ac`, `p_up` (`n ≥ N`, or a constant `C` that absorbs small `n`). The
exponent `c₂` of `n^(−c₂ p_up p_ac)` depends on `λ` (through `α_λ` of Lemma A.4) but not on `p_ac`,
`p_up`; with that dependence the term `C n^(−λ/4)` could be absorbed into it, and the statements
keep the paper's two terms for readability.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- **Theorem 4.1** (`S:thm:main-lazy-details`), corrected. Assume `|R₀| = n/2 + Δ`,
`p p_ac n ≥ (1 + λ) log n` for a constant `λ > 0`, and `(1 − p) p_ac n ≥ 10`. For every
`ε ∈ (0, 1)` and `K ≥ 8` there are `S_ε` and `M_K` such that, if `p_ac^(1/2) Δ ≥ S_ε n^(1/2)` and
`p p_up p_ac² Δ ≥ M_K`, a Red unanimity is reached within time `O(p_up⁻¹ p_ac⁻¹ log n)` with
probability at least `1 − ε − e^(−Ω(K² p⁻¹)) − O(n^(−λ/4)) − n^(−Ω(p_up p_ac))`.

Correction: the printed theorem has no hypothesis on `p_ac^(1/2) Δ / n^(1/2)` and is false
(`theorem4_1_printed_false`). The hypothesis `p_ac^(1/2) Δ ≥ S_ε n^(1/2)` and the term `ε` are
those of Proposition 4.2; the printed `O(1/(p_up² p_ac² min{n, p p_ac Δ²}))` was the Chebyshev part
of that `ε`, and the printed `e^(−Ω(p_up² p_ac⁴ p Δ²))` is Proposition 4.3's `e^(−Ω(K² p⁻¹))` with
`K` free. The hypothesis `(1 − p) p_ac n ≥ 10` is the one the propositions' proofs use. -/
theorem theorem4_1 (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10) :
    ∃ (M S : ℝ → ℝ) (A c₁ : ℝ), 0 < c₁ ∧ ∀ ε K lam : ℝ, 0 < ε → ε < 1 → 8 ≤ K → 0 < lam →
      ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ pac pup : ℝ, 0 < pac → pac ≤ 1 → 0 < pup → pup ≤ 1 →
      ∃ C : ℝ, ∀ (n : ℕ) (p : ℝ) (B₀ : Set (Fin n)), 0 < p →
        (1 + lam) * Real.log n ≤ p * pac * n → 10 ≤ (1 - p) * pac * n →
        S ε * Real.sqrt n ≤ Real.sqrt pac * ((n : ℝ) / 2 - B₀.ncard) →
        M K ≤ p * pup * pac ^ 2 * ((n : ℝ) / 2 - B₀.ncard) →
        1 - ε - Real.exp (-(c₁ * K ^ 2 / p)) - C * (n : ℝ) ^ (-(lam / 4)) -
            (n : ℝ) ^ (-(c₂ * pup * pac)) ≤
          lazyProb n p pac pup (fun G c => ∃ t : ℕ,
            (t : ℝ) ≤ A * Real.log n / (pup * pac) ∧ lazyBlueAfter G c B₀ t = ∅) := by
  sorry

/-- **Theorem 1.7** (`S:thm:main-lazy`), corrected. Consider majority dynamics with fixed
activation rate `p_ac` and updating rate `p_up` on `G(n, p)`, with `n/2 + Δ` initial Red vertices,
`p p_ac n ≥ (1 + λ) log n` for a constant `λ > 0`, and `(1 − p) p_ac n ≥ 10`. For every
`ε ∈ (0, 1)` there are constants `C` and `S` such that, when `pΔ ≥ C` and `Δ ≥ S n^(1/2)`, a Red
unanimity is reached within time `O(log n)` with probability at least
`1 − ε − O(n^(−λ/4)) − n^(−Ω(1))`; all these constants depend only on `p_ac`, `p_up`, `λ` and
`ε`.

Correction: the printed theorem (with its misprint `n⁻¹ log n` corrected) has neither the
hypothesis `Δ ≥ S n^(1/2)` nor the term `ε`, and is false (`theorem1_7_printed_false`). -/
theorem theorem1_7 (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10)
    {pac pup : ℝ} (hpac0 : 0 < pac) (hpac1 : pac ≤ 1) (hpup0 : 0 < pup) (hpup1 : pup ≤ 1)
    {lam : ℝ} (hlam : 0 < lam) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C S A C' c : ℝ, 0 < c ∧ ∀ (n : ℕ) (p : ℝ) (B₀ : Set (Fin n)), 0 < p →
      (1 + lam) * Real.log n ≤ p * pac * n → 10 ≤ (1 - p) * pac * n →
      C ≤ p * ((n : ℝ) / 2 - B₀.ncard) → S * Real.sqrt n ≤ (n : ℝ) / 2 - B₀.ncard →
      1 - ε - C' * (n : ℝ) ^ (-(lam / 4)) - (n : ℝ) ^ (-c) ≤
        lazyProb n p pac pup (fun G c' => ∃ t : ℕ,
          (t : ℝ) ≤ A * Real.log n ∧ lazyBlueAfter G c' B₀ t = ∅) := by
  sorry

end PowerOfFew.Sparse

end
