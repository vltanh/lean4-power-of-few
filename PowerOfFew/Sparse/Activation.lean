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

/-- An event about the graph and the coins of one day is measurable (the graph and the coins of
a day range over finite sets). -/
private lemma lazyFinalAux_measurableSet_day {n : ℕ} (t : ℕ)
    (Q : SimpleGraph (Fin n) → DayCoins n → Prop) :
    MeasurableSet {x : SimpleGraph (Fin n) × (ℕ → DayCoins n) | Q x.1 (x.2 t)} := by
  have hS : MeasurableSet {y : SimpleGraph (Fin n) × DayCoins n | Q y.1 y.2} := by
    have : {y : SimpleGraph (Fin n) × DayCoins n | Q y.1 y.2} =
        ⋃ d : DayCoins n, {G | Q G d} ×ˢ {d} := by
      ext ⟨G, d⟩
      simp
    rw [this]
    exact MeasurableSet.iUnion fun d =>
      (measurableSet_simpleGraph _).prod (measurableSet_singleton d)
  exact hS.preimage (measurable_fst.prodMk ((measurable_pi_apply t).comp measurable_snd))

/-- The complement rule for an event about the graph and the coins of one day. -/
private lemma lazyFinalAux_lazyProb_not {n : ℕ} {p pac pup : ℝ} (t : ℕ)
    (P : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop)
    (Q : SimpleGraph (Fin n) → DayCoins n → Prop) (hPQ : ∀ G c, P G c ↔ Q G (c t)) :
    lazyProb n p pac pup (fun G c => ¬ P G c) = 1 - lazyProb n p pac pup P := by
  have hP : P = fun G c => Q G (c t) := funext₂ fun G c => propext (hPQ G c)
  subst hP
  unfold lazyProb
  rw [← probReal_compl_eq_one_sub (lazyFinalAux_measurableSet_day t Q)]
  rfl

/-- `n ≥ 1` when `(1 − p) p_ac n ≥ 10`. -/
private lemma lazyFinalAux_one_le {n : ℕ} {p pac : ℝ} (hpn' : 10 ≤ (1 - p) * pac * n) :
    (1 : ℝ) ≤ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    norm_num at hpn'
  · exact_mod_cast h

/-- `p < 1` when `(1 − p) p_ac n ≥ 10`. -/
private lemma lazyFinalAux_lt_one {n : ℕ} {p pac : ℝ} (hpac0 : 0 < pac) (hn : (0 : ℝ) < n)
    (hpn' : 10 ≤ (1 - p) * pac * n) : p < 1 := by
  by_contra h
  push Not at h
  have : (1 - p) * pac * n ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hpac0.le) hn.le
  linarith

/-- The conditions on large `n` in the proof of Theorem 4.1. -/
private lemma lazyFinalAux_eventually (a b : ℝ) {e : ℝ} (he : 0 < e) :
    ∃ N : ℕ, ∀ n ≥ N, 1 ≤ Real.log n ∧ a ^ 2 ≤ Real.log n ∧ b ≤ (n : ℝ) ^ e := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  exact Filter.eventually_atTop.mp ((hlog.eventually_ge_atTop 1).and
    ((hlog.eventually_ge_atTop _).and (hpow.eventually_ge_atTop _)))

/-- For `1 ≤ n < N`, `(max C 0 + N^(λ/4)) n^(−λ/4) ≥ 1`: the claimed lower bound of Theorem 4.1
is not positive. -/
private lemma lazyFinalAux_small {n N : ℕ} {lam C : ℝ} (hn1 : (1 : ℝ) ≤ n) (hnN : n < N)
    (hlam : 0 ≤ lam / 4) :
    1 ≤ (max C 0 + (N : ℝ) ^ (lam / 4)) * (n : ℝ) ^ (-(lam / 4)) := by
  have hnpos : (0 : ℝ) < n := by linarith
  rw [Real.rpow_neg hnpos.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hnpos _),
    one_mul]
  have : (n : ℝ) ^ (lam / 4) ≤ (N : ℝ) ^ (lam / 4) :=
    Real.rpow_le_rpow hnpos.le (by exact_mod_cast hnN.le) hlam
  linarith [le_max_right C 0]

/-- `C n^(−λ/4) ≤ (max C 0 + N^(λ/4)) n^(−λ/4)`. -/
private lemma lazyFinalAux_le_C {n N : ℕ} {lam C : ℝ} (hn : (0 : ℝ) < n) :
    C * (n : ℝ) ^ (-(lam / 4)) ≤ (max C 0 + (N : ℝ) ^ (lam / 4)) * (n : ℝ) ^ (-(lam / 4)) := by
  have h0 : 0 ≤ (n : ℝ) ^ (-(lam / 4)) := Real.rpow_nonneg hn.le _
  have h1 : 0 ≤ (N : ℝ) ^ (lam / 4) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have := mul_le_mul_of_nonneg_right (le_max_left C 0) h0
  have := mul_nonneg h1 h0
  linarith

/-- Proposition 4.2's hypothesis `T ≤ p^(1/2) p_up p_ac Δ` follows from `p_ac^(1/2) Δ ≥ S n^(1/2)`
with `S ≥ 1`, `p p_ac n ≥ log n` and `log n ≥ (T / p_up)²`. -/
private lemma lazyFinalAux_hypT {n : ℕ} {p pac pup S T Δ : ℝ} (hp0 : 0 < p) (hpac0 : 0 < pac)
    (hpup0 : 0 < pup) (hS1 : 1 ≤ S) (hS : S * Real.sqrt n ≤ Real.sqrt pac * Δ)
    (hpn : Real.log n ≤ p * pac * n) (hLT : (T / pup) ^ 2 ≤ Real.log n) :
    T ≤ Real.sqrt p * pup * pac * Δ := by
  have hsq : Real.sqrt n ≤ Real.sqrt pac * Δ :=
    le_trans (le_mul_of_one_le_left (Real.sqrt_nonneg _) hS1) hS
  have h1 : pup * Real.sqrt (p * pac * n) ≤ Real.sqrt p * pup * pac * Δ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hp0.le]
    have hs := Real.mul_self_sqrt hpac0.le
    calc pup * (Real.sqrt p * Real.sqrt pac * Real.sqrt n)
        = Real.sqrt p * pup * Real.sqrt pac * Real.sqrt n := by ring
      _ ≤ Real.sqrt p * pup * Real.sqrt pac * (Real.sqrt pac * Δ) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = Real.sqrt p * pup * pac * Δ := by
        linear_combination (Real.sqrt p * pup * Δ) * hs
  have h2 : |T / pup| ≤ Real.sqrt (p * pac * n) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_trans hLT hpn)
  have h3 : T ≤ pup * |T / pup| := by
    rw [abs_div, abs_of_pos hpup0, mul_div_cancel₀ _ hpup0.ne']
    exact le_abs_self _
  calc T ≤ pup * |T / pup| := h3
    _ ≤ pup * Real.sqrt (p * pac * n) := mul_le_mul_of_nonneg_left h2 hpup0.le
    _ ≤ _ := h1

/-- The day `⌈A₁ L / q⌉ + ⌈A₄ L⌉` of Proposition 4.4 is at most `(A₁ + max A₄ 0 + 2) L / q` when
`L ≥ 1` and `0 < q ≤ 1`. -/
private lemma lazyFinalAux_ceil_add_le {L q A₁ A₄ : ℝ} (hL1 : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hA₁ : 0 ≤ A₁) :
    (((⌈A₁ * L / q⌉₊ + ⌈A₄ * L⌉₊ : ℕ)) : ℝ) ≤ (A₁ + max A₄ 0 + 2) * L / q := by
  have hL0 : 0 ≤ L := by linarith
  have hLq : L ≤ L / q := le_div_self hL0 hq0 hq1
  have hc1 : (⌈A₁ * L / q⌉₊ : ℝ) < A₁ * L / q + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hc2 : (⌈A₄ * L⌉₊ : ℝ) < max A₄ 0 * L + 1 := by
    have : ⌈A₄ * L⌉₊ ≤ ⌈max A₄ 0 * L⌉₊ :=
      Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left _ _) hL0)
    exact lt_of_le_of_lt (by exact_mod_cast this)
      (Nat.ceil_lt_add_one (mul_nonneg (le_max_right _ _) hL0))
  have hc3 : max A₄ 0 * L ≤ max A₄ 0 * (L / q) :=
    mul_le_mul_of_nonneg_left hLq (le_max_right _ _)
  have hc4 : 1 ≤ L / q := le_trans hL1 hLq
  have e1 : (A₁ + max A₄ 0 + 2) * L / q = A₁ * L / q + max A₄ 0 * (L / q) + 2 * (L / q) := by
    ring
  push_cast
  rw [e1]
  linarith

/-- Absorbing `n^(−c₂ p_up p_ac) + C n^(−p_up p_ac / 2)` into `n^(−c₂' p_up p_ac)`,
`c₂' = min c₂ (1/2) / 2`, once `n^(c₂' p_up p_ac) ≥ 1 + max C 0`. -/
private lemma lazyFinalAux_absorb {n : ℕ} {c₂ pup pac C : ℝ} (hn1 : (1 : ℝ) ≤ n)
    (hq0 : 0 < pup * pac)
    (hpow : 1 + max C 0 ≤ (n : ℝ) ^ (min c₂ (1 / 2) * (pup * pac) / 2)) :
    (n : ℝ) ^ (-(c₂ * pup * pac)) + C * (n : ℝ) ^ (-(pup * pac / 2)) ≤
      (n : ℝ) ^ (-(min c₂ (1 / 2) / 2 * pup * pac)) := by
  have hnpos : (0 : ℝ) < n := by linarith
  set m := min c₂ (1 / 2) with hm
  set y := (n : ℝ) ^ (m * (pup * pac) / 2) with hy
  set z := (n : ℝ) ^ (-(m * (pup * pac) / 2)) with hz
  have hyz : y * z = 1 := by
    rw [hy, hz, Real.rpow_neg hnpos.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hnpos _).ne']
  have hz0 : 0 ≤ z := Real.rpow_nonneg hnpos.le _
  have hzz : (n : ℝ) ^ (-(m * (pup * pac))) = z * z := by
    rw [hz, ← Real.rpow_add hnpos]
    ring_nf
  have hle1 : (n : ℝ) ^ (-(c₂ * pup * pac)) ≤ (n : ℝ) ^ (-(m * (pup * pac))) := by
    apply Real.rpow_le_rpow_of_exponent_le hn1
    have := mul_le_mul_of_nonneg_right (min_le_left c₂ (1 / 2)) hq0.le
    linarith
  have hle2 : (n : ℝ) ^ (-(pup * pac / 2)) ≤ (n : ℝ) ^ (-(m * (pup * pac))) := by
    apply Real.rpow_le_rpow_of_exponent_le hn1
    have := mul_le_mul_of_nonneg_right (min_le_right c₂ (1 / 2)) hq0.le
    linarith
  have hle3 : C * (n : ℝ) ^ (-(pup * pac / 2)) ≤ max C 0 * (n : ℝ) ^ (-(m * (pup * pac))) :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hnpos.le _))
      (mul_le_mul_of_nonneg_left hle2 (le_max_right _ _))
  have e2 : -(m / 2 * pup * pac) = -(m * (pup * pac) / 2) := by ring
  have hyzz : y * (z * z) = z := by rw [← mul_assoc, hyz, one_mul]
  have key := mul_le_mul_of_nonneg_right hpow (mul_nonneg hz0 hz0)
  rw [e2, ← hz]
  rw [hzz] at hle1 hle3
  linarith

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
  classical
  obtain ⟨M₂, S₂, T₂, h42⟩ := proposition4_2 hBE
  obtain ⟨A₃, c₁, hc₁, h43⟩ := proposition4_3 hBBK hBLM
  obtain ⟨A₄, C₄, h44⟩ := proposition4_4
  refine ⟨M₂, fun ε => max (S₂ ε) 1, max A₃ 1 + max A₄ 0 + 2, c₁, hc₁, ?_⟩
  intro ε K lam hε0 hε1 hK hlam
  obtain ⟨c₂, hc₂, h43K⟩ := h43 K lam hK hlam
  refine ⟨min c₂ (1 / 2) / 2, by positivity, ?_⟩
  intro pac pup hpac0 hpac1 hpup0 hpup1
  obtain ⟨N₂, h42N⟩ := h42 ε K lam pac pup hε0 hε1 (by linarith) hlam hpac0 hpac1 hpup0 hpup1
  obtain ⟨N₃, h43N⟩ := h43K pac pup hpac0 hpac1 hpup0 hpup1
  obtain ⟨N₄, h44N⟩ := h44 (max A₃ 1) lam pac pup (by positivity) hlam hpac0 hpac1 hpup0 hpup1
  have hq0 : 0 < pup * pac := mul_pos hpup0 hpac0
  have hq1 : pup * pac ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hpup1 hpac0.le
    linarith
  obtain ⟨N₅, hN₅⟩ := lazyFinalAux_eventually (T₂ ε / pup) (1 + max C₄ 0)
    (by positivity : 0 < min c₂ (1 / 2) * (pup * pac) / 2)
  refine ⟨max C₄ 0 + ((max (max N₂ N₃) (max N₄ N₅) : ℕ) : ℝ) ^ (lam / 4), ?_⟩
  intro n p B₀ hp0 hpn hpn' hS hM
  have hn1 : (1 : ℝ) ≤ n := lazyFinalAux_one_le hpn'
  have hnpos : (0 : ℝ) < n := by linarith
  have hp1 : p < 1 := lazyFinalAux_lt_one hpac0 hnpos hpn'
  have hprob0 := lazyProb_nonneg (n := n) (p := p) (pac := pac) (pup := pup)
    (fun G c => ∃ t : ℕ, (t : ℝ) ≤ (max A₃ 1 + max A₄ 0 + 2) * Real.log n / (pup * pac) ∧
      lazyBlueAfter G c B₀ t = ∅)
  have hexp0 : 0 < Real.exp (-(c₁ * K ^ 2 / p)) := Real.exp_pos _
  have hrp0 : 0 ≤ (n : ℝ) ^ (-(min c₂ (1 / 2) / 2 * pup * pac)) := Real.rpow_nonneg hnpos.le _
  by_cases hnN : n < max (max N₂ N₃) (max N₄ N₅)
  · -- small `n`: the claimed bound is not positive
    have h1 := lazyFinalAux_small (C := C₄) hn1 hnN (lam := lam) (by positivity)
    linarith
  · push Not at hnN
    have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hnN
    have hn3 : N₃ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hnN
    have hn4 : N₄ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnN
    have hn5 : N₅ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnN
    obtain ⟨hL1, hLT, hpowC⟩ := hN₅ n hn5
    have hL0 : 0 ≤ Real.log n := by linarith
    -- Proposition 4.2: the first day fails with probability at most `ε`; its hypothesis
    -- `T_ε ≤ p^(1/2) p_up p_ac Δ` holds for large `n`
    have hS₂ : S₂ ε * Real.sqrt n ≤ Real.sqrt pac * ((n : ℝ) / 2 - B₀.ncard) :=
      le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) hS
    have hlogle : Real.log n ≤ p * pac * n := by
      have := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ 1 + lam) hL0
      linarith
    have hT₂ : T₂ ε ≤ Real.sqrt p * pup * pac * ((n : ℝ) / 2 - B₀.ncard) :=
      lazyFinalAux_hypT hp0 hpac0 hpup0 (le_max_right _ _) hS hlogle hLT
    have h42n := h42N n hn2 p B₀ hp0 hpn hpn' hS₂ hT₂ hM
    have hE₂ : lazyProb n p pac pup (fun G c =>
        ¬ (((lazyBlueAfter G c B₀ 1).ncard : ℝ) ≤ n / 2 - K * Real.sqrt (n / (p * pac)))) ≤ ε := by
      have h := lazyFinalAux_lazyProb_not (n := n) (p := p) (pac := pac) (pup := pup) 0
        (fun G c => ((lazyBlueAfter G c B₀ 1).ncard : ℝ) ≤ n / 2 - K * Real.sqrt (n / (p * pac)))
        (fun G d => ((lazyStep G (actSet d) (updSet d) B₀).ncard : ℝ) ≤
          n / 2 - K * Real.sqrt (n / (p * pac)))
        (fun G c => Iff.rfl)
      rw [h]
      linarith
    -- Proposition 4.3
    have h43n := h43N n hn3 p B₀ hp0 hpn hpn'
    -- Proposition 4.4, with `A₁ = max A₃ 1`
    have h44n := h44N n hn4 p B₀ hp0 hp1.le hpn
    -- the day `T` of Proposition 4.4 is within the claimed time
    have hTle := lazyFinalAux_ceil_add_le (A₄ := A₄) hL1 hq0 hq1
      (by positivity : (0 : ℝ) ≤ max A₃ 1)
    -- the failure event is contained in the failure events of Propositions 4.2, 4.3 and 4.4
    have hfail : lazyProb n p pac pup (fun G c => ¬ ∃ t : ℕ,
        (t : ℝ) ≤ (max A₃ 1 + max A₄ 0 + 2) * Real.log n / (pup * pac) ∧
          lazyBlueAfter G c B₀ t = ∅) ≤
        ε + ((Real.exp (-(c₁ * K ^ 2 / p)) + (n : ℝ) ^ (-(c₂ * pup * pac))) +
          (C₄ * (n : ℝ) ^ (-(lam / 4)) + C₄ * (n : ℝ) ^ (-(pup * pac / 2)))) := by
      refine le_trans (lazyProb_mono ?_) (le_trans (lazyProb_or_le _ _)
        (add_le_add hE₂ (le_trans (lazyProb_or_le _ _) (add_le_add h43n h44n))))
      intro G c hG
      have hT : lazyBlueAfter G c B₀
          (⌈max A₃ 1 * Real.log n / (pup * pac)⌉₊ + ⌈A₄ * Real.log n⌉₊) ≠ ∅ :=
        fun h => hG ⟨_, hTle, h⟩
      by_cases h₂ : ((lazyBlueAfter G c B₀ 1).ncard : ℝ) ≤ n / 2 - K * Real.sqrt (n / (p * pac))
      · right
        by_cases h₃ : ∀ t : ℕ, (t : ℝ) ≤ A₃ * Real.log n / (pup * pac) →
            alphaDeg lam * Real.log n / 2 < (lazyBlueAfter G c B₀ t).ncard
        · exact Or.inl ⟨h₂, h₃⟩
        · right
          push Not at h₃
          obtain ⟨t, ht, ht'⟩ := h₃
          refine ⟨⟨t, le_trans ht ?_, ht'⟩, hT⟩
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hL0) hq0.le
      · exact Or.inl h₂
    -- absorbing the error terms
    have habs := lazyFinalAux_absorb hn1 hq0 hpowC
    have hC4 := lazyFinalAux_le_C (C := C₄) (N := max (max N₂ N₃) (max N₄ N₅)) (lam := lam)
      hnpos
    have := le_lazyProb_of_not_le hfail
    linarith

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
  obtain ⟨M, S, A, c₁, hc₁, h41⟩ := theorem4_1 hBE hBBK hBLM
  -- `K ≥ 8` with `e^(−c₁ K²) ≤ ε / 2`
  have hK8 : (8 : ℝ) ≤ max 8 (Real.log (2 / ε) / c₁) := le_max_left _ _
  obtain ⟨c₂, hc₂, h41ε⟩ := h41 (ε / 2) (max 8 (Real.log (2 / ε) / c₁)) lam (by positivity)
    (by linarith) hK8 hlam
  obtain ⟨C₁, hC₁⟩ := h41ε pac pup hpac0 hpac1 hpup0 hpup1
  refine ⟨M (max 8 (Real.log (2 / ε) / c₁)) / (pup * pac ^ 2), S (ε / 2) / Real.sqrt pac,
    A / (pup * pac), C₁, c₂ * pup * pac, by positivity, ?_⟩
  intro n p B₀ hp0 hpn hpn' hC hS
  set K := max 8 (Real.log (2 / ε) / c₁) with hK
  have hn0 : (0 : ℝ) < n := by linarith [lazyFinalAux_one_le hpn']
  have hp1 : p < 1 := lazyFinalAux_lt_one hpac0 hn0 hpn'
  -- `e^(−c₁ K² / p) ≤ e^(−c₁ K²) ≤ ε / 2`, since `0 < p < 1`
  have hexp : Real.exp (-(c₁ * K ^ 2 / p)) ≤ ε / 2 := by
    have h1 : Real.log (2 / ε) ≤ c₁ * K ^ 2 := by
      have hK1 : K ≤ K ^ 2 := by nlinarith
      have hKl : Real.log (2 / ε) / c₁ ≤ K := le_max_right _ _
      have : Real.log (2 / ε) ≤ c₁ * K := by
        rw [div_le_iff₀ hc₁] at hKl
        linarith
      nlinarith
    have h2 : c₁ * K ^ 2 ≤ c₁ * K ^ 2 / p := le_div_self (by positivity) hp0 hp1.le
    calc Real.exp (-(c₁ * K ^ 2 / p)) ≤ Real.exp (-Real.log (2 / ε)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = ε / 2 := by
          rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have hM : M K ≤ p * pup * pac ^ 2 * ((n : ℝ) / 2 - B₀.ncard) := by
    have hpos : 0 < pup * pac ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hC hpos.le
    rw [div_mul_cancel₀ _ hpos.ne'] at this
    linarith
  have hS' : S (ε / 2) * Real.sqrt n ≤ Real.sqrt pac * ((n : ℝ) / 2 - B₀.ncard) := by
    have hs : 0 < Real.sqrt pac := Real.sqrt_pos.mpr hpac0
    have := mul_le_mul_of_nonneg_left hS hs.le
    calc S (ε / 2) * Real.sqrt n =
          Real.sqrt pac * (S (ε / 2) / Real.sqrt pac * Real.sqrt n) := by
          field_simp
      _ ≤ _ := this
  have h := hC₁ n p B₀ hp0 hpn hpn' hS' hM
  have e : ∀ x : ℝ, A / (pup * pac) * x = A * x / (pup * pac) :=
    fun x => div_mul_eq_mul_div _ _ _
  simp only [e]
  linarith

end PowerOfFew.Sparse

end
