module

public import PowerOfFew.Sparse.Main
public import PowerOfFew.Model.Majority

/-!
# Sparse paper, Section 3: below the connectivity threshold

Theorem 3.1 of the sparse paper: for `p = (1 − λ) n⁻¹ log n`, the process becomes periodic, and
the Blue camp ends with at most `(log n)^(O_λ(√(log n))) n^λ` vertices, of average degree
`O_λ(√(pn))`.

Reading: the constants hidden in `O(·)` and `O_λ(·)` may depend on `λ`.

## Proof (the paper's)

Write `q = pn = (1 − λ) log n`.

1. Steps 1–2 of the proof of Theorem 1.2: Lemma 2.1 with `c = 10`, `D = 0.21` gives
   `|B₁| ≤ n/2 − 0.21 min{n, Δ √(pn)} ≤ n/2 − 2.1 n/√(pn)` (as `pΔ ≥ 10` and `pn ≥ 100`), and
   Lemma 2.4 with `a = 2.1`, `b = 1/4` gives `|B₂| ≤ n/4`.
2. Lemma A.7 with `c = a = 1 − λ`: `‖A − EA‖ ≤ C √(pn)`, so `‖A − p𝟏𝟏ᵀ‖ ≤ (C + 1) √(pn)`
   (with `max{C, 0}` for `C`), and Lemma 2.5 with `b = 1/4` gives, for every Blue set `B` of at
   most `n/4` vertices, either `B' = ∅` or `|B'| (avg_{B'} d)² ≤ M pn |B|` (`B'` the next day,
   `M = 12 (C + 1)²`): the paper's Equation (tmp1).
3. Lemma A.5 with `ε = √(2M/(pn))` and `δ = 5 √M (pn)^(-1/2) log(pn)`: every set of at least
   `n^(λ+δ)` vertices has average degree at least `ε pn`.
4. So, from day 2 on, Blue has at most `n/4` vertices (it halves when it has at least
   `n^(λ+δ) ≤ n/4` vertices), falls below `n^(λ+δ)` and stays there (`subconAux_dynamics`).
5. Goles–Olivos (`blueAfter_eventually_period_two`): from some day on the process has period at
   most two; `t*` is the day with the larger of the two alternating Blue sets.
6. Equation (tmp1) for `B_{t*+1}`, whose successor is `B_{t*+2} = B_{t*}`, bounds the average
   degree of `B_{t*}` by `√(M pn)`.
7. `n^(λ+δ) = n^λ e^(δ log n) ≤ (log n)^(K √(log n)) n^λ` (`subconAux_size`).
8. The failure probabilities add up to `O(1/min{n, pΔ²} + n^(−(1−λ)))` (`subconAux_failure`);
   small `n` are absorbed by the constant.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-! ### Numerical facts -/

/-- `Φ₀(1.9) > 0.266`, from `e^(-x²/2) ≥ 1 − x²/2`: `Φ₀(1.9) ≥ (1.9 − 1.9³/6)/√(2π)`. -/
private lemma subconAux_Φ₀_gt : (0.266 : ℝ) < Φ₀ 1.9 := by
  unfold Φ₀
  have hint : ∫ x in (0 : ℝ)..1.9, (1 - x ^ 2 / 2) ≤
      ∫ x in (0 : ℝ)..1.9, Real.exp (-x ^ 2 / 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (by fun_prop : Continuous fun x : ℝ => 1 - x ^ 2 / 2).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun x : ℝ => Real.exp (-x ^ 2 / 2)).intervalIntegrable _ _
    · intro x _
      have := Real.add_one_le_exp (-x ^ 2 / 2)
      linarith
  have hval : ∫ x in (0 : ℝ)..1.9, (1 - x ^ 2 / 2) = 1.9 - 1.9 ^ 3 / 6 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((by fun_prop : Continuous fun x : ℝ => x ^ 2 / 2).intervalIntegrable _ _)]
    norm_num [integral_pow]
  have hpi : Real.sqrt (2 * Real.pi) < 2.6 := by
    rw [Real.sqrt_lt' (by norm_num)]
    nlinarith [Real.pi_lt_d2]
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [hval] at hint
  rw [← div_eq_inv_mul, lt_div_iff₀ hsqrt_pos]
  nlinarith

/-- `D = 0.21 < D_c` for `c = 10` (the proof of Theorem 1.2: "`D = .21 < D_c ≈ .41`"). -/
private lemma subconAux_Dc_gt : (0.21 : ℝ) < Dc 10 := by
  unfold Dc
  have h := subconAux_Φ₀_gt
  have h19 : (2 : ℝ) - 1 / 10 = 1.9 := by norm_num
  rw [h19]
  norm_num
  linarith

/-- The variance coefficient of Lemma 2.1 is at most `3` for `n ≥ 3`. -/
private lemma subconAux_varConst_le {n : ℕ} (hn : 3 ≤ n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    varConst n p ≤ 3 := by
  unfold varConst
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : ((n : ℝ) - 1) / ((n : ℝ) - 2) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have h3 : 0 ≤ ((n : ℝ) - 1) / ((n : ℝ) - 2) := div_nonneg (by linarith) (by linarith)
  have hσ0 : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  have hσ1 : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have h2 : (1 - 2 * (p * (1 - p))) ^ 2 ≤ 1 := by nlinarith
  have h4 : (1 - 2 * (p * (1 - p))) ^ 2 * (((n : ℝ) - 1) / ((n : ℝ) - 2)) ≤ 2 := by
    nlinarith [sq_nonneg (1 - 2 * (p * (1 - p)))]
  nlinarith

/-! ### The spectral bound and Lemma 2.5 -/

/-- `A − p𝟏𝟏ᵀ = (A − EA) − pI`, so `‖A − p𝟏𝟏ᵀ‖ ≤ ‖A − EA‖ + |p|` (proof of Lemma 2.6,
Equation (step3-temp1)). -/
private lemma subconAux_specNorm_le {n : ℕ} (G : SimpleGraph (Fin n)) (p : ℝ) :
    specNorm (adjMat G - p • onesMat n) ≤ specNorm (adjMat G - meanAdj n p) + |p| := by
  have hmat : adjMat G - p • onesMat n =
      (adjMat G - meanAdj n p) - p • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext u v
    simp only [Matrix.sub_apply, Matrix.smul_apply, meanAdj, onesMat, Matrix.of_apply,
      Matrix.one_apply, smul_eq_mul]
    split_ifs <;> ring
  unfold specNorm
  rw [hmat, map_sub, map_smul, map_one]
  refine (norm_sub_le _ _).trans ?_
  gcongr
  rw [norm_smul, Real.norm_eq_abs]
  calc |p| * ‖(1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ |p| * 1 := by
        gcongr; exact ContinuousLinearMap.norm_id_le
    _ = |p| := mul_one _

/-- Lemma 2.5 with `b = 1/4` (so `(1 − b)/(1/2 − b)² = 12`) and `x = p` in the infimum: if
`‖A − EA‖ + |p| ≤ s`, then every Blue set `B` of at most `n/4` vertices either vanishes the next
day or satisfies `(∑_{B'} d)²/|B'| ≤ 12 s² |B|`, where `B'` is the Blue set of the next day. -/
private lemma subconAux_step_bound {n : ℕ} (G : SimpleGraph (Fin n)) {p s : ℝ}
    (hs : specNorm (adjMat G - meanAdj n p) + |p| ≤ s) (B : Set (Fin n))
    (hB : (B.ncard : ℝ) ≤ n / 4) :
    majorityStep G B = ∅ ∨
      (∑ᶠ v ∈ majorityStep G B, (degree G v : ℝ)) ^ 2 / (majorityStep G B).ncard ≤
        12 * s ^ 2 * B.ncard := by
  rcases lemma2_5 G B (b := 1 / 4) (by norm_num) (by linarith) with h | h
  · exact Or.inl h
  · right
    refine h.trans ?_
    have hinf : (⨅ x : ℝ, specNorm (adjMat G - x • onesMat n) ^ 2) ≤ s ^ 2 := by
      refine (ciInf_le ⟨0, ?_⟩ p).trans ?_
      · rintro _ ⟨x, rfl⟩
        positivity
      · have h0 : 0 ≤ specNorm (adjMat G - p • onesMat n) := norm_nonneg _
        exact pow_le_pow_left₀ h0 ((subconAux_specNorm_le G p).trans hs) 2
    have hc : (1 - 1 / 4 : ℝ) / (1 / 2 - 1 / 4) ^ 2 = 12 := by norm_num
    rw [hc]
    have hB0 : (0 : ℝ) ≤ B.ncard := Nat.cast_nonneg _
    calc (⨅ x : ℝ, specNorm (adjMat G - x • onesMat n) ^ 2) * 12 * B.ncard
        = (⨅ x : ℝ, specNorm (adjMat G - x • onesMat n) ^ 2) * (12 * B.ncard) := by ring
      _ ≤ s ^ 2 * (12 * B.ncard) := by gcongr
      _ = 12 * s ^ 2 * B.ncard := by ring

/-! ### The dynamics on a good graph -/

/-- Steps 4–6 of the proof of Theorem 3.1 (deterministic). Assume `|B₂| ≤ n/4`, Equation (tmp1)
of the paper for every Blue set of at most `n/4` vertices (with `L = M pn`), and that every set
of at least `T` vertices (`T = n^(λ+δ) ≤ n/4`) has degree sum at least `e` times its size, where
`e² ≥ 2L` (`e = ε pn`). Then:
* while `|B_{t+1}| ≥ T`, Equation (tmp1) gives `|B_{t+1}| e² ≤ L |B_t|`, so Blue halves;
  otherwise `|B_{t+1}| < T ≤ n/4`. Hence `|B_t| ≤ n/4` for all `t ≥ 2` (the paper leaves this
  implicit: it is what lets Equation (tmp1) be applied every day), Blue falls below `T`, and it
  stays below `T` (a set below `T` cannot double);
* by the period-two theorem, from some day on `B_{t+2} = B_t`; `t*` is the day with the larger
  of the two alternating sets ("without any loss" in the paper);
* Equation (tmp1) for `B_{t*+1}`, whose successor is `B_{t*}`, gives
  `(∑_{B_{t*}} d)² ≤ L |B_{t*+1}| |B_{t*}| ≤ L |B_{t*}|²`. -/
private lemma subconAux_dynamics {n : ℕ} (G : SimpleGraph (Fin n)) (B₀ : Set (Fin n))
    {L e T : ℝ} (hL : 0 < L) (he : 0 ≤ e) (hLe : 2 * L ≤ e ^ 2) (hT : 0 < T)
    (hTn : T ≤ n / 4)
    (hstep : ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ n / 4 → majorityStep G B = ∅ ∨
      (∑ᶠ v ∈ majorityStep G B, (degree G v : ℝ)) ^ 2 / (majorityStep G B).ncard ≤
        L * B.ncard)
    (hdeg : ∀ U : Set (Fin n), T ≤ U.ncard → e * U.ncard ≤ ∑ᶠ u ∈ U, (degree G u : ℝ))
    (h2 : ((blueAfter G B₀ 2).ncard : ℝ) ≤ n / 4) :
    ∃ t₀ : ℕ, (∀ t ≥ t₀, blueAfter G B₀ t = blueAfter G B₀ t₀ ∨
        blueAfter G B₀ t = blueAfter G B₀ (t₀ + 1)) ∧
      (blueAfter G B₀ (t₀ + 1)).ncard ≤ (blueAfter G B₀ t₀).ncard ∧
      ((blueAfter G B₀ t₀).ncard : ℝ) < T ∧
      ∑ᶠ v ∈ blueAfter G B₀ t₀, (degree G v : ℝ) ≤
        Real.sqrt L * (blueAfter G B₀ t₀).ncard := by
  classical
  have hsucc : ∀ t, blueAfter G B₀ (t + 1) = majorityStep G (blueAfter G B₀ t) :=
    fun t => blueAfter_succ G B₀ t
  -- Halving: if `|B_t| ≤ n/4` and `|B_{t+1}| ≥ T`, then `|B_{t+1}| ≤ |B_t|/2`.
  have hhalf : ∀ t, ((blueAfter G B₀ t).ncard : ℝ) ≤ n / 4 →
      T ≤ (blueAfter G B₀ (t + 1)).ncard →
      ((blueAfter G B₀ (t + 1)).ncard : ℝ) ≤ (blueAfter G B₀ t).ncard / 2 := by
    intro t ht hTt
    rw [hsucc] at hTt ⊢
    rcases hstep _ ht with h | h
    · rw [h, Set.ncard_empty, Nat.cast_zero] at hTt
      linarith
    · set k : ℝ := ((majorityStep G (blueAfter G B₀ t)).ncard : ℝ) with hk_def
      set m : ℝ := ((blueAfter G B₀ t).ncard : ℝ) with hm_def
      set S : ℝ := ∑ᶠ v ∈ majorityStep G (blueAfter G B₀ t), (degree G v : ℝ) with hS_def
      have hk : 0 < k := lt_of_lt_of_le hT hTt
      have h1 : e * k ≤ S := hdeg _ hTt
      have h3 : (e * k) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      rw [div_le_iff₀ hk] at h
      have h4 : 2 * L * k ^ 2 ≤ L * m * k := by
        calc 2 * L * k ^ 2 ≤ e ^ 2 * k ^ 2 := by gcongr
          _ = (e * k) ^ 2 := by ring
          _ ≤ S ^ 2 := h3
          _ ≤ L * m * k := h
      nlinarith [mul_pos hL hk]
  -- Every Blue set from day 2 on has at most `n/4` vertices.
  have hinv : ∀ t ≥ 2, ((blueAfter G B₀ t).ncard : ℝ) ≤ n / 4 := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact h2
    | succ t ht ih =>
      by_cases hTt : T ≤ (blueAfter G B₀ (t + 1)).ncard
      · have := hhalf t ih hTt
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      · push Not at hTt
        linarith
  -- Blue eventually has fewer than `T` vertices: otherwise it would halve every day.
  have hsmall : ∃ t₁ ≥ 2, ((blueAfter G B₀ t₁).ncard : ℝ) < T := by
    by_contra hcon
    push Not at hcon
    have hgeom : ∀ k : ℕ, ((blueAfter G B₀ (2 + k)).ncard : ℝ) ≤ n / 4 / 2 ^ k := by
      intro k
      induction k with
      | zero => simpa using h2
      | succ k ih =>
        have h := hhalf (2 + k) (hinv (2 + k) (by omega)) (hcon (2 + k + 1) (by omega))
        calc ((blueAfter G B₀ (2 + (k + 1))).ncard : ℝ)
            = ((blueAfter G B₀ (2 + k + 1)).ncard : ℝ) := rfl
          _ ≤ ((blueAfter G B₀ (2 + k)).ncard : ℝ) / 2 := h
          _ ≤ n / 4 / 2 ^ k / 2 := by gcongr
          _ = n / 4 / 2 ^ (k + 1) := by ring
    have h2n : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
    have hlt : ((blueAfter G B₀ (2 + n)).ncard : ℝ) < 1 := by
      have h1 := hgeom n
      have h3 : (n : ℝ) / 4 / 2 ^ n < 1 := by
        rw [div_lt_one (by positivity)]
        linarith
      linarith
    have h0 : (blueAfter G B₀ (2 + n)).ncard = 0 := by
      have : (blueAfter G B₀ (2 + n)).ncard < 1 := by exact_mod_cast hlt
      omega
    have := hcon (2 + n) (by omega)
    rw [h0, Nat.cast_zero] at this
    linarith
  obtain ⟨t₁, ht₁2, ht₁T⟩ := hsmall
  -- Once below `T`, Blue stays below `T`.
  have hstay : ∀ t ≥ t₁, ((blueAfter G B₀ t).ncard : ℝ) < T := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact ht₁T
    | succ t ht ih =>
      by_contra hcon
      push Not at hcon
      have := hhalf t (hinv t (le_trans ht₁2 ht)) hcon
      have : (0 : ℝ) ≤ (blueAfter G B₀ t).ncard := Nat.cast_nonneg _
      linarith
  -- The period-two theorem of Goles–Olivos and Poljak–Sůra.
  obtain ⟨t₂, ht₂⟩ := blueAfter_eventually_period_two G B₀
  have hper : ∀ s ≥ t₂, ∀ t ≥ s, blueAfter G B₀ t = blueAfter G B₀ s ∨
      blueAfter G B₀ t = blueAfter G B₀ (s + 1) := by
    intro s hs t ht
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      rcases Nat.lt_or_ge t (s + 2) with h | h
      · obtain rfl | rfl : t = s ∨ t = s + 1 := by omega
        · exact Or.inl rfl
        · exact Or.inr rfl
      · have h' : blueAfter G B₀ t = blueAfter G B₀ (t - 2) := by
          have := ht₂ (t - 2) (by omega)
          rwa [Nat.sub_add_cancel (by omega)] at this
        rw [h']
        exact ih (t - 2) (by omega) (by omega)
  -- The average degree in the larger of the two alternating sets: Equation (tmp1) for
  -- `B_{s+1}`, whose successor is `B_{s+2} = B_s`.
  have havg : ∀ s ≥ t₂, 1 ≤ s → (blueAfter G B₀ (s + 1)).ncard ≤ (blueAfter G B₀ s).ncard →
      ∑ᶠ v ∈ blueAfter G B₀ s, (degree G v : ℝ) ≤
        Real.sqrt L * (blueAfter G B₀ s).ncard := by
    intro s hs hs1 hle
    have hstep2 : majorityStep G (blueAfter G B₀ (s + 1)) = blueAfter G B₀ s := by
      rw [← hsucc]
      exact ht₂ s hs
    rcases hstep (blueAfter G B₀ (s + 1)) (hinv (s + 1) (by omega)) with h | h
    · rw [hstep2] at h
      rw [h]
      simp
    · rw [hstep2] at h
      rcases Nat.eq_zero_or_pos (blueAfter G B₀ s).ncard with h0 | h0
      · have : blueAfter G B₀ s = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp h0
        rw [this]
        simp
      · have hk : (0 : ℝ) < (blueAfter G B₀ s).ncard := by exact_mod_cast h0
        have hle' : ((blueAfter G B₀ (s + 1)).ncard : ℝ) ≤ (blueAfter G B₀ s).ncard := by
          exact_mod_cast hle
        set k : ℝ := ((blueAfter G B₀ s).ncard : ℝ) with hk_def
        set S : ℝ := ∑ᶠ v ∈ blueAfter G B₀ s, (degree G v : ℝ) with hS_def
        rw [div_le_iff₀ hk] at h
        have hS2 : S ^ 2 ≤ L * k ^ 2 := by
          calc S ^ 2 ≤ L * ((blueAfter G B₀ (s + 1)).ncard : ℝ) * k := h
            _ ≤ L * k * k := by gcongr
            _ = L * k ^ 2 := by ring
        calc S ≤ |S| := le_abs_self S
          _ = Real.sqrt (S ^ 2) := (Real.sqrt_sq_eq_abs S).symm
          _ ≤ Real.sqrt (L * k ^ 2) := Real.sqrt_le_sqrt hS2
          _ = Real.sqrt L * k := by rw [Real.sqrt_mul hL.le, Real.sqrt_sq hk.le]
  -- The day `t*`: the larger of two consecutive Blue sets after both thresholds.
  set t₀ := max t₁ t₂ with ht₀
  by_cases hcmp : (blueAfter G B₀ (t₀ + 1)).ncard ≤ (blueAfter G B₀ t₀).ncard
  · exact ⟨t₀, hper t₀ (le_max_right _ _), hcmp, hstay t₀ (le_max_left _ _),
      havg t₀ (le_max_right _ _) (by omega) hcmp⟩
  · push Not at hcmp
    have h2' : blueAfter G B₀ (t₀ + 1 + 1) = blueAfter G B₀ t₀ := ht₂ t₀ (le_max_right _ _)
    have hcmp' : (blueAfter G B₀ (t₀ + 1 + 1)).ncard ≤ (blueAfter G B₀ (t₀ + 1)).ncard := by
      rw [h2']
      exact hcmp.le
    exact ⟨t₀ + 1, hper (t₀ + 1) (by omega), hcmp', hstay _ (by omega),
      havg (t₀ + 1) (by omega) (by omega) hcmp'⟩

/-! ### The parameters `δ` and `ε` of Lemma A.5 -/

/-- `δ = 5 √M (pn)^(-1/2) log(pn)` of the proof of Theorem 3.1, as a function of `q = pn`. -/
private def subconAux_δ (M q : ℝ) : ℝ := 5 * Real.sqrt M * Real.log q / Real.sqrt q

/-- `ε = √(2M/(pn))` of the proof of Theorem 3.1, as a function of `q = pn`. -/
private def subconAux_ε (M q : ℝ) : ℝ := Real.sqrt (2 * M / q)

/-- The conditions on `q = pn` that the proof of Theorem 3.1 uses: `pn ≥ 200` (for Lemmas 2.1
and 2.4), and the hypotheses of Lemma A.5 on `δ` and `ε` (`8 ≤ δ q` gives `8 ≤ δ log n`). -/
private def subconAux_Good (lam M q : ℝ) : Prop :=
  200 ≤ q ∧ 0 < subconAux_δ M q ∧ subconAux_δ M q ≤ (1 - lam) / 2 ∧
    8 ≤ subconAux_δ M q * q ∧ 0 < subconAux_ε M q ∧ subconAux_ε M q < 1 ∧
    subconAux_ε M q * Real.log (Real.exp 1 / subconAux_ε M q) ≤ subconAux_δ M q / 4

/-- The conditions of `subconAux_Good` hold for `q = pn` large. The key one is
`ε log(e/ε) ≤ δ/4`: with `ε = √(2M/q)`, `log(e/ε) ≤ 1 + (log q)/2`, and
`√2 (1 + (log q)/2) ≤ (5/4) log q` once `log q ≥ 3` (the ratio tends to `2√2/5 < 1`). -/
private lemma subconAux_good_eventually {lam M : ℝ} (hlam1 : lam < 1) (hM : 12 ≤ M) :
    ∀ᶠ q : ℝ in Filter.atTop, subconAux_Good lam M q := by
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.mpr (by linarith)
  have hc : 0 < (1 - lam) / (10 * Real.sqrt M) := by
    have : 0 < 1 - lam := by linarith
    positivity
  have hlo := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound hc
  filter_upwards [hlo, Filter.eventually_ge_atTop (max (max 200 (2 * M + 1)) (Real.exp 3))]
    with q hq1 hq2
  have hq200 : 200 ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq2
  have hqM : 2 * M + 1 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq2
  have hqe : Real.exp 3 ≤ q := le_trans (le_max_right _ _) hq2
  have hq0 : 0 < q := by linarith
  have hlogq : 3 ≤ Real.log q := by
    rw [Real.le_log_iff_exp_le hq0]; exact hqe
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hsq1 : 1 ≤ Real.sqrt q := Real.one_le_sqrt.mpr (by linarith)
  have hsM1 : 1 ≤ Real.sqrt M := Real.one_le_sqrt.mpr (by linarith)
  have hlog_le : Real.log q ≤ (1 - lam) / (10 * Real.sqrt M) * Real.sqrt q := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ Real.log q by linarith),
      abs_of_nonneg (Real.rpow_nonneg hq0.le _), ← Real.sqrt_eq_rpow] at hq1
    exact hq1
  have hε_pos : 0 < Real.sqrt (2 * M / q) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨hq200, ?_, ?_, ?_, hε_pos, ?_, ?_⟩
  · unfold subconAux_δ
    have : 0 < Real.log q := by linarith
    positivity
  · -- `δ ≤ (1 - λ)/2`, as `log q ≤ (1 − λ)/(10 √M) √q`.
    unfold subconAux_δ
    rw [div_le_iff₀ hsq]
    calc 5 * Real.sqrt M * Real.log q
        ≤ 5 * Real.sqrt M * ((1 - lam) / (10 * Real.sqrt M) * Real.sqrt q) := by gcongr
      _ = (1 - lam) / 2 * Real.sqrt q := by field_simp; ring
  · -- `8 ≤ δ q = 5 √M √q log q`.
    unfold subconAux_δ
    have h1 : 5 * Real.sqrt M * Real.log q / Real.sqrt q * q
        = 5 * Real.sqrt M * Real.log q * Real.sqrt q := by
      rw [div_mul_eq_mul_div, div_eq_iff hsq.ne', mul_assoc _ (Real.sqrt q),
        Real.mul_self_sqrt hq0.le]
    rw [h1]
    have h2 : 3 ≤ Real.sqrt M * Real.log q := by nlinarith
    have h3 : 3 ≤ Real.sqrt M * Real.log q * Real.sqrt q := by nlinarith
    linarith
  · -- `ε < 1`, as `q > 2M`.
    unfold subconAux_ε
    rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one hq0]
    linarith
  · -- `ε log(e/ε) ≤ δ/4`.
    unfold subconAux_ε subconAux_δ
    set ε := Real.sqrt (2 * M / q) with hε
    have hlog_ε : Real.log ε = (Real.log (2 * M) - Real.log q) / 2 := by
      rw [hε, Real.log_sqrt (by positivity), Real.log_div (by positivity) hq0.ne']
    have hlog2M : 0 ≤ Real.log (2 * M) := Real.log_nonneg (by linarith)
    have hlog_e : Real.log (Real.exp 1 / ε) ≤ 1 + Real.log q / 2 := by
      rw [Real.log_div (Real.exp_ne_zero 1) hε_pos.ne', Real.log_exp, hlog_ε]
      linarith
    have hε_eq : ε = Real.sqrt 2 * Real.sqrt M / Real.sqrt q := by
      rw [hε, Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num)]
    have hs2 : Real.sqrt 2 < 1.415 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hkey : Real.sqrt 2 * (1 + Real.log q / 2) ≤ 5 * Real.log q / 4 := by
      nlinarith [Real.sqrt_nonneg 2]
    calc ε * Real.log (Real.exp 1 / ε) ≤ ε * (1 + Real.log q / 2) :=
          mul_le_mul_of_nonneg_left hlog_e hε_pos.le
      _ = Real.sqrt M / Real.sqrt q * (Real.sqrt 2 * (1 + Real.log q / 2)) := by
          rw [hε_eq]; ring
      _ ≤ Real.sqrt M / Real.sqrt q * (5 * Real.log q / 4) := by gcongr
      _ = 5 * Real.sqrt M * Real.log q / Real.sqrt q / 4 := by ring

/-- For `n` large (in terms of `λ`, `M` and `N₀`): `n ≥ N₀`, the conditions `subconAux_Good`
on `pn = (1 − λ) log n`, `n^((1−λ)/2) ≥ 4` (so that `n^(λ+δ) ≤ n/4`) and `log n ≤ 4 n^λ` (so that
Lemma A.5's failure probability is at most `n^(−(1−λ))`). -/
private lemma subconAux_eventually {lam M : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hM : 12 ≤ M) (N₀ : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, N₀ ≤ n ∧ subconAux_Good lam M ((1 - lam) * Real.log n) ∧
      4 ≤ (n : ℝ) ^ ((1 - lam) / 2) ∧ Real.log n ≤ 4 * (n : ℝ) ^ lam := by
  have hn : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hq : Filter.Tendsto (fun n : ℕ => (1 - lam) * Real.log n) Filter.atTop Filter.atTop :=
    (Real.tendsto_log_atTop.comp hn).const_mul_atTop (by linarith)
  have h1 := hq.eventually (subconAux_good_eventually hlam1 hM)
  have h2 := hn.eventually
    ((tendsto_rpow_atTop (by linarith : 0 < (1 - lam) / 2)).eventually_ge_atTop 4)
  have h3 := hn.eventually ((isLittleO_log_rpow_atTop hlam0).bound (by norm_num : (0 : ℝ) < 4))
  filter_upwards [Filter.eventually_ge_atTop N₀, h1, h2, h3] with n hN₀ hgood h4 hlog
  refine ⟨hN₀, hgood, h4, ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) lam)] at hlog
  exact (le_abs_self _).trans hlog

/-- Step 7 of the proof of Theorem 3.1: with `ℓ = log n`, `q = (1 − λ) ℓ = pn` and
`δ = 5 √M q^(-1/2) log q`, we have `δ ℓ = K √ℓ log q ≤ K √ℓ log ℓ` for `K = 5 √M / √(1 − λ)`,
so `n^(λ+δ) = n^λ e^(δ ℓ) ≤ ℓ^(K √ℓ) n^λ`. -/
private lemma subconAux_size {n : ℕ} {lam M : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hn : 0 < (n : ℝ)) (hq : 0 < (1 - lam) * Real.log n) :
    (n : ℝ) ^ (lam + subconAux_δ M ((1 - lam) * Real.log n)) ≤
      Real.log n ^ (5 * Real.sqrt M / Real.sqrt (1 - lam) * Real.sqrt (Real.log n)) *
        (n : ℝ) ^ lam := by
  have hl1 : 0 < 1 - lam := by linarith
  set ℓ : ℝ := Real.log n with hℓ_def
  set q : ℝ := (1 - lam) * ℓ with hq_def
  set K : ℝ := 5 * Real.sqrt M / Real.sqrt (1 - lam) with hK_def
  set δ : ℝ := subconAux_δ M q with hδ_def
  have hℓpos : 0 < ℓ := pos_of_mul_pos_right hq hl1.le
  have hqℓ : q ≤ ℓ := by
    have := mul_nonneg hlam0.le hℓpos.le
    rw [hq_def]
    linarith
  have hsql : 0 < Real.sqrt (1 - lam) := Real.sqrt_pos.mpr hl1
  have hK0 : 0 ≤ K := div_nonneg (by positivity) hsql.le
  rw [Real.rpow_add hn, mul_comm ((n : ℝ) ^ lam)]
  gcongr ?_ * _
  rw [Real.rpow_def_of_pos hn, Real.rpow_def_of_pos hℓpos]
  apply Real.exp_le_exp.mpr
  have hsqℓ : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓpos
  have hsqq : Real.sqrt q = Real.sqrt (1 - lam) * Real.sqrt ℓ := Real.sqrt_mul hl1.le ℓ
  have hℓsq : Real.sqrt ℓ * Real.sqrt ℓ = ℓ := Real.mul_self_sqrt hℓpos.le
  have hlogq : Real.log q ≤ Real.log ℓ := Real.log_le_log hq hqℓ
  have hratio : ℓ / Real.sqrt q = Real.sqrt ℓ / Real.sqrt (1 - lam) := by
    rw [hsqq, div_eq_div_iff (by positivity) hsql.ne']
    linear_combination (-(Real.sqrt (1 - lam))) * hℓsq
  have heq : ℓ * δ = K * Real.sqrt ℓ * Real.log q := by
    have : ℓ * δ = 5 * Real.sqrt M * Real.log q * (ℓ / Real.sqrt q) := by
      rw [hδ_def, subconAux_δ]
      ring
    rw [this, hratio, hK_def]
    ring
  have key : ℓ * δ ≤ Real.log ℓ * (K * Real.sqrt ℓ) := by
    rw [heq]
    calc K * Real.sqrt ℓ * Real.log q ≤ K * Real.sqrt ℓ * Real.log ℓ := by gcongr
      _ = Real.log ℓ * (K * Real.sqrt ℓ) := by ring
  exact key

/-! ### Probabilities -/

/-- Four events with failure probabilities at most `f₁, …, f₄` hold together with probability at
least `1 − (f₁ + f₂ + f₃ + f₄)` (union bound). -/
private lemma subconAux_gnpProb_and4 {n : ℕ} {p : ℝ}
    {P₁ P₂ P₃ P₄ Q : SimpleGraph (Fin n) → Prop} {f₁ f₂ f₃ f₄ : ℝ}
    (h₁ : 1 - f₁ ≤ gnpProb n p P₁) (h₂ : 1 - f₂ ≤ gnpProb n p P₂)
    (h₃ : 1 - f₃ ≤ gnpProb n p P₃) (h₄ : 1 - f₄ ≤ gnpProb n p P₄)
    (himp : ∀ G, P₁ G → P₂ G → P₃ G → P₄ G → Q G) :
    1 - (f₁ + f₂ + f₃ + f₄) ≤ gnpProb n p Q := by
  have a1 := gnpProb_and_ge (n := n) (p := p) P₃ P₄
  have a2 := gnpProb_and_ge (n := n) (p := p) P₂ (fun G => P₃ G ∧ P₄ G)
  have a3 := gnpProb_and_ge (n := n) (p := p) P₁ (fun G => P₂ G ∧ P₃ G ∧ P₄ G)
  have a4 := gnpProb_mono (n := n) (p := p) (P := fun G => P₁ G ∧ P₂ G ∧ P₃ G ∧ P₄ G) (Q := Q)
    (fun G hG => himp G hG.1 hG.2.1 hG.2.2.1 hG.2.2.2)
  linarith

/-- Step 8 of the proof of Theorem 3.1: the four failure probabilities (Lemmas 2.1, 2.4, A.7 and
A.5) add up to at most `C (1/min{n, pΔ²} + n^(−(1−λ)))`. Here `m = min{n, pΔ²}`:
`varConst n p ≤ 3`, `e^(−κn) ≤ 1/(κn) ≤ 1/(κm)`, and Lemma A.5's `n^(−δ n^(λ+δ)/2)` is at most
`n^(−(1−λ))` because `δ n^(λ+δ) ≥ δ n^λ ≥ δ (log n)/4 ≥ 2`. -/
private lemma subconAux_failure {n : ℕ} {lam p m κ δ C : ℝ} (hlam0 : 0 < lam) (hn3 : 3 ≤ n)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hm : 0 < m) (hmn : m ≤ n) (hκ : 0 < κ)
    (hDc : 0.21 < Dc 10) (hC : 3 / (Dc 10 - 0.21) ^ 2 + 1 / κ + 2 ≤ C) (hδ0 : 0 < δ)
    (hδlog : 8 ≤ δ * Real.log n) (hlogn : Real.log n ≤ 4 * (n : ℝ) ^ lam) :
    1 - C * (1 / m + (n : ℝ) ^ (-(1 - lam))) ≤
      1 - (varConst n p / ((Dc 10 - 0.21) ^ 2 * m) + Real.exp (-(κ * n)) +
        (n : ℝ) ^ (-(1 - lam)) + (n : ℝ) ^ (-(δ * (n : ℝ) ^ (lam + δ) / 2))) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) < n := by linarith
  set r : ℝ := (n : ℝ) ^ (-(1 - lam)) with hr_def
  have hr : 0 ≤ r := Real.rpow_nonneg hnpos.le _
  set C₁ : ℝ := 3 / (Dc 10 - 0.21) ^ 2 with hC₁_def
  have hf₁ : varConst n p / ((Dc 10 - 0.21) ^ 2 * m) ≤ C₁ / m := by
    rw [hC₁_def, div_div]
    have : 0 < (Dc 10 - 0.21) ^ 2 * m := by
      have : 0 < Dc 10 - 0.21 := by linarith
      positivity
    gcongr
    exact subconAux_varConst_le hn3 hp0 hp1
  have hf₂ : Real.exp (-(κ * n)) ≤ 1 / κ / m := by
    have h1 : κ * n ≤ Real.exp (κ * n) := by linarith [Real.add_one_le_exp (κ * n)]
    have hκn : 0 < κ * n := mul_pos hκ hnpos
    have hκm : 0 < κ * m := mul_pos hκ hm
    rw [Real.exp_neg]
    calc (Real.exp (κ * n))⁻¹ ≤ (κ * n)⁻¹ := by gcongr
      _ ≤ (κ * m)⁻¹ := by gcongr
      _ = 1 / κ / m := by rw [div_div, one_div]
  have hf₄ : (n : ℝ) ^ (-(δ * (n : ℝ) ^ (lam + δ) / 2)) ≤ r := by
    apply Real.rpow_le_rpow_of_exponent_le hn1
    have hpow : (n : ℝ) ^ lam ≤ (n : ℝ) ^ (lam + δ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have h1 := mul_le_mul_of_nonneg_left hlogn hδ0.le
    have h2 := mul_le_mul_of_nonneg_left hpow hδ0.le
    linarith
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hκ' : 0 ≤ 1 / κ := by positivity
  have hCm : (C₁ + 1 / κ) * (1 / m) ≤ C * (1 / m) := by
    have : 0 ≤ 1 / m := by positivity
    gcongr
    linarith
  have hCr : 2 * r ≤ C * r := mul_le_mul_of_nonneg_right (by linarith) hr
  have e1 : C * (1 / m + r) = C * (1 / m) + C * r := by ring
  have e2 : C₁ / m + 1 / κ / m = (C₁ + 1 / κ) * (1 / m) := by ring
  linarith

/-! ### Theorem 3.1 -/

/-- Steps 1–7 of the proof of Theorem 3.1, on the event where the four lemmas hold: `|B₁|` is
small (Lemma 2.1), every Blue set of at most `n/2 − 2.1 n/√(pn)` vertices has at most `n/4`
vertices the next day (Lemma 2.4), `‖A − EA‖ ≤ C √(pn)` (Lemma A.7), and every set of at least
`n^(λ+δ)` vertices has average degree at least `ε pn` (Lemma A.5). Then `|B₂| ≤ n/4`;
`‖A − p𝟏𝟏ᵀ‖ ≤ ‖A − EA‖ + p ≤ (C + 1) √(pn)`, so Lemma 2.5 (with `b = 1/4`) gives Equation
(tmp1) of the paper with `M = 12 (C + 1)²`; `(ε pn)² = 2 M pn`; and `subconAux_dynamics` does
the rest. -/
private lemma subconAux_event {n : ℕ} (G : SimpleGraph (Fin n)) (B₀ : Set (Fin n))
    {lam p Δ M CA δ ε K : ℝ} (hn : 0 < (n : ℝ)) (hp0 : 0 < p) (hp_half : p ≤ 1 / 2)
    (hpn : p * n = (1 - lam) * Real.log n) (hq200 : 200 ≤ (1 - lam) * Real.log n)
    (hΔ : 10 ≤ p * Δ) (hM : M = 12 * (max CA 0 + 1) ^ 2) (hε0 : 0 ≤ ε)
    (hε2 : ε ^ 2 = 2 * M / ((1 - lam) * Real.log n)) (hK : Real.sqrt M ≤ K)
    (hTn : (n : ℝ) ^ (lam + δ) ≤ n / 4)
    (hsize : (n : ℝ) ^ (lam + δ) ≤ Real.log n ^ (K * Real.sqrt (Real.log n)) * (n : ℝ) ^ lam)
    (h1 : ((blueAfter G B₀ 1).ncard : ℝ) ≤ n / 2 - 0.21 * min (n : ℝ) (Δ * Real.sqrt (p * n)))
    (h2 : ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ n / 2 - 2.1 * n / Real.sqrt (p * n) →
      ((majorityStep G B).ncard : ℝ) ≤ 1 / 4 * n)
    (h3 : specNorm (adjMat G - meanAdj n p) ≤ CA * Real.sqrt (p * n))
    (h4 : ∀ U : Set (Fin n), (n : ℝ) ^ (lam + δ) ≤ U.ncard →
      ε * p * n * U.ncard ≤ ∑ᶠ u ∈ U, (degree G u : ℝ)) :
    ∃ t₀ : ℕ, (∀ t ≥ t₀, blueAfter G B₀ t = blueAfter G B₀ t₀ ∨
        blueAfter G B₀ t = blueAfter G B₀ (t₀ + 1)) ∧
      (blueAfter G B₀ (t₀ + 1)).ncard ≤ (blueAfter G B₀ t₀).ncard ∧
      ((blueAfter G B₀ t₀).ncard : ℝ) ≤
        Real.log n ^ (K * Real.sqrt (Real.log n)) * (n : ℝ) ^ lam ∧
      ∑ᶠ v ∈ blueAfter G B₀ t₀, (degree G v : ℝ) ≤
        K * Real.sqrt ((1 - lam) * Real.log n) * (blueAfter G B₀ t₀).ncard := by
  set q : ℝ := (1 - lam) * Real.log n with hq_def
  have hq0 : 0 < q := by linarith
  have hsq10 : 10 ≤ Real.sqrt q := Real.le_sqrt_of_sq_le (by linarith)
  have hsqpos : 0 < Real.sqrt q := by linarith
  have hM0 : 0 < M := by
    have : 0 < (max CA 0 + 1) ^ 2 := by
      have := le_max_right CA 0
      positivity
    linarith
  -- `|B₁| ≤ n/2 − 2.1 n/√(pn)`, because `0.21 min{n, Δ √(pn)} ≥ 2.1 n/√(pn)` when `pΔ ≥ 10`
  -- and `pn ≥ 100` (as in the proof of Theorem 1.2).
  have hcmp : (n : ℝ) / 2 - 0.21 * min (n : ℝ) (Δ * Real.sqrt (p * n)) ≤
      (n : ℝ) / 2 - 2.1 * n / Real.sqrt (p * n) := by
    rw [hpn]
    have h1 : 10 * (n : ℝ) / Real.sqrt q ≤ n := by
      rw [div_le_iff₀ hsqpos]
      have := mul_le_mul_of_nonneg_left hsq10 hn.le
      linarith
    have h2 : 10 * (n : ℝ) / Real.sqrt q ≤ Δ * Real.sqrt q := by
      rw [div_le_iff₀ hsqpos, mul_assoc, Real.mul_self_sqrt hq0.le, ← hpn]
      have := mul_le_mul_of_nonneg_right hΔ hn.le
      linarith
    have h3 := le_min h1 h2
    have h4 : 2.1 * (n : ℝ) / Real.sqrt q = 0.21 * (10 * n / Real.sqrt q) := by ring
    rw [h4]
    linarith [mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 0.21)]
  -- `|B₂| ≤ n/4` (Lemma 2.4).
  have hB2 : ((blueAfter G B₀ 2).ncard : ℝ) ≤ n / 4 := by
    have h21 : blueAfter G B₀ 2 = majorityStep G (blueAfter G B₀ 1) := blueAfter_succ G B₀ 1
    rw [h21]
    have := h2 (blueAfter G B₀ 1) (h1.trans hcmp)
    linarith
  -- `‖A − EA‖ + p ≤ (C + 1) √(pn)` (Lemma A.7, and `p ≤ 1 ≤ √(pn)`).
  have hs : specNorm (adjMat G - meanAdj n p) + |p| ≤ (max CA 0 + 1) * Real.sqrt q := by
    rw [hpn] at h3
    have hCA' : CA * Real.sqrt q ≤ max CA 0 * Real.sqrt q := by
      gcongr
      exact le_max_left _ _
    have hp_le : |p| ≤ Real.sqrt q := by
      rw [abs_of_pos hp0]
      linarith
    have e : (max CA 0 + 1) * Real.sqrt q = max CA 0 * Real.sqrt q + Real.sqrt q := by ring
    linarith
  -- Lemma 2.5 with `b = 1/4`: Equation (tmp1) of the paper, with `M pn`.
  have hstep : ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ n / 4 → majorityStep G B = ∅ ∨
      (∑ᶠ v ∈ majorityStep G B, (degree G v : ℝ)) ^ 2 / (majorityStep G B).ncard ≤
        (M * q) * B.ncard := by
    intro B hB
    have := subconAux_step_bound G hs B hB
    have heq : 12 * ((max CA 0 + 1) * Real.sqrt q) ^ 2 = M * q := by
      rw [mul_pow, Real.sq_sqrt hq0.le, hM]
      ring
    rwa [heq] at this
  -- Lemma A.5: every set of at least `n^(λ+δ)` vertices has degree sum at least `ε pn` times
  -- its size.
  have hdeg : ∀ U : Set (Fin n), (n : ℝ) ^ (lam + δ) ≤ U.ncard →
      (ε * q) * U.ncard ≤ ∑ᶠ u ∈ U, (degree G u : ℝ) := by
    intro U hU
    calc (ε * q) * U.ncard = ε * (p * n) * U.ncard := by rw [hpn]
      _ = ε * p * n * U.ncard := by ring
      _ ≤ _ := h4 U hU
  -- `(ε pn)² = 2 M pn`: the factor `M/(ε² pn)` of the paper is `1/2`.
  have hLe : 2 * (M * q) ≤ (ε * q) ^ 2 := by
    rw [mul_pow, hε2]
    apply le_of_eq
    field_simp
  obtain ⟨t₀, hper, hle, hlt, havg⟩ := subconAux_dynamics G B₀ (L := M * q) (e := ε * q)
    (T := (n : ℝ) ^ (lam + δ)) (mul_pos hM0 hq0) (mul_nonneg hε0 hq0.le) hLe
    (Real.rpow_pos_of_pos hn _) hTn hstep hdeg hB2
  refine ⟨t₀, hper, hle, hlt.le.trans hsize, havg.trans ?_⟩
  rw [Real.sqrt_mul hM0.le]
  gcongr

/-- **Theorem 3.1** (`S:thm:subcon-main`). Let `0 < λ < 1` and consider majority dynamics on
`G(n, p)` with `p = (1 − λ) n⁻¹ log n` and an initial gap `Δ` (`|R₀| = n/2 + Δ`) with `pΔ ≥ 10`.
With probability at least `1 − O(1/min{n, pΔ²} + n^(−(1−λ)))` there is a day `t*` such that
`B_t = B_{t*}` or `B_t = B_{t*+1}` for all `t ≥ t*`,
`|B_{t*+1}| ≤ |B_{t*}| ≤ (log n)^(O_λ(log^(1/2) n)) n^λ`, and the average degree of the vertices of
`B_{t*}` is `O_λ(√(pn))`.

Departure from the paper (a step the paper leaves implicit): to apply Lemma 2.5 on every day from
day 2 on, the proof needs `|B_t| ≤ n/4` for every `t ≥ 2`; the paper does not say so, and the proof
gets it from the paper's own dichotomy (Blue halves while it has at least `n^(λ+δ)` vertices, and
`n^(λ+δ) ≤ n/4`). The failure probability of the average-degree event is the one Lemma A.5 gives,
`n^(−δ n^(λ+δ)/2)`, where the paper writes `e^(−Ω(n^λ))`. -/
theorem theorem3_1 (hBE : ShevtsovaBerryEsseen)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ C K : ℝ, ∀ (n : ℕ) (B₀ : Set (Fin n)),
      10 ≤ (1 - lam) * Real.log n / n * ((n : ℝ) / 2 - B₀.ncard) →
      1 - C * (1 / min (n : ℝ) ((1 - lam) * Real.log n / n * ((n : ℝ) / 2 - B₀.ncard) ^ 2) +
          (n : ℝ) ^ (-(1 - lam))) ≤
        gnpProb n ((1 - lam) * Real.log n / n) (fun G => ∃ t₀ : ℕ,
          (∀ t ≥ t₀, blueAfter G B₀ t = blueAfter G B₀ t₀ ∨
            blueAfter G B₀ t = blueAfter G B₀ (t₀ + 1)) ∧
          (blueAfter G B₀ (t₀ + 1)).ncard ≤ (blueAfter G B₀ t₀).ncard ∧
          ((blueAfter G B₀ t₀).ncard : ℝ) ≤
            Real.log n ^ (K * Real.sqrt (Real.log n)) * (n : ℝ) ^ lam ∧
          ∑ᶠ v ∈ blueAfter G B₀ t₀, (degree G v : ℝ) ≤
            K * Real.sqrt ((1 - lam) * Real.log n) * (blueAfter G B₀ t₀).ncard) := by
  classical
  have hl1 : 0 < 1 - lam := by linarith
  -- Step 2 of the proof of Theorem 1.2: Lemma 2.4 with `a = 2.1` and `b = 1/4`.
  have hab : 3 * Real.log 2 / 2 < (1 / 4 : ℝ) * 2.1 ^ 2 := by
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    linarith
  obtain ⟨κ, hκ, N₁, hN₁⟩ := lemma2_4 (a := 2.1) (b := 1 / 4) (by norm_num) (by norm_num)
    (by norm_num) hab
  -- The spectral bound: Lemma A.7 with `c = a = 1 − λ`.
  obtain ⟨CA, hCA⟩ := lemmaA_7 hl1 hl1
  -- The average degree of large sets: Lemma A.5.
  obtain ⟨N₂, hN₂⟩ := lemmaA_5 hlam0 hlam1
  -- `M = 12 (C + 1)²`, where `12 = (1 − b)/(1/2 − b)²` for `b = 1/4` in Lemma 2.5.
  set M : ℝ := 12 * (max CA 0 + 1) ^ 2 with hM_def
  have hM12 : 12 ≤ M := by
    have : 1 ≤ (max CA 0 + 1) ^ 2 := one_le_pow₀ (by linarith [le_max_right CA 0])
    linarith
  have hDc := subconAux_Dc_gt
  set K : ℝ := 5 * Real.sqrt M / Real.sqrt (1 - lam) with hK_def
  have hsql : 0 < Real.sqrt (1 - lam) := Real.sqrt_pos.mpr hl1
  have hK : Real.sqrt M ≤ K := by
    rw [hK_def, le_div_iff₀ hsql]
    have h1 : Real.sqrt (1 - lam) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
    have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg M)
    linarith [Real.sqrt_nonneg M]
  -- `n` large in terms of `λ` (and of the constants of the lemmas).
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (subconAux_eventually hlam0 hlam1 hM12 (max 3 (max N₁ N₂)))
  set C : ℝ := 3 / (Dc 10 - 0.21) ^ 2 + 1 / κ + 2 + N with hC_def
  refine ⟨C, K, fun n B₀ hΔ => ?_⟩
  have hC₁0 : 0 ≤ 3 / (Dc 10 - 0.21) ^ 2 := by positivity
  have hκ' : 0 ≤ 1 / κ := by positivity
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set ℓ : ℝ := Real.log n with hℓ_def
  set q : ℝ := (1 - lam) * ℓ with hq_def
  set p : ℝ := q / n with hp_def
  set Δ : ℝ := (n : ℝ) / 2 - B₀.ncard with hΔ_def
  have hℓ0 : 0 ≤ ℓ := Real.log_natCast_nonneg n
  have hp0' : 0 ≤ p := div_nonneg (mul_nonneg hl1.le hℓ0) (Nat.cast_nonneg n)
  have hp0 : 0 < p := by
    rcases hp0'.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hΔ
      norm_num at hΔ
  have hnpos : (0 : ℝ) < n := by
    rcases (Nat.cast_nonneg n : (0 : ℝ) ≤ n).lt_or_eq with h | h
    · exact h
    · rw [hp_def, ← h, div_zero] at hp0
      exact absurd hp0 (lt_irrefl 0)
  have hΔpos : 0 < Δ := by
    by_contra h
    push Not at h
    have := mul_nonpos_of_nonneg_of_nonpos hp0.le h
    linarith
  have hm : 0 < min (n : ℝ) (p * Δ ^ 2) := lt_min hnpos (mul_pos hp0 (pow_pos hΔpos 2))
  have hmn : min (n : ℝ) (p * Δ ^ 2) ≤ n := min_le_left _ _
  rcases lt_or_ge n N with hnN | hnN
  · -- Small `n` (absorbed by `C ≥ N`): the claimed lower bound is at most `0`.
    have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN.le
    have hCm : 1 ≤ C / min (n : ℝ) (p * Δ ^ 2) := by
      rw [le_div_iff₀ hm]
      linarith
    have hCr : 0 ≤ C * (n : ℝ) ^ (-(1 - lam)) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hnpos.le _)
    calc 1 - C * (1 / min (n : ℝ) (p * Δ ^ 2) + (n : ℝ) ^ (-(1 - lam)))
        = 1 - C / min (n : ℝ) (p * Δ ^ 2) - C * (n : ℝ) ^ (-(1 - lam)) := by ring
      _ ≤ 0 := by linarith
      _ ≤ _ := gnpProb_nonneg _
  -- Large `n`.
  obtain ⟨hN0', hgood, h4n, hlogn⟩ : max 3 (max N₁ N₂) ≤ n ∧ subconAux_Good lam M q ∧
      4 ≤ (n : ℝ) ^ ((1 - lam) / 2) ∧ ℓ ≤ 4 * (n : ℝ) ^ lam := hN n hnN
  have hn3 : 3 ≤ n := le_trans (le_max_left _ _) hN0'
  have hnN₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN0'
  have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN0'
  obtain ⟨hq200, hδ0, hδ1, hδq, hε0, hε1, hεδ⟩ := hgood
  set δ : ℝ := subconAux_δ M q with hδ_def
  set ε : ℝ := subconAux_ε M q with hε_def
  have hq0 : 0 < q := by linarith
  have hℓpos : 0 < ℓ := pos_of_mul_pos_right hq0 hl1.le
  have hqℓ : q ≤ ℓ := by
    have := mul_nonneg hlam0.le hℓ0
    rw [hq_def]
    linarith
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hpn : p * n = q := div_mul_cancel₀ q hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog_half : ℓ ≤ n / 2 := by
    have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < n / 2)
    rw [Real.log_div hn0 two_ne_zero, ← hℓ_def] at h
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  have hp_half : p ≤ 1 / 2 := by
    rw [hp_def, div_le_iff₀ hnpos]
    linarith
  -- Step 1 of the proof of Theorem 1.2: Lemma 2.1 with `c = 10` and `D = 0.21`.
  have hcn : (10 : ℝ) ≤ Real.sqrt (p * (1 - p) * n) := by
    apply Real.le_sqrt_of_sq_le
    have : p * (1 - p) * n = q * (1 - p) := by rw [← hpn]; ring
    rw [this]
    have h1 : q * (1 / 2) ≤ q * (1 - p) := mul_le_mul_of_nonneg_left (by linarith) hq0.le
    norm_num
    linarith
  have P1 := lemma2_1 hBE (n := n) (p := p) (Δ := Δ) (c := 10) (D := 0.21) hp0 (by linarith)
    (by norm_num) hΔ hcn (by norm_num) hDc (B₀ := B₀) (by linarith)
  -- Step 2 of the proof of Theorem 1.2: Lemma 2.4 (with `a = 2.1` and `b = 1/4`).
  have hsq10 : 10 ≤ Real.sqrt q := Real.le_sqrt_of_sq_le (by linarith)
  have h2sqrt : 2 * Real.sqrt p ≤ 2.1 := by
    have : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
    linarith
  have hb : (1 / 4 : ℝ) ≤ 1 / 2 - 2.1 / Real.sqrt (p * n) := by
    rw [hpn]
    have : 2.1 / Real.sqrt q ≤ 0.21 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  have P2 := hN₁ n hnN₁ p hp0 (by linarith) h2sqrt hb
  -- Lemma A.7 (with `c = a = 1 − λ`).
  have P3 := hCA n p hp0 (by linarith) (le_of_eq hpn.symm)
  -- Lemma A.5 with `δ = 5 √M (pn)^(-1/2) log(pn)` and `ε = √(2M/(pn))`.
  have hδlog : 8 ≤ δ * ℓ := le_trans hδq (mul_le_mul_of_nonneg_left hqℓ hδ0.le)
  have P4 : 1 - (n : ℝ) ^ (-(δ * (n : ℝ) ^ (lam + δ) / 2)) ≤
      gnpProb n p (fun G => ∀ U : Set (Fin n), (n : ℝ) ^ (lam + δ) ≤ U.ncard →
        ε * p * n * U.ncard ≤ ∑ᶠ u ∈ U, (degree G u : ℝ)) :=
    hN₂ n hnN₂ δ ε hδ0 hδ1 hδlog hε0 hε1 hεδ
  -- `n^(λ+δ) ≤ n/4`, since `λ + δ ≤ (1 + λ)/2` and `n^((1−λ)/2) ≥ 4`.
  have hTn : (n : ℝ) ^ (lam + δ) ≤ n / 4 := by
    have h1 : (n : ℝ) ^ (lam + δ) ≤ (n : ℝ) ^ ((1 + lam) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have h2 : (n : ℝ) ^ ((1 + lam) / 2) * (n : ℝ) ^ ((1 - lam) / 2) = n := by
      rw [← Real.rpow_add hnpos, show (1 + lam) / 2 + (1 - lam) / 2 = 1 by ring,
        Real.rpow_one]
    have h3 : 0 ≤ (n : ℝ) ^ ((1 + lam) / 2) := Real.rpow_nonneg hnpos.le _
    have h4 := mul_le_mul_of_nonneg_left h4n h3
    linarith
  have hε2 : ε ^ 2 = 2 * M / q := Real.sq_sqrt (div_nonneg (by linarith) hq0.le)
  refine le_trans ?_ (subconAux_gnpProb_and4 P1 P2 P3 P4 ?_)
  · exact subconAux_failure hlam0 hn3 hp0.le (by linarith) hm hmn hκ hDc (by linarith) hδ0
      hδlog hlogn
  · intro G h1 h2 h3 h4
    exact subconAux_event G B₀ hnpos hp0 hp_half hpn hq200 hΔ hM_def hε0.le hε2 hK hTn
      (subconAux_size hlam0 hlam1 hnpos hq0) h1 h2 h3 h4

end PowerOfFew.Sparse

end
