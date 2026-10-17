module

public import PowerOfFew.Sparse.DayOne
public import PowerOfFew.Sparse.DayTwo
public import PowerOfFew.Sparse.DayThree

/-!
# Sparse paper: Theorem 1.2, the power of few for sparse graphs

Reading of the asymptotic notation: `λ > 0` is a constant, and the constants hidden in `O(·)` (the
time bound and the failure probability) may depend on it, as they do in the paper's proof
(Lemmas 2.6 and A.4 take `n` large in terms of `λ`). `Δ = n/2 − |B₀|`, so that `|R₀| = n/2 + Δ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-! ### Helpers for Theorem 1.2 -/

/-- `∫₀^{5/3} e^{−x²/2} dx ≥ 4105/3888`: on `[0, 2]`, `e^{−x²/2} = (e^{−x²/4})² ≥ (1 − x²/4)²`,
whose integral over `[0, 5/3]` is `5/3 − (5/3)³/6 + (5/3)⁵/80 = 4105/3888`. -/
private theorem mainAux_integral_ge :
    (4105 / 3888 : ℝ) ≤ ∫ x in (0 : ℝ)..(5 / 3), Real.exp (-x ^ 2 / 2) := by
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) (5 / 3),
      HasDerivAt (fun x : ℝ => x - x ^ 3 / 6 + x ^ 5 / 80) ((1 - x ^ 2 / 4) ^ 2) x := by
    intro x _
    have h := ((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
      ((hasDerivAt_pow 5 x).div_const 80)
    have e : (1 - x ^ 2 / 4) ^ 2 =
        1 - ((3 : ℕ) : ℝ) * x ^ (3 - 1) / 6 + ((5 : ℕ) : ℝ) * x ^ (5 - 1) / 80 := by
      norm_num
      ring
    rw [e]
    exact h
  have hint : ∫ x in (0 : ℝ)..(5 / 3), (1 - x ^ 2 / 4) ^ 2 = 4105 / 3888 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    norm_num
  rw [← hint]
  refine intervalIntegral.integral_mono_on (by norm_num)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) fun x hx => ?_
  have h1 : 0 ≤ 1 - x ^ 2 / 4 := by nlinarith [hx.1, hx.2]
  have h2 : 1 - x ^ 2 / 4 ≤ Real.exp (-x ^ 2 / 4) := by
    have := Real.add_one_le_exp (-x ^ 2 / 4)
    linarith
  have h3 : Real.exp (-x ^ 2 / 2) = Real.exp (-x ^ 2 / 4) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h3]
  exact pow_le_pow_left₀ h1 h2 2

/-- `D₃ = Φ₀(5/3) − 0.56/3 > 0.21` (numerically `D₃ ≈ 0.2655`): `Φ₀(5/3) ≥ (4105/3888)/√(2π)` and
`√(2π) < 2.51`. -/
private theorem mainAux_Dc_three : (0.21 : ℝ) < Dc 3 := by
  have hI := mainAux_integral_ge
  have hpi := Real.pi_lt_d2
  have hs0 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs : Real.sqrt (2 * Real.pi) < 2.51 := by
    rw [Real.sqrt_lt' (by norm_num)]
    nlinarith
  have hI0 : 0 ≤ ∫ x in (0 : ℝ)..(5 / 3), Real.exp (-x ^ 2 / 2) := le_trans (by norm_num) hI
  have h53 : (2 : ℝ) - 1 / 3 = 5 / 3 := by norm_num
  unfold Dc Φ₀
  rw [h53, inv_mul_eq_div]
  have h := div_le_div_of_nonneg_left hI0 hs0 hs.le
  have h' : (4105 / 3888 : ℝ) / 2.51 ≤ (∫ x in (0 : ℝ)..(5 / 3), Real.exp (-x ^ 2 / 2)) / 2.51 :=
    div_le_div_of_nonneg_right hI (by norm_num)
  have hnum : (0.21 : ℝ) + 0.56 / 3 < 4105 / 3888 / 2.51 := by norm_num
  linarith

/-- `varConst n p ≤ 3` for `n ≥ 3` and `0 ≤ p ≤ 1`: `(1 − 2σ²)² ≤ 1` and `(n − 1)/(n − 2) ≤ 2`. -/
private theorem mainAux_varConst_le {n : ℕ} (hn : 3 ≤ n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    varConst n p ≤ 3 := by
  unfold varConst
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : ((n : ℝ) - 1) / ((n : ℝ) - 2) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have h2 : 0 ≤ ((n : ℝ) - 1) / ((n : ℝ) - 2) := div_nonneg (by linarith) (by linarith)
  have hσ0 : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  have hσ1 : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have h3 : (1 - 2 * (p * (1 - p))) ^ 2 ≤ 1 := by nlinarith
  have h5 := mul_le_mul h3 h1 h2 zero_le_one
  nlinarith

/-- The arithmetic of the wrap-up for large `n` (`log n ≥ 100`, hence `pn ≥ 100`): `p < 1`;
`c = 3 ≤ √(p(1 − p)n)` (as `p(1 − p)n ≥ 9`); the hypotheses `2√p ≤ a = 2.1` and
`b = 1/4 ≤ 1/2 − a/√(pn)` of Lemma 2.4; `D min{n, Δ√(pn)} ≥ a n/√(pn)` (as
`D min{√(pn), pΔ} ≥ 0.21 · 10 = 2.1`); and `log n / log(pn) ≥ 1`. -/
private theorem mainAux_large_arith {n : ℕ} {p Δ lam : ℝ} (hlam : 0 < lam) (hp0 : 0 < p)
    (hpn10 : p * n ≤ (n : ℝ) - 10) (hpn : (1 + lam) * Real.log n ≤ p * n) (hΔ : 10 ≤ p * Δ)
    (hlogn : 100 ≤ Real.log n) :
    p < 1 ∧ (3 : ℝ) ≤ Real.sqrt (p * (1 - p) * n) ∧ 2 * Real.sqrt p ≤ 2.1 ∧
      (1 / 4 : ℝ) ≤ 1 / 2 - 2.1 / Real.sqrt (p * n) ∧
      2.1 * n / Real.sqrt (p * n) ≤ 0.21 * min (n : ℝ) (Δ * Real.sqrt (p * n)) ∧
      1 ≤ Real.log n / Real.log (p * n) := by
  have hn10 : (10 : ℝ) < n := by nlinarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hpn100 : 100 ≤ p * n := by nlinarith
  have hp1 : p < 1 := by
    by_contra h
    push Not at h
    nlinarith
  have hs : 10 ≤ Real.sqrt (p * n) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hspos : 0 < Real.sqrt (p * n) := by linarith
  have hsq : Real.sqrt (p * n) ^ 2 = p * n := Real.sq_sqrt (by linarith)
  -- `p(1 − p)n ≥ 9`: if `p ≤ 0.9`, `p(1 − p)n ≥ pn/10 ≥ 10`; otherwise `(1 − p)n ≥ 10`
  have hσ : 9 ≤ p * (1 - p) * n := by
    rcases le_or_gt p 0.9 with h | h
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 0.9 - p) (by linarith : (0 : ℝ) ≤ p * n)]
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ p - 0.9)
        (by linarith : (0 : ℝ) ≤ (1 - p) * n - 10)]
  refine ⟨hp1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  · have : Real.sqrt p ≤ 1 := Real.sqrt_le_one.2 hp1.le
    linarith
  · have : 2.1 / Real.sqrt (p * n) ≤ 0.21 := by
      rw [div_le_iff₀ hspos]
      linarith
    linarith
  · have h1 : 2.1 * n / Real.sqrt (p * n) ≤ 0.21 * n := by
      rw [div_le_iff₀ hspos]
      calc (2.1 : ℝ) * n = 0.21 * n * 10 := by ring
        _ ≤ 0.21 * n * Real.sqrt (p * n) := by gcongr
    have h2 : 2.1 * n / Real.sqrt (p * n) ≤ 0.21 * (Δ * Real.sqrt (p * n)) := by
      rw [div_le_iff₀ hspos]
      calc (2.1 : ℝ) * n = 0.21 * 10 * n := by ring
        _ ≤ 0.21 * (p * Δ) * n := by gcongr
        _ = 0.21 * (Δ * Real.sqrt (p * n)) * Real.sqrt (p * n) := by
          rw [show (0.21 : ℝ) * (Δ * Real.sqrt (p * n)) * Real.sqrt (p * n) =
            0.21 * Δ * Real.sqrt (p * n) ^ 2 by ring, hsq]
          ring
    rw [mul_min_of_nonneg _ _ (by norm_num)]
    exact le_min h1 h2
  · have hlogpn : 0 < Real.log (p * n) := Real.log_pos (by linarith)
    rw [le_div_iff₀ hlogpn, one_mul]
    exact Real.log_le_log (by linarith) (mul_le_of_le_one_left hnpos.le hp1.le)

/-- The failure probability of the wrap-up:
`C₁/min{n, pΔ²} + e^{−κn} + 2n^{−λ/2} ≤ C (1/min{n, pΔ²} + n^{−λ/2})` with `C₁ = 3/(D₃ − D)²`
(`varConst ≤ 3`), `e^{−κn} ≤ 1/(κn)` and `C ≥ C₁ + 1/κ + 2`; `m` stands for `min{n, pΔ²}`. -/
private theorem mainAux_fail {n : ℕ} {p κ lam m C : ℝ} (hn : (3 : ℝ) ≤ n) (hp0 : 0 < p)
    (hp1 : p < 1) (hκ : 0 < κ) (hm0 : 0 < m) (hmn : m ≤ n) (hD3 : (0.21 : ℝ) < Dc 3)
    (hC : 3 / (Dc 3 - 0.21) ^ 2 + 1 / κ + 2 ≤ C) :
    1 - C * (1 / m + (n : ℝ) ^ (-(lam / 2))) ≤
      (1 - varConst n p / ((Dc 3 - 0.21) ^ 2 * m)) + (1 - Real.exp (-(κ * n))) - 1 +
        (1 - 2 * (n : ℝ) ^ (-(lam / 2))) - 1 := by
  have hnpos : (0 : ℝ) < n := by linarith
  have hpow0 : 0 ≤ (n : ℝ) ^ (-(lam / 2)) := Real.rpow_nonneg hnpos.le _
  have hV := mainAux_varConst_le (n := n) (by exact_mod_cast hn) hp0.le hp1.le
  have hD0 : 0 < (Dc 3 - 0.21) ^ 2 := by
    have : 0 < Dc 3 - 0.21 := by linarith
    positivity
  have ha : varConst n p / ((Dc 3 - 0.21) ^ 2 * m) ≤ 3 / (Dc 3 - 0.21) ^ 2 / m := by
    rw [div_div]
    exact div_le_div_of_nonneg_right hV (by positivity)
  have hb : Real.exp (-(κ * n)) ≤ 1 / κ / m := by
    have h1 : κ * n ≤ Real.exp (κ * n) := by linarith [Real.add_one_le_exp (κ * n)]
    have h2 : 0 < κ * n := by positivity
    rw [Real.exp_neg]
    calc (Real.exp (κ * n))⁻¹ ≤ (κ * n)⁻¹ := inv_anti₀ h2 h1
      _ = 1 / κ / n := by field_simp
      _ ≤ 1 / κ / m := div_le_div_of_nonneg_left (by positivity) hm0 hmn
  have hQ0 : 0 ≤ 3 / (Dc 3 - 0.21) ^ 2 + 1 / κ := by positivity
  have h1 : (3 / (Dc 3 - 0.21) ^ 2 + 1 / κ) / m ≤ C / m :=
    div_le_div_of_nonneg_right (by linarith) hm0.le
  have h2 : 2 * (n : ℝ) ^ (-(lam / 2)) ≤ C * (n : ℝ) ^ (-(lam / 2)) :=
    mul_le_mul_of_nonneg_right (by linarith) hpow0
  have hQm : (3 / (Dc 3 - 0.21) ^ 2 + 1 / κ) / m = 3 / (Dc 3 - 0.21) ^ 2 / m + 1 / κ / m :=
    add_div _ _ _
  rw [mul_add, mul_one_div]
  linarith

/-- The deterministic part of the wrap-up: if `|B₁| ≤ n/2 − D min{n, Δ√(pn)}`, if `G` shrinks every
Blue set of at most `n/2 − a n/√(pn)` vertices to at most `n/4` (Lemma 2.4), and if `G` empties
every Blue set of at most `n/4` vertices within `K₆ log n / log(pn)` days (Lemma 2.6), then Red
wins within `2 + K₆ log n / log(pn) ≤ (max{K₆, 0} + 2) log n / log(pn)` days. -/
private theorem mainAux_imp {n : ℕ} (G : SimpleGraph (Fin n)) (B₀ : Set (Fin n)) {p Δ K₆ : ℝ}
    (harith : 2.1 * n / Real.sqrt (p * n) ≤ 0.21 * min (n : ℝ) (Δ * Real.sqrt (p * n)))
    (hratio : 1 ≤ Real.log n / Real.log (p * n)) :
    ((((blueAfter G B₀ 1).ncard : ℝ) ≤ n / 2 - 0.21 * min (n : ℝ) (Δ * Real.sqrt (p * n)) ∧
        ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ n / 2 - 2.1 * n / Real.sqrt (p * n) →
          ((majorityStep G B).ncard : ℝ) ≤ 1 / 4 * n) ∧
        ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ 1 / 4 * n →
          ∃ t : ℕ, (t : ℝ) ≤ K₆ * (Real.log n / Real.log (p * n)) ∧ blueAfter G B t = ∅) →
      ∃ t : ℕ, (t : ℝ) ≤ (max K₆ 0 + 2) * (Real.log n / Real.log (p * n)) ∧
        blueAfter G B₀ t = ∅ := by
  rintro ⟨⟨hE1, hE2⟩, hE3⟩
  -- `|B₁| ≤ n/2 − D min{n, Δ√(pn)} ≤ n/2 − a n/√(pn)`
  have hB1 : ((blueAfter G B₀ 1).ncard : ℝ) ≤ n / 2 - 2.1 * n / Real.sqrt (p * n) :=
    hE1.trans (by linarith)
  -- `|B₂| ≤ n/4` (Lemma 2.4)
  have hB2 : ((blueAfter G B₀ 2).ncard : ℝ) ≤ 1 / 4 * n := by
    rw [blueAfter_succ]
    exact hE2 _ hB1
  -- `B_{2+t} = ∅` (Lemma 2.6)
  obtain ⟨t, ht, hBt⟩ := hE3 _ hB2
  refine ⟨2 + t, ?_, ?_⟩
  · have ht' : (t : ℝ) ≤ max K₆ 0 * (Real.log n / Real.log (p * n)) :=
      ht.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
    push_cast
    linarith
  · rw [blueAfter_add]
    exact hBt

/-- **Theorem 1.2** (`S:thm:main-nonlazy`, the power of few for sparse graphs). Consider a set
`V` of `n` vertices with a partition `V = R ∪ B`, `|R| = n/2 + Δ`, and draw `G ∼ G(n, p)` on `V`.
If `n − 10 ≥ pn ≥ (1 + λ) log n` and `pΔ ≥ 10`, where `λ > 0` is a constant, then majority
dynamics on `G` from `(R, B)` reaches a Red unanimity within time `O(log_{pn} n)` with probability
at least `1 − O(1 / min{n, pΔ²} + n^(−λ/2))`.

Departure from the paper: the paper's wrap-up applies Lemma 2.1 with `c = 10`, claiming
`min{√(p(1 − p)n), pΔ} ≥ 10` for `n` large; this fails for `p` close to `1 − 10/n`, where
`p(1 − p)n` is close to `10`. The proof here takes `c = 3` instead: for `n` large,
`p(1 − p)n ≥ 9` (if `p ≤ 0.9` then `p(1 − p)n ≥ pn/10 ≥ 10`, and otherwise `p(1 − p)n ≥ 0.9 · 10`
since `(1 − p)n ≥ 10`), and `D₃ = Φ₀(5/3) − 0.56/3 ≈ 0.2655` still exceeds the paper's `D = 0.21`.
The rest is the paper's argument: Lemma 2.1 with `D = 0.21`, Lemma 2.4 with `b = 1/4` and the
fixed `a = 2.1 ≤ D min{√(pn), pΔ}` (the paper's `a = D min{√(pn), pΔ}`; for `pn ≥ 100` the set
`|B₁| ≤ n/2 − D min{n, Δ√(pn)}` lies inside `|B₁| ≤ n/2 − 2.1 n/√(pn)`), then Lemma 2.6 with
`b = 1/4`; small `n` are absorbed into the constant. -/
theorem theorem1_2 (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10)
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ C K : ℝ, ∀ (n : ℕ) (p : ℝ) (B₀ : Set (Fin n)), 0 < p →
      p * n ≤ (n : ℝ) - 10 → (1 + lam) * Real.log n ≤ p * n →
      10 ≤ p * ((n : ℝ) / 2 - B₀.ncard) →
      1 - C * (1 / min (n : ℝ) (p * ((n : ℝ) / 2 - B₀.ncard) ^ 2) + (n : ℝ) ^ (-(lam / 2))) ≤
        gnpProb n p (fun G => ∃ t : ℕ,
          (t : ℝ) ≤ K * (Real.log n / Real.log (p * n)) ∧ blueAfter G B₀ t = ∅) := by
  -- Step 2: Lemma 2.4 with `a = 2.1`, `b = 1/4` (`b a² = 1.1025 > 3 log 2 / 2 ≈ 1.04`)
  have hab : 3 * Real.log 2 / 2 < (1 / 4 : ℝ) * 2.1 ^ 2 := by
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    linarith
  obtain ⟨κ, hκ, N₂, h24⟩ := lemma2_4 (a := 2.1) (b := 1 / 4) (by norm_num) (by norm_num)
    (by norm_num) hab
  -- Step 3: Lemma 2.6 with `b = 1/4`
  obtain ⟨K₆, N₆, h26⟩ := lemma2_6 hBBK hBLM (b := 1 / 4) hlam (by norm_num) (by norm_num)
  -- Step 1: Lemma 2.1 with `c = 3` and `D = 0.21 < D₃`
  have hD3 : (0.21 : ℝ) < Dc 3 := mainAux_Dc_three
  -- `n` is large when `n ≥ N`
  obtain ⟨N, hN₂, hN₆, hNexp⟩ : ∃ N : ℕ, N₂ ≤ N ∧ N₆ ≤ N ∧ Real.exp 100 ≤ N :=
    ⟨max (max N₂ N₆) ⌈Real.exp 100⌉₊, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _),
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)⟩
  refine ⟨max (N : ℝ) (3 / (Dc 3 - 0.21) ^ 2 + 1 / κ + 2), max K₆ 0 + 2, ?_⟩
  intro n p B₀ hp0 hpn10 hpn hΔ
  have hn10 : (10 : ℝ) < n := by nlinarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hΔpos : 0 < (n : ℝ) / 2 - B₀.ncard := by
    by_contra h
    push Not at h
    nlinarith
  have hm0 : 0 < min (n : ℝ) (p * ((n : ℝ) / 2 - B₀.ncard) ^ 2) := lt_min hnpos (by positivity)
  have hmn : min (n : ℝ) (p * ((n : ℝ) / 2 - B₀.ncard) ^ 2) ≤ n := min_le_left _ _
  by_cases hnN : N ≤ n
  swap
  · -- small `n`: the bound is trivial, since `C ≥ N > n ≥ min{n, pΔ²}`
    have hnN' : (n : ℝ) < N := by exact_mod_cast not_le.1 hnN
    have hNC : (N : ℝ) ≤ max (N : ℝ) (3 / (Dc 3 - 0.21) ^ 2 + 1 / κ + 2) := le_max_left _ _
    have hC0 : 0 ≤ max (N : ℝ) (3 / (Dc 3 - 0.21) ^ 2 + 1 / κ + 2) := by linarith
    have h1 : 1 ≤ max (N : ℝ) (3 / (Dc 3 - 0.21) ^ 2 + 1 / κ + 2) *
        (1 / min (n : ℝ) (p * ((n : ℝ) / 2 - B₀.ncard) ^ 2)) := by
      rw [mul_one_div, le_div_iff₀ hm0]
      linarith
    have hpow0 : 0 ≤ (n : ℝ) ^ (-(lam / 2)) := Real.rpow_nonneg hnpos.le _
    refine le_trans ?_ (gnpProb_nonneg _)
    have := mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right hpow0 :
        1 / min (n : ℝ) (p * ((n : ℝ) / 2 - B₀.ncard) ^ 2) ≤
          1 / min (n : ℝ) (p * ((n : ℝ) / 2 - B₀.ncard) ^ 2) + (n : ℝ) ^ (-(lam / 2))) hC0
    linarith
  -- large `n`: `log n ≥ 100`, hence `pn ≥ 100`
  have hlogn : 100 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]
    exact hNexp.trans (by exact_mod_cast hnN)
  obtain ⟨hp1, hcn, hsqrtp, hb₁, harith, hratio⟩ :=
    mainAux_large_arith hlam hp0 hpn10 hpn hΔ hlogn
  have hfail := mainAux_fail (lam := lam) (by linarith) hp0 hp1 hκ hm0 hmn hD3
    (le_max_right (N : ℝ) _)
  -- the three events and their probabilities
  have h21 := lemma2_1 hBE (B₀ := B₀) hp0 hp1 (by norm_num : (0 : ℝ) < 3)
    (by linarith : (3 : ℝ) ≤ p * ((n : ℝ) / 2 - B₀.ncard)) hcn (by norm_num : (0 : ℝ) < 0.21)
    hD3 (le_of_eq (by ring))
  have h24' := h24 n (hN₂.trans hnN) p hp0 hp1 hsqrtp hb₁
  have h26' := h26 n (hN₆.trans hnN) p hp0 hp1.le hpn
  -- on the three events Red wins (`mainAux_imp`); union bound over the three failure events
  refine hfail.trans (le_trans ?_ (gnpProb_mono fun G => mainAux_imp G B₀ harith hratio))
  refine le_trans ?_ (gnpProb_and_ge _ _)
  refine le_trans ?_ (sub_le_sub_right (add_le_add (gnpProb_and_ge _ _) le_rfl) _)
  exact sub_le_sub_right (add_le_add (sub_le_sub_right (add_le_add h21 h24') 1) h26') 1

end PowerOfFew.Sparse

end
