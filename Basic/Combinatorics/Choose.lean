module

public import Mathlib

/-!
# Upper bounds on binomial coefficients

* `Nat.centralBinom_lt_four_pow_div_sqrt`: `C(2m, m) < 2^(2m) / √(2m)` for `m ≥ 1`
  (Matoušek–Nešetřil, *Invitation to Discrete Mathematics*, Proposition 2.6.2, which the dense
  paper cites in the proof of its Lemma 3.2).
* `Nat.choose_le_exp_mul_binEntropy`: `C(n, k) ≤ exp(n H(k / n))`, with `H` the binary entropy in
  nats (the "routine Stirling bound" in the proof of the sparse paper's Lemma 2.3).
-/

@[expose] public section

namespace Nat

/-! ### The central binomial coefficient -/

/-- Matoušek–Nešetřil's identity: with `P = C(2m, m) / 4^m = (1·3···(2m − 1)) / (2·4···2m)`,
`(2m + 1) P² = (1 − 1/2²)(1 − 1/4²)···(1 − 1/(2m)²)`. (Induction on `m`: `P` gets multiplied by
`(2m + 1)/(2m + 2)`, and `(2m + 1)(2m + 3) = (2m + 2)² − 1`.) -/
private lemma two_mul_add_one_mul_sq_centralBinom_div (m : ℕ) :
    (2 * m + 1 : ℝ) * ((centralBinom m : ℝ) / 4 ^ m) ^ 2 =
      ∏ j ∈ Finset.range m, (1 - 1 / (2 * (j : ℝ) + 2) ^ 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ← ih]
    have h : ((m : ℝ) + 1) * centralBinom (m + 1) = 2 * (2 * m + 1) * centralBinom m := by
      exact_mod_cast succ_mul_centralBinom_succ m
    have h' : (centralBinom (m + 1) : ℝ) = 2 * (2 * m + 1) * centralBinom m / (m + 1) := by
      rw [eq_div_iff (by positivity), mul_comm]; exact h
    rw [h']
    push_cast
    field_simp
    ring

/-- `(1 − 1/2²)(1 − 1/4²)···(1 − 1/(2m)²) < 1` for `m ≥ 1`: every factor lies in `[0, 1]`, and the
first one is `3/4`. -/
private lemma prod_one_sub_one_div_sq_lt_one {m : ℕ} (hm : 1 ≤ m) :
    ∏ j ∈ Finset.range m, (1 - 1 / (2 * (j : ℝ) + 2) ^ 2) < 1 := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [Finset.prod_range_succ']
  have hle : ∏ j ∈ Finset.range m, (1 - 1 / (2 * ((j + 1 : ℕ) : ℝ) + 2) ^ 2) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro j _
      have : 1 / (2 * ((j + 1 : ℕ) : ℝ) + 2) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (0 : ℝ) ≤ j := j.cast_nonneg
        push_cast
        nlinarith
      linarith
    · intro j _
      have : 0 ≤ 1 / (2 * ((j + 1 : ℕ) : ℝ) + 2) ^ 2 := by positivity
      linarith
  calc (∏ j ∈ Finset.range m, (1 - 1 / (2 * ((j + 1 : ℕ) : ℝ) + 2) ^ 2)) *
        (1 - 1 / (2 * ((0 : ℕ) : ℝ) + 2) ^ 2)
      ≤ 1 * (1 - 1 / (2 * ((0 : ℕ) : ℝ) + 2) ^ 2) := by gcongr
    _ < 1 := by norm_num

/-- `C(2m, m) < 2^(2m) / √(2m)` for `m ≥ 1` (Matoušek–Nešetřil, *Invitation to Discrete
Mathematics*, 2nd ed., Proposition 2.6.2).

Proof (Matoušek–Nešetřil's): with `P = C(2m, m) / 4^m`,
`(2m + 1) P² = (1 − 1/2²)(1 − 1/4²)···(1 − 1/(2m)²) < 1`, so `P < 1/√(2m + 1) < 1/√(2m)`. -/
theorem centralBinom_lt_four_pow_div_sqrt {m : ℕ} (hm : 1 ≤ m) :
    (centralBinom m : ℝ) < 4 ^ m / Real.sqrt (2 * m) := by
  have hlt := prod_one_sub_one_div_sq_lt_one hm
  rw [← two_mul_add_one_mul_sq_centralBinom_div m, div_pow, ← mul_div_assoc,
    div_lt_one (by positivity)] at hlt
  -- `hlt : (2m + 1) C(2m, m)² < (4^m)²`
  have hm0 : (0 : ℝ) < 2 * m := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [lt_div_iff₀ (Real.sqrt_pos.2 hm0)]
  apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
  rw [mul_pow, Real.sq_sqrt hm0.le]
  nlinarith [sq_nonneg (centralBinom m : ℝ)]

/-! ### The entropy bound -/

/-- Stirling's upper bound `n! ≤ e √n (n/e)^n` for `n ≥ 1`: Mathlib's Stirling sequence
`n! / (√(2n) (n/e)^n)` is decreasing on `n ≥ 1`, and equals `e / √2` at `n = 1`. -/
private lemma factorial_le_exp_one_mul_sqrt_mul_pow {n : ℕ} (hn : n ≠ 0) :
    (n ! : ℝ) ≤ Real.exp 1 * Real.sqrt n * (n / Real.exp 1) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h : Stirling.stirlingSeq (m + 1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  rw [Stirling.stirlingSeq_one, Stirling.stirlingSeq, div_le_iff₀ (by positivity),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
  calc ((m + 1)! : ℝ)
      ≤ Real.exp 1 / Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt ((m + 1 : ℕ) : ℝ) *
          (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1)) := h
    _ = _ := by field_simp

/-- The Stirling bound for `0 < k < n`: `C(n, k) ≤ (n/k)^k (n/(n − k))^(n − k)`. With
`m = n − k`, Stirling's bounds `√(2πj) (j/e)^j ≤ j! ≤ e √j (j/e)^j` give
`C(n, k) = n! / (k! m!) ≤ (e √n / (√(2πk) √(2πm))) (n/k)^k (n/m)^m`, and the constant is at most
`1` because `e² n ≤ 9 · 2km ≤ 4π² km` (as `km ≥ n − 1 ≥ n/2`). -/
private lemma choose_le_div_pow_mul_div_pow {n k : ℕ} (hk0 : 0 < k) (hkn : k < n) :
    (n.choose k : ℝ) ≤ ((n : ℝ) / k) ^ k * ((n : ℝ) / (n - k : ℕ)) ^ (n - k) := by
  obtain ⟨M, hM⟩ : ∃ M, M = n - k := ⟨_, rfl⟩
  rw [← hM]
  have hM0 : 0 < M := by omega
  have hnkM : k + M = n := by omega
  -- Stirling's bounds on `n!`, `k!` and `M!`
  have hn := factorial_le_exp_one_mul_sqrt_mul_pow (n := n) (by omega)
  have hk := Stirling.le_factorial_stirling k
  have hm := Stirling.le_factorial_stirling M
  have hfac : (n.choose k : ℝ) * k ! * M ! = n ! := by
    rw [hM]; exact_mod_cast choose_mul_factorial_mul_factorial hkn.le
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM0
  have hn' : (n : ℝ) = k + M := by rw [← hnkM]; push_cast; ring
  set e := Real.exp 1 with he_def
  set T := ((n : ℝ) / k) ^ k * ((n : ℝ) / M) ^ M with hT_def
  set X := ((k : ℝ) / e) ^ k * ((M : ℝ) / e) ^ M with hX_def
  -- the powers of `e` cancel: `T X = (n/e)^n`
  have hT : T * X = ((n : ℝ) / e) ^ n := by
    calc T * X = ((n : ℝ) / k * (k / e)) ^ k * ((n : ℝ) / M * (M / e)) ^ M := by
          rw [hT_def, hX_def, mul_pow, mul_pow]; ring
      _ = ((n : ℝ) / e) ^ k * ((n : ℝ) / e) ^ M := by
          rw [div_mul_div_cancel₀ hk'.ne', div_mul_div_cancel₀ hM'.ne']
      _ = ((n : ℝ) / e) ^ n := by rw [← pow_add, hnkM]
  have hX : 0 < X := by positivity
  -- the constant: `e √n ≤ √(2πk) √(2πM)`
  have hS : e * Real.sqrt n ≤ Real.sqrt (2 * Real.pi * k) * Real.sqrt (2 * Real.pi * M) := by
    rw [← Real.sqrt_mul (by positivity),
      show e * Real.sqrt n = Real.sqrt (e ^ 2 * n) by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq he.le]]
    apply Real.sqrt_le_sqrt
    have he3 : e < 3 := Real.exp_one_lt_three
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have h9 : e ^ 2 ≤ 9 := by nlinarith
    have hpi2 : 9 ≤ Real.pi ^ 2 := by nlinarith
    have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    have h2 : (1 : ℝ) ≤ M := by exact_mod_cast hM0
    have hkM : (n : ℝ) ≤ 2 * k * M := by rw [hn']; nlinarith
    calc e ^ 2 * n ≤ 9 * (2 * k * M) := by gcongr
      _ ≤ 4 * Real.pi ^ 2 * (k * M) := by nlinarith [mul_pos hk' hM']
      _ = 2 * Real.pi * k * (2 * Real.pi * M) := by ring
  have hSpos : 0 < Real.sqrt (2 * Real.pi * k) * Real.sqrt (2 * Real.pi * M) := by positivity
  have hCX : (n.choose k : ℝ) * (Real.sqrt (2 * Real.pi * k) * Real.sqrt (2 * Real.pi * M)) * X ≤
      e * Real.sqrt n * T * X := by
    calc (n.choose k : ℝ) * (Real.sqrt (2 * Real.pi * k) * Real.sqrt (2 * Real.pi * M)) * X
        = (n.choose k : ℝ) * (Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / e) ^ k) *
            (Real.sqrt (2 * Real.pi * M) * ((M : ℝ) / e) ^ M) := by rw [hX_def]; ring
      _ ≤ (n.choose k : ℝ) * k ! * M ! := by gcongr
      _ = n ! := hfac
      _ ≤ e * Real.sqrt n * ((n : ℝ) / e) ^ n := hn
      _ = e * Real.sqrt n * T * X := by rw [← hT]; ring
  have hC : (n.choose k : ℝ) * (Real.sqrt (2 * Real.pi * k) * Real.sqrt (2 * Real.pi * M)) ≤
      T * (Real.sqrt (2 * Real.pi * k) * Real.sqrt (2 * Real.pi * M)) := by
    have := le_of_mul_le_mul_right hCX hX
    have hT0 : 0 ≤ T := by positivity
    nlinarith
  exact le_of_mul_le_mul_right hC hSpos

/-- `C(n, k) ≤ exp(n H(k / n))`, where `H(x) = −x log x − (1 − x) log(1 − x)` is the binary
entropy.

Proof (the sparse paper's "routine Stirling bound"): for `0 < k < n`,
`exp(n H(k/n)) = (n/k)^k (n/(n − k))^(n − k)`, which bounds `C(n, k)` by Stirling's bounds on the
factorials (`choose_le_div_pow_mul_div_pow`); the cases `k = 0`, `k = n` and `k > n` are
immediate. -/
theorem choose_le_exp_mul_binEntropy (n k : ℕ) :
    (n.choose k : ℝ) ≤ Real.exp (n * Real.binEntropy (k / n)) := by
  rcases Nat.lt_or_ge n k with hnk | hkn
  · rw [Nat.choose_eq_zero_of_lt hnk, Nat.cast_zero]; exact (Real.exp_pos _).le
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  rcases hkn.eq_or_lt with rfl | hkn'
  · have : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
    rw [Nat.choose_self, div_self this, Real.binEntropy_one]; simp
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hk0.trans hkn'
    have hnk : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hkn'
    have hcast : ((n - k : ℕ) : ℝ) = n - k := by rw [Nat.cast_sub hkn'.le]
    have h1 : (1 : ℝ) - k / n = ((n - k : ℕ) : ℝ) / n := by
      rw [hcast]; field_simp
    -- `n H(k/n) = k log(n/k) + (n − k) log(n/(n − k))`
    have hH : (n : ℝ) * Real.binEntropy (k / n) =
        k * Real.log (n / k) + ((n - k : ℕ) : ℝ) * Real.log (n / (n - k : ℕ)) := by
      have e1 : Real.log ((n : ℝ) / k) = -Real.log (k / n) := by rw [← Real.log_inv, inv_div]
      have e2 : Real.log ((n : ℝ) / (n - k : ℕ)) = -Real.log ((n - k : ℕ) / n) := by
        rw [← Real.log_inv, inv_div]
      rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def, h1, e1, e2]
      field_simp
    rw [hH, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by positivity),
      Real.exp_log (by positivity)]
    exact choose_le_div_pow_mul_div_pow hk0 hkn'

end Nat
