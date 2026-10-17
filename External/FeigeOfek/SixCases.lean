module

public import Mathlib

/-!
# Feige and Ofek's bound for the heavy pairs: the six cases

The combinatorial core of the bound on the heavy pairs (Feige–Ofek 2005, Section 2.2; Chin–Rao–Vu
2015, the appendix that proves their heavy-pair lemma), stated on block data.

The coordinates of `x` are grouped into the blocks `S_i = {u : 2^(i−1) < √n |xᵤ| ≤ 2^i}`, `i ∈ ℤ`,
and those of `y` into blocks `T_j`. With `sᵢ = |S_i|`, `tⱼ = |T_j|`, `e_{ij} = e(S_i, T_j)`,
`αᵢ = sᵢ 4^i / n`, `βⱼ = tⱼ 4^j / n`, `μ_{ij} = sᵢ tⱼ d / n`, `λ_{ij} = e_{ij} / μ_{ij}` and
`σ_{ij} = λ_{ij} √d / 2^(i+j)`, the heavy pairs contribute at most
`∑_{2^(i+j) > √d} e_{ij} 2^(i+j) / n = √d ∑ αᵢ βⱼ σ_{ij}`, and `∑ αᵢ ≤ 4`, `∑ βⱼ ≤ 4`. The pairs
`(i, j)` with `sᵢ ≤ tⱼ` fall into six cases, each taken only if the earlier ones fail:

1. `σ_{ij} ≤ 1`: at most `∑ αᵢ βⱼ ≤ 16`;
2. `λ_{ij} ≤ c₂`: then `σ_{ij} ≤ c₂`, at most `16 c₂`;
3. `2^i > √d 2^j`: bounded degrees give `λ_{ij} ≤ c₁ n / tⱼ`, so `βⱼ σ_{ij} ≤ c₁ √d 2^j / 2^i`, a
   geometric sum over `j`: at most `8 c₁`;
4. otherwise the discrepancy property, with `m = tⱼ`, gives
   `σ_{ij} αᵢ log λ_{ij} ≤ c₃ (2^i / (2^j √d)) log(n / tⱼ)`, and
   (a) if `log λ_{ij} > (1/4) log(n / tⱼ)`: `σ_{ij} αᵢ ≤ 4 c₃ 2^i / (2^j √d)`, a geometric sum
       over `i` (as `2^i ≤ √d 2^j`): at most `32 c₃`;
   (b) if not, and `log(n / tⱼ) ≤ 4 log 2^j`: then `λ_{ij} ≤ 2^j`, so `2^i < √d`, and
       `log λ_{ij} ≥ 1`: `σ_{ij} αᵢ ≤ 4 c₃ (2^i / √d) (log 2^j / 2^j) ≤ 4 c₃ 2^i / √d`, a geometric
       sum over `i`: at most `32 c₃`;
   (c) if not, and `log(n / tⱼ) > 4 log 2^j`: then `λ_{ij} ≤ 1 / βⱼ`, so
       `βⱼ σ_{ij} ≤ √d / 2^(i+j)`, a geometric sum over `j`: at most `8`.

The pairs with `tⱼ ≤ sᵢ` are bounded in the same way with the roles of `x` and `y` exchanged (the
pairs with `sᵢ = tⱼ` are counted twice, which only enlarges the bound). In
total the heavy pairs contribute at most `2 (24 + 8 c₁ + 16 c₂ + 64 c₃) √d`.
-/

@[expose] public section

noncomputable section

namespace External.FeigeOfek

/-! ### Geometric sums over finite sets of exponents -/

/-- A sum of distinct powers `2^k`, all with `k < a`, is at most `2^a`. -/
private lemma fo3aAux_sum_zpow_le (K : Finset ℤ) :
    ∀ a : ℤ, (∀ k ∈ K, k < a) → ∑ k ∈ K, (2 : ℝ) ^ k ≤ (2 : ℝ) ^ a := by
  induction K using Finset.induction_on_max with
  | empty => intro a _; simp only [Finset.sum_empty]; positivity
  | insert b K hb ih =>
    intro a ha
    have hbK : b ∉ K := fun h => lt_irrefl b (hb b h)
    rw [Finset.sum_insert hbK]
    have h1 := ih b hb
    have h2 : b < a := ha b (Finset.mem_insert_self b K)
    have h3 : (2 : ℝ) ^ (b + 1) ≤ 2 ^ a := zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [zpow_add_one₀ (two_ne_zero : (2 : ℝ) ≠ 0)] at h3
    linarith

/-- `∑_{k ∈ K, 2^k ≤ r} 2^k ≤ 2 r` for `r > 0`. -/
private lemma fo3aAux_geom_le (K : Finset ℤ) {r : ℝ} (hr : 0 < r) :
    ∑ k ∈ K, (if (2 : ℝ) ^ k ≤ r then (2 : ℝ) ^ k else 0) ≤ 2 * r := by
  induction K using Finset.induction_on_max with
  | empty => simp only [Finset.sum_empty]; linarith
  | insert b K hb ih =>
    have hbK : b ∉ K := fun h => lt_irrefl b (hb b h)
    rw [Finset.sum_insert hbK]
    by_cases hbr : (2 : ℝ) ^ b ≤ r
    · rw [ite_eq_left hbr]
      have h1 : ∑ k ∈ K, (if (2 : ℝ) ^ k ≤ r then (2 : ℝ) ^ k else 0) ≤ ∑ k ∈ K, (2 : ℝ) ^ k :=
        Finset.sum_le_sum fun k _ => by
          split_ifs
          · exact le_rfl
          · positivity
      have h2 := fo3aAux_sum_zpow_le K b hb
      linarith
    · rw [ite_eq_right hbr, zero_add]
      exact ih

/-- `∑_{k ∈ K, 2^k < r} 2^k ≤ 2 r` for `r > 0`. -/
private lemma fo3aAux_geom_lt (K : Finset ℤ) {r : ℝ} (hr : 0 < r) :
    ∑ k ∈ K, (if (2 : ℝ) ^ k < r then (2 : ℝ) ^ k else 0) ≤ 2 * r := by
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) (fo3aAux_geom_le K hr)
  by_cases h : (2 : ℝ) ^ k < r
  · rw [ite_eq_left h, ite_eq_left h.le]
  · rw [ite_eq_right h]
    split_ifs
    · positivity
    · exact le_rfl

/-- A sum of distinct powers `2^(-k)`, all with `k > a`, is at most `2^(-a)`. -/
private lemma fo3aAux_sum_zpow_inv_le (K : Finset ℤ) :
    ∀ a : ℤ, (∀ k ∈ K, a < k) → ∑ k ∈ K, ((2 : ℝ) ^ k)⁻¹ ≤ ((2 : ℝ) ^ a)⁻¹ := by
  induction K using Finset.induction_on_min with
  | empty => intro a _; simp only [Finset.sum_empty]; positivity
  | insert b K hb ih =>
    intro a ha
    have hbK : b ∉ K := fun h => lt_irrefl b (hb b h)
    rw [Finset.sum_insert hbK]
    have h1 := ih b hb
    have h2 : a < b := ha b (Finset.mem_insert_self b K)
    have h3 : (2 : ℝ) ^ (a + 1) ≤ 2 ^ b := zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [zpow_add_one₀ (two_ne_zero : (2 : ℝ) ≠ 0)] at h3
    have h4 := inv_anti₀ (by positivity) h3
    rw [mul_inv] at h4
    linarith

/-- `∑_{k ∈ K, 2^k > r} 2^(-k) ≤ 2 / r` for `r > 0`. -/
private lemma fo3aAux_geom_inv (K : Finset ℤ) {r : ℝ} (hr : 0 < r) :
    ∑ k ∈ K, (if r < (2 : ℝ) ^ k then ((2 : ℝ) ^ k)⁻¹ else 0) ≤ 2 / r := by
  induction K using Finset.induction_on_min with
  | empty => simp only [Finset.sum_empty]; positivity
  | insert b K hb ih =>
    have hbK : b ∉ K := fun h => lt_irrefl b (hb b h)
    rw [Finset.sum_insert hbK]
    by_cases hbr : r < (2 : ℝ) ^ b
    · rw [ite_eq_left hbr]
      have h1 : ∑ k ∈ K, (if r < (2 : ℝ) ^ k then ((2 : ℝ) ^ k)⁻¹ else 0) ≤
          ∑ k ∈ K, ((2 : ℝ) ^ k)⁻¹ :=
        Finset.sum_le_sum fun k _ => by
          split_ifs
          · exact le_rfl
          · positivity
      have h2 := fo3aAux_sum_zpow_inv_le K b hb
      have h3 : ((2 : ℝ) ^ b)⁻¹ < r⁻¹ := inv_strictAnti₀ hr hbr
      rw [div_eq_mul_inv]
      linarith
    · rw [ite_eq_right hbr, zero_add]
      exact ih

/-! ### One block pair: the six cases -/

/-- **The six cases for one block pair**, with `A = 2^i`, `B = 2^j`, `S = sᵢ ≤ T = tⱼ`,
`E = e_{ij}`, `N = n` and `d = q²`, so that `αᵢ = S A² / N`, `βⱼ = T B² / N` and `μ = S T q² / N`. The term
`E A B / N` of a heavy pair (`q < A B`) with `S ≤ T` is at most the sum of the six case bounds:
`(1 + c₂) q αᵢ βⱼ` (cases 1 and 2), `αᵢ c₁ q² B / A` if `q B < A` (case 3),
`βⱼ 4 c₃ A / B` if `A ≤ q B` (case 4(a)), `βⱼ 4 c₃ A` if `A < q` (case 4(b)) and
`αᵢ q² / (A B)` if `q < A B` (case 4(c)); every term is nonnegative. -/
private lemma fo3aAux_pair {N q c₁ c₂ c₃ S T E A B : ℝ} (hN : 0 < N) (hq : 0 < q)
    (hc₁ : 0 ≤ c₁) (hc₂ : Real.exp 1 ≤ c₂) (hc₃ : 0 ≤ c₃) (hS : 1 ≤ S) (hT : 1 ≤ T)
    (hTN : T ≤ N) (hA : 0 < A) (hB : 0 < B) (hE : 0 ≤ E) (hdeg : E ≤ c₁ * (q * q) * S)
    (hdisc : E ≤ c₂ * (S * T * (q * q) / N) ∨
      E * Real.log (E / (S * T * (q * q) / N)) ≤ c₃ * max S T * Real.log (N / max S T)) :
    (if S ≤ T ∧ q < A * B then E * (A * B) / N else 0) ≤
      (1 + c₂) * q * (S * A ^ 2 / N) * (T * B ^ 2 / N) +
      S * A ^ 2 / N * (c₁ * (q * q) / A * (if B < A / q then B else 0) +
        q * q / A * (if q / A < B then B⁻¹ else 0)) +
      T * B ^ 2 / N * (4 * c₃ / B * (if A ≤ q * B then A else 0) +
        4 * c₃ * (if A < q then A else 0)) := by
  have hc₂0 : 0 < c₂ := lt_of_lt_of_le (Real.exp_pos 1) hc₂
  have hS0 : 0 < S := by linarith
  have hT0 : 0 < T := by linarith
  have hα : 0 ≤ S * A ^ 2 / N := by positivity
  have hβ : 0 ≤ T * B ^ 2 / N := by positivity
  have g1 : 0 ≤ (if B < A / q then B else 0) := by split_ifs <;> linarith
  have g2 : 0 ≤ (if q / A < B then B⁻¹ else 0) := by
    split_ifs
    · positivity
    · exact le_rfl
  have g3 : 0 ≤ (if A ≤ q * B then A else 0) := by split_ifs <;> linarith
  have g4 : 0 ≤ (if A < q then A else 0) := by split_ifs <;> linarith
  have hR1 : 0 ≤ (1 + c₂) * q * (S * A ^ 2 / N) * (T * B ^ 2 / N) := by positivity
  have hR2a : 0 ≤ S * A ^ 2 / N * (c₁ * (q * q) / A * (if B < A / q then B else 0)) :=
    mul_nonneg hα (mul_nonneg (by positivity) g1)
  have hR2b : 0 ≤ S * A ^ 2 / N * (q * q / A * (if q / A < B then B⁻¹ else 0)) :=
    mul_nonneg hα (mul_nonneg (by positivity) g2)
  have hR3a : 0 ≤ T * B ^ 2 / N * (4 * c₃ / B * (if A ≤ q * B then A else 0)) :=
    mul_nonneg hβ (mul_nonneg (by positivity) g3)
  have hR3b : 0 ≤ T * B ^ 2 / N * (4 * c₃ * (if A < q then A else 0)) :=
    mul_nonneg hβ (mul_nonneg (by positivity) g4)
  have hsplit : (1 + c₂) * q * (S * A ^ 2 / N) * (T * B ^ 2 / N) +
      S * A ^ 2 / N * (c₁ * (q * q) / A * (if B < A / q then B else 0) +
        q * q / A * (if q / A < B then B⁻¹ else 0)) +
      T * B ^ 2 / N * (4 * c₃ / B * (if A ≤ q * B then A else 0) +
        4 * c₃ * (if A < q then A else 0)) =
      (1 + c₂) * q * (S * A ^ 2 / N) * (T * B ^ 2 / N) +
      S * A ^ 2 / N * (c₁ * (q * q) / A * (if B < A / q then B else 0)) +
      S * A ^ 2 / N * (q * q / A * (if q / A < B then B⁻¹ else 0)) +
      T * B ^ 2 / N * (4 * c₃ / B * (if A ≤ q * B then A else 0)) +
      T * B ^ 2 / N * (4 * c₃ * (if A < q then A else 0)) := by ring
  rw [hsplit]
  by_cases hc : S ≤ T ∧ q < A * B
  swap
  · rw [ite_eq_right hc]
    linarith
  rw [ite_eq_left hc]
  obtain ⟨hST, hheavy⟩ := hc
  have hμ : 0 < S * T * (q * q) / N := by positivity
  -- Case 1: `σ ≤ 1`, that is, the term is at most `q αᵢ βⱼ`.
  by_cases h1 : E * (A * B) / N ≤ q * (S * A ^ 2 / N) * (T * B ^ 2 / N)
  · have h0 : 0 ≤ c₂ * (q * (S * A ^ 2 / N) * (T * B ^ 2 / N)) := by positivity
    have : (1 + c₂) * q * (S * A ^ 2 / N) * (T * B ^ 2 / N) =
        q * (S * A ^ 2 / N) * (T * B ^ 2 / N) + c₂ * (q * (S * A ^ 2 / N) * (T * B ^ 2 / N)) := by
      ring
    linarith
  have h1' := not_le.mp h1
  -- Case 2: `λ ≤ c₂`.
  by_cases h2 : E ≤ c₂ * (S * T * (q * q) / N)
  · have hX : E * (A * B) / N ≤ c₂ * (S * T * (q * q) / N) * (A * B) / N := by gcongr
    have e1 : c₂ * (S * T * (q * q) / N) * (A * B) / N =
        c₂ * S * T * q * A * B / N ^ 2 * q := by ring
    have e2 : (1 + c₂) * q * (S * A ^ 2 / N) * (T * B ^ 2 / N) =
        c₂ * S * T * q * A * B / N ^ 2 * (A * B) + q * (S * A ^ 2 / N) * (T * B ^ 2 / N) := by
      ring
    have h0 : 0 ≤ c₂ * S * T * q * A * B / N ^ 2 := by positivity
    have h0' : 0 ≤ q * (S * A ^ 2 / N) * (T * B ^ 2 / N) := by positivity
    have h5 := mul_le_mul_of_nonneg_left hheavy.le h0
    linarith
  have h2' := not_le.mp h2
  -- Case 3: `2^i > √d 2^j`; bounded degrees.
  by_cases h3 : q * B < A
  · have hif : (if B < A / q then B else 0) = B := ite_eq_left (by rw [lt_div_iff₀ hq]; linarith)
    have : E * (A * B) / N ≤ S * A ^ 2 / N * (c₁ * (q * q) / A * B) := by
      calc E * (A * B) / N ≤ c₁ * (q * q) * S * (A * B) / N := by gcongr
        _ = S * A ^ 2 / N * (c₁ * (q * q) / A * B) := by field_simp
    rw [hif]
    linarith
  have h3' := not_lt.mp h3
  -- Case 4: the discrepancy property, with `m = max(S, T) = T`.
  have hdisc' : E * Real.log (E / (S * T * (q * q) / N)) ≤ c₃ * T * Real.log (N / T) := by
    rcases hdisc with h | h
    · exact absurd h h2
    · rwa [max_eq_right hST] at h
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = E / (S * T * (q * q) / N) := ⟨_, rfl⟩
  rw [← hlam] at hdisc'
  have hlam_gt : c₂ < lam := by rw [hlam, lt_div_iff₀ hμ]; exact h2'
  have hlam_pos : 0 < lam := by linarith
  have hlog1 : 1 ≤ Real.log lam := by
    have := Real.log_le_log (Real.exp_pos 1) (hc₂.trans hlam_gt.le)
    rwa [Real.log_exp] at this
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (N / T) := ⟨_, rfl⟩
  rw [← hL] at hdisc'
  have hL0 : 0 ≤ L := by rw [hL]; exact Real.log_nonneg (by rw [le_div_iff₀ hT0]; linarith)
  by_cases ha : L < 4 * Real.log lam
  · -- Case 4(a): `log λ > (1/4) log(n / tⱼ)`.
    have hE4 : E ≤ 4 * c₃ * T := by
      by_contra hcon
      have hcon' := not_le.mp hcon
      have hlogpos : 0 < Real.log lam := by linarith
      have h6 : c₃ * T * L ≤ c₃ * T * (4 * Real.log lam) :=
        mul_le_mul_of_nonneg_left ha.le (by positivity)
      have h7 := mul_pos (sub_pos.mpr hcon') hlogpos
      nlinarith
    have hif : (if A ≤ q * B then A else 0) = A := ite_eq_left h3'
    have : E * (A * B) / N ≤ T * B ^ 2 / N * (4 * c₃ / B * A) := by
      calc E * (A * B) / N ≤ 4 * c₃ * T * (A * B) / N := by gcongr
        _ = T * B ^ 2 / N * (4 * c₃ / B * A) := by field_simp
    rw [hif]
    linarith
  have ha' := not_lt.mp ha
  by_cases hb : L ≤ 4 * Real.log B
  · -- Case 4(b): `log(n / tⱼ) ≤ 4 log 2^j`, so `λ ≤ 2^j` and `2^i < √d`.
    have hlamB : lam ≤ B := (Real.log_le_log_iff hlam_pos hB).mp (by linarith)
    have hEB : E ≤ B * (S * T * (q * q) / N) := by
      rw [hlam, div_le_iff₀ hμ] at hlamB
      linarith
    have hAq : A < q := by
      by_contra hcon
      have hqA := not_lt.mp hcon
      have h8 : E * (A * B) / N ≤ q * (S * A ^ 2 / N) * (T * B ^ 2 / N) := by
        calc E * (A * B) / N ≤ B * (S * T * (q * q) / N) * (A * B) / N := by gcongr
          _ = S * T * q * A * B ^ 2 / N ^ 2 * q := by ring
          _ ≤ S * T * q * A * B ^ 2 / N ^ 2 * A := by gcongr
          _ = q * (S * A ^ 2 / N) * (T * B ^ 2 / N) := by ring
      linarith
    have hlogB : Real.log B ≤ B := by linarith [Real.log_le_sub_one_of_pos hB]
    have hEle : E ≤ 4 * c₃ * T * B := by
      have h5 : E * 1 ≤ E * Real.log lam := mul_le_mul_of_nonneg_left hlog1 hE
      have h6 : c₃ * T * L ≤ c₃ * T * (4 * B) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have hif : (if A < q then A else 0) = A := ite_eq_left hAq
    have : E * (A * B) / N ≤ T * B ^ 2 / N * (4 * c₃ * A) := by
      calc E * (A * B) / N ≤ 4 * c₃ * T * B * (A * B) / N := by gcongr
        _ = T * B ^ 2 / N * (4 * c₃ * A) := by ring
    rw [hif]
    linarith
  · -- Case 4(c): `log(n / tⱼ) > 4 log 2^j`, so `λ ≤ 1 / βⱼ`.
    have hb' := not_le.mp hb
    have hlogNTB : Real.log (N / T / B ^ 2) = L - 2 * Real.log B := by
      rw [Real.log_div (div_pos hN hT0).ne' (pow_pos hB 2).ne', Real.log_pow, hL]
      push_cast
      ring
    have hlam_le : lam ≤ N / T / B ^ 2 :=
      (Real.log_le_log_iff hlam_pos (by positivity)).mp (by rw [hlogNTB]; linarith)
    have hEle : E ≤ S * (q * q) / B ^ 2 := by
      rw [hlam, div_le_iff₀ hμ] at hlam_le
      calc E ≤ N / T / B ^ 2 * (S * T * (q * q) / N) := hlam_le
        _ = S * (q * q) / B ^ 2 := by field_simp
    have hif : (if q / A < B then B⁻¹ else 0) = B⁻¹ :=
      ite_eq_left (by rw [div_lt_iff₀ hA]; linarith)
    have : E * (A * B) / N ≤ S * A ^ 2 / N * (q * q / A * B⁻¹) := by
      calc E * (A * B) / N ≤ S * (q * q) / B ^ 2 * (A * B) / N := by gcongr
        _ = S * A ^ 2 / N * (q * q / A * B⁻¹) := by field_simp
    rw [hif]
    linarith

/-! ### Summing over the block pairs -/

/-- Summing the bound of `fo3aAux_pair` over the block pairs: if `∑ αᵢ ≤ 4`, `∑ βⱼ ≤ 4`, every row
sum `∑ⱼ F i j` is at most `a` and every column sum `∑ᵢ G i j` at most `b`, then
`∑ᵢ ∑ⱼ (K αᵢ βⱼ + αᵢ F i j + βⱼ G i j) ≤ 16 K + 4 a + 4 b`. -/
private lemma fo3aAux_sum3 (I J : Finset ℤ) (α β : ℤ → ℝ) (F G : ℤ → ℤ → ℝ) {K a b : ℝ}
    (hK : 0 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b) (hα0 : ∀ i ∈ I, 0 ≤ α i) (hβ0 : ∀ j ∈ J, 0 ≤ β j)
    (hα : ∑ i ∈ I, α i ≤ 4) (hβ : ∑ j ∈ J, β j ≤ 4)
    (hF : ∀ i ∈ I, ∑ j ∈ J, F i j ≤ a) (hG : ∀ j ∈ J, ∑ i ∈ I, G i j ≤ b) :
    ∑ i ∈ I, ∑ j ∈ J, (K * α i * β j + α i * F i j + β j * G i j) ≤
      16 * K + 4 * a + 4 * b := by
  simp only [Finset.sum_add_distrib]
  have b1 : ∑ i ∈ I, ∑ j ∈ J, K * α i * β j ≤ 16 * K := by
    calc ∑ i ∈ I, ∑ j ∈ J, K * α i * β j = ∑ i ∈ I, K * α i * ∑ j ∈ J, β j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ I, K * α i * 4 :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left hβ (mul_nonneg hK (hα0 i hi))
      _ = 4 * K * ∑ i ∈ I, α i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ 4 * K * 4 := mul_le_mul_of_nonneg_left hα (by positivity)
      _ = 16 * K := by ring
  have b2 : ∑ i ∈ I, ∑ j ∈ J, α i * F i j ≤ 4 * a := by
    calc ∑ i ∈ I, ∑ j ∈ J, α i * F i j = ∑ i ∈ I, α i * ∑ j ∈ J, F i j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ I, α i * a :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hF i hi) (hα0 i hi)
      _ = (∑ i ∈ I, α i) * a := by rw [Finset.sum_mul]
      _ ≤ 4 * a := mul_le_mul_of_nonneg_right hα ha
  have b3 : ∑ i ∈ I, ∑ j ∈ J, β j * G i j ≤ 4 * b := by
    rw [Finset.sum_comm]
    calc ∑ j ∈ J, ∑ i ∈ I, β j * G i j = ∑ j ∈ J, β j * ∑ i ∈ I, G i j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ J, β j * b :=
          Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hG j hj) (hβ0 j hj)
      _ = (∑ j ∈ J, β j) * b := by rw [Finset.sum_mul]
      _ ≤ 4 * b := mul_le_mul_of_nonneg_right hβ hb
  linarith

/-- **One half of the six cases**: the heavy block pairs with `sᵢ ≤ tⱼ` contribute at most
`(24 + 8 c₁ + 16 c₂ + 64 c₃) √d`. Only the degree bound `e_{ij} ≤ c₁ d sᵢ` is used. -/
private lemma fo3aAux_half {n d c₁ c₂ c₃ : ℝ} (hn : 0 < n) (hd : 0 < d) (hc₁ : 0 ≤ c₁)
    (hc₂ : Real.exp 1 ≤ c₂) (hc₃ : 0 ≤ c₃) (I J : Finset ℤ) (s t : ℤ → ℝ) (e : ℤ → ℤ → ℝ)
    (hs : ∀ i ∈ I, 1 ≤ s i ∧ s i ≤ n) (ht : ∀ j ∈ J, 1 ≤ t j ∧ t j ≤ n)
    (hα : ∑ i ∈ I, s i * 4 ^ i / n ≤ 4) (hβ : ∑ j ∈ J, t j * 4 ^ j / n ≤ 4)
    (he : ∀ i ∈ I, ∀ j ∈ J, 0 ≤ e i j)
    (hdeg : ∀ i ∈ I, ∀ j ∈ J, e i j ≤ c₁ * d * s i)
    (hdisc : ∀ i ∈ I, ∀ j ∈ J, e i j ≤ c₂ * (s i * t j * d / n) ∨
      e i j * Real.log (e i j / (s i * t j * d / n)) ≤
        c₃ * max (s i) (t j) * Real.log (n / max (s i) (t j))) :
    ∑ i ∈ I, ∑ j ∈ J,
        (if s i ≤ t j ∧ Real.sqrt d < (2 : ℝ) ^ (i + j) then e i j * (2 : ℝ) ^ (i + j) / n
          else 0) ≤
      (24 + 8 * c₁ + 16 * c₂ + 64 * c₃) * Real.sqrt d := by
  have h4 : ∀ k : ℤ, (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := fun k => by
    rw [sq, ← mul_zpow]
    norm_num
  simp only [h4] at hα hβ
  have hc₂0 : 0 < c₂ := lt_of_lt_of_le (Real.exp_pos 1) hc₂
  obtain ⟨q, hq_def⟩ : ∃ q, Real.sqrt d = q := ⟨_, rfl⟩
  have hq : 0 < q := by rw [← hq_def]; exact Real.sqrt_pos.mpr hd
  have hqq : q * q = d := by rw [← hq_def]; exact Real.mul_self_sqrt hd.le
  rw [hq_def]
  subst hqq
  have hkey : ∀ i ∈ I, ∀ j ∈ J,
      (if s i ≤ t j ∧ q < (2 : ℝ) ^ (i + j) then e i j * (2 : ℝ) ^ (i + j) / n else 0) ≤
        (1 + c₂) * q * (s i * ((2 : ℝ) ^ i) ^ 2 / n) * (t j * ((2 : ℝ) ^ j) ^ 2 / n) +
        s i * ((2 : ℝ) ^ i) ^ 2 / n *
          (c₁ * (q * q) / (2 : ℝ) ^ i *
              (if (2 : ℝ) ^ j < (2 : ℝ) ^ i / q then (2 : ℝ) ^ j else 0) +
            q * q / (2 : ℝ) ^ i * (if q / (2 : ℝ) ^ i < (2 : ℝ) ^ j then ((2 : ℝ) ^ j)⁻¹ else 0)) +
        t j * ((2 : ℝ) ^ j) ^ 2 / n *
          (4 * c₃ / (2 : ℝ) ^ j * (if (2 : ℝ) ^ i ≤ q * (2 : ℝ) ^ j then (2 : ℝ) ^ i else 0) +
            4 * c₃ * (if (2 : ℝ) ^ i < q then (2 : ℝ) ^ i else 0)) := by
    intro i hi j hj
    rw [zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]
    exact fo3aAux_pair hn hq hc₁ hc₂ hc₃ (hs i hi).1 (ht j hj).1 (ht j hj).2
      (zpow_pos two_pos i) (zpow_pos two_pos j) (he i hi j hj) (hdeg i hi j hj) (hdisc i hi j hj)
  refine le_trans (Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hkey i hi j hj) ?_
  have hα0 : ∀ i ∈ I, 0 ≤ s i * ((2 : ℝ) ^ i) ^ 2 / n := fun i hi => by
    have := (hs i hi).1
    positivity
  have hβ0 : ∀ j ∈ J, 0 ≤ t j * ((2 : ℝ) ^ j) ^ 2 / n := fun j hj => by
    have := (ht j hj).1
    positivity
  have hF : ∀ i ∈ I, ∑ j ∈ J,
      (c₁ * (q * q) / (2 : ℝ) ^ i * (if (2 : ℝ) ^ j < (2 : ℝ) ^ i / q then (2 : ℝ) ^ j else 0) +
        q * q / (2 : ℝ) ^ i * (if q / (2 : ℝ) ^ i < (2 : ℝ) ^ j then ((2 : ℝ) ^ j)⁻¹ else 0)) ≤
      (2 * c₁ + 2) * q := by
    intro i _
    have hA : 0 < (2 : ℝ) ^ i := zpow_pos two_pos i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have g1 := fo3aAux_geom_lt J (r := (2 : ℝ) ^ i / q) (by positivity)
    have g3 := fo3aAux_geom_inv J (r := q / (2 : ℝ) ^ i) (by positivity)
    calc c₁ * (q * q) / (2 : ℝ) ^ i *
            ∑ j ∈ J, (if (2 : ℝ) ^ j < (2 : ℝ) ^ i / q then (2 : ℝ) ^ j else 0) +
          q * q / (2 : ℝ) ^ i *
            ∑ j ∈ J, (if q / (2 : ℝ) ^ i < (2 : ℝ) ^ j then ((2 : ℝ) ^ j)⁻¹ else 0) ≤
          c₁ * (q * q) / (2 : ℝ) ^ i * (2 * ((2 : ℝ) ^ i / q)) +
            q * q / (2 : ℝ) ^ i * (2 / (q / (2 : ℝ) ^ i)) := by gcongr
      _ = (2 * c₁ + 2) * q := by
          field_simp
  have hG : ∀ j ∈ J, ∑ i ∈ I,
      (4 * c₃ / (2 : ℝ) ^ j * (if (2 : ℝ) ^ i ≤ q * (2 : ℝ) ^ j then (2 : ℝ) ^ i else 0) +
        4 * c₃ * (if (2 : ℝ) ^ i < q then (2 : ℝ) ^ i else 0)) ≤ 16 * c₃ * q := by
    intro j _
    have hB : 0 < (2 : ℝ) ^ j := zpow_pos two_pos j
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have g2 := fo3aAux_geom_le I (r := q * (2 : ℝ) ^ j) (by positivity)
    have g4 := fo3aAux_geom_lt I hq
    calc 4 * c₃ / (2 : ℝ) ^ j *
            ∑ i ∈ I, (if (2 : ℝ) ^ i ≤ q * (2 : ℝ) ^ j then (2 : ℝ) ^ i else 0) +
          4 * c₃ * ∑ i ∈ I, (if (2 : ℝ) ^ i < q then (2 : ℝ) ^ i else 0) ≤
          4 * c₃ / (2 : ℝ) ^ j * (2 * (q * (2 : ℝ) ^ j)) + 4 * c₃ * (2 * q) := by gcongr
      _ = 16 * c₃ * q := by
          field_simp
          ring
  calc _ ≤ 16 * ((1 + c₂) * q) + 4 * ((2 * c₁ + 2) * q) + 4 * (16 * c₃ * q) :=
        fo3aAux_sum3 I J (fun i => s i * ((2 : ℝ) ^ i) ^ 2 / n)
          (fun j => t j * ((2 : ℝ) ^ j) ^ 2 / n)
          (fun i j => c₁ * (q * q) / (2 : ℝ) ^ i *
              (if (2 : ℝ) ^ j < (2 : ℝ) ^ i / q then (2 : ℝ) ^ j else 0) +
            q * q / (2 : ℝ) ^ i * (if q / (2 : ℝ) ^ i < (2 : ℝ) ^ j then ((2 : ℝ) ^ j)⁻¹ else 0))
          (fun i j => 4 * c₃ / (2 : ℝ) ^ j *
              (if (2 : ℝ) ^ i ≤ q * (2 : ℝ) ^ j then (2 : ℝ) ^ i else 0) +
            4 * c₃ * (if (2 : ℝ) ^ i < q then (2 : ℝ) ^ i else 0))
          (by positivity) (by positivity) (by positivity) hα0 hβ0 hα hβ hF hG
    _ = (24 + 8 * c₁ + 16 * c₂ + 64 * c₃) * q := by ring

/-- **The six cases of Feige and Ofek**, on block data. Let `I, J ⊆ ℤ` be finite sets of block
indices, `s, t` the block sizes (between `1` and `n`) and `e` the block edge counts, with
`∑_{i ∈ I} sᵢ 4^i / n ≤ 4` and `∑_{j ∈ J} tⱼ 4^j / n ≤ 4` (the vectors have norm at most `1`),
`e_{ij} ≤ c₁ d min(sᵢ, tⱼ)` (bounded degrees), and, for every pair, `e_{ij} ≤ c₂ μ_{ij}` or
`e_{ij} log(e_{ij} / μ_{ij}) ≤ c₃ m log(n / m)` with `μ_{ij} = sᵢ tⱼ d / n` and `m = max(sᵢ, tⱼ)`
(discrepancy). Then the block pairs with `2^(i+j) > √d` contribute
`∑ e_{ij} 2^(i+j) / n ≤ 2 (24 + 8 c₁ + 16 c₂ + 64 c₃) √d`. -/
theorem sum_blocks_le {n d c₁ c₂ c₃ : ℝ} (hn : 0 < n) (hd : 0 < d) (hc₁ : 0 ≤ c₁)
    (hc₂ : Real.exp 1 ≤ c₂) (hc₃ : 0 ≤ c₃) (I J : Finset ℤ) (s t : ℤ → ℝ) (e : ℤ → ℤ → ℝ)
    (hs : ∀ i ∈ I, 1 ≤ s i ∧ s i ≤ n) (ht : ∀ j ∈ J, 1 ≤ t j ∧ t j ≤ n)
    (hα : ∑ i ∈ I, s i * 4 ^ i / n ≤ 4) (hβ : ∑ j ∈ J, t j * 4 ^ j / n ≤ 4)
    (he : ∀ i ∈ I, ∀ j ∈ J, 0 ≤ e i j)
    (hdeg : ∀ i ∈ I, ∀ j ∈ J, e i j ≤ c₁ * d * s i ∧ e i j ≤ c₁ * d * t j)
    (hdisc : ∀ i ∈ I, ∀ j ∈ J, e i j ≤ c₂ * (s i * t j * d / n) ∨
      e i j * Real.log (e i j / (s i * t j * d / n)) ≤
        c₃ * max (s i) (t j) * Real.log (n / max (s i) (t j))) :
    ∑ i ∈ I, ∑ j ∈ J,
        (if Real.sqrt d < (2 : ℝ) ^ (i + j) then e i j * (2 : ℝ) ^ (i + j) / n else 0) ≤
      2 * (24 + 8 * c₁ + 16 * c₂ + 64 * c₃) * Real.sqrt d := by
  -- The pairs with `sᵢ ≤ tⱼ`.
  have h1 := fo3aAux_half hn hd hc₁ hc₂ hc₃ I J s t e hs ht hα hβ he
    (fun i hi j hj => (hdeg i hi j hj).1) hdisc
  -- The pairs with `tⱼ ≤ sᵢ`: the same bound with the roles of `x` and `y` exchanged.
  have h2 := fo3aAux_half hn hd hc₁ hc₂ hc₃ J I t s (fun j i => e i j) ht hs hβ hα
    (fun j hj i hi => he i hi j hj) (fun j hj i hi => (hdeg i hi j hj).2)
    (fun j hj i hi => by
      have h := hdisc i hi j hj
      rw [max_comm (s i) (t j), mul_comm (s i) (t j)] at h
      exact h)
  rw [Finset.sum_comm] at h2
  have hsplit : ∀ i ∈ I, ∀ j ∈ J,
      (if Real.sqrt d < (2 : ℝ) ^ (i + j) then e i j * (2 : ℝ) ^ (i + j) / n else 0) ≤
        (if s i ≤ t j ∧ Real.sqrt d < (2 : ℝ) ^ (i + j) then e i j * (2 : ℝ) ^ (i + j) / n
          else 0) +
        (if t j ≤ s i ∧ Real.sqrt d < (2 : ℝ) ^ (j + i) then e i j * (2 : ℝ) ^ (j + i) / n
          else 0) := by
    intro i hi j hj
    rw [add_comm j i]
    have hX : 0 ≤ e i j * (2 : ℝ) ^ (i + j) / n := by
      have := he i hi j hj
      positivity
    have hY : 0 ≤ (if s i ≤ t j ∧ Real.sqrt d < (2 : ℝ) ^ (i + j) then
        e i j * (2 : ℝ) ^ (i + j) / n else 0) := by
      split_ifs <;> linarith
    have hZ : 0 ≤ (if t j ≤ s i ∧ Real.sqrt d < (2 : ℝ) ^ (i + j) then
        e i j * (2 : ℝ) ^ (i + j) / n else 0) := by
      split_ifs <;> linarith
    by_cases h : Real.sqrt d < (2 : ℝ) ^ (i + j)
    · rw [ite_eq_left h]
      rcases le_total (s i) (t j) with hst | hts
      · rw [ite_eq_left (show s i ≤ t j ∧ Real.sqrt d < (2 : ℝ) ^ (i + j) from ⟨hst, h⟩)]
        linarith
      · rw [ite_eq_left (show t j ≤ s i ∧ Real.sqrt d < (2 : ℝ) ^ (i + j) from ⟨hts, h⟩)]
        linarith
    · rw [ite_eq_right h]
      linarith
  calc _ ≤ ∑ i ∈ I, ∑ j ∈ J,
          ((if s i ≤ t j ∧ Real.sqrt d < (2 : ℝ) ^ (i + j) then e i j * (2 : ℝ) ^ (i + j) / n
            else 0) +
          (if t j ≤ s i ∧ Real.sqrt d < (2 : ℝ) ^ (j + i) then e i j * (2 : ℝ) ^ (j + i) / n
            else 0)) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hsplit i hi j hj
    _ = ∑ i ∈ I, ∑ j ∈ J,
          (if s i ≤ t j ∧ Real.sqrt d < (2 : ℝ) ^ (i + j) then e i j * (2 : ℝ) ^ (i + j) / n
            else 0) +
        ∑ i ∈ I, ∑ j ∈ J,
          (if t j ≤ s i ∧ Real.sqrt d < (2 : ℝ) ^ (j + i) then e i j * (2 : ℝ) ^ (j + i) / n
            else 0) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ (24 + 8 * c₁ + 16 * c₂ + 64 * c₃) * Real.sqrt d +
        (24 + 8 * c₁ + 16 * c₂ + 64 * c₃) * Real.sqrt d := add_le_add h1 h2
    _ = 2 * (24 + 8 * c₁ + 16 * c₂ + 64 * c₃) * Real.sqrt d := by ring

end External.FeigeOfek
