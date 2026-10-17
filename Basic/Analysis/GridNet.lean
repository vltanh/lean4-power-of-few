module

public import Mathlib

/-!
# A grid net of the Euclidean unit ball

`gridNet n` is the set of points `z / (4√n)` with `z ∈ ℤⁿ` and `∑ zᵢ² ≤ 16 n`. It lies in the unit
ball of `ℝⁿ` (`sum_sq_le_one_of_mem_gridNet`), it has at most `(33 e)ⁿ` points (`card_gridNet_le`),
and every point `x` of the unit ball lies within `1/4` of one of its points
(`exists_mem_gridNet_sum_sq_sub_le`: round each coordinate of `4√n x` toward zero). Hence the
operator norm of a square matrix is at most twice the largest value of its bilinear form on the net
(`Matrix.norm_toEuclideanCLM_le_of_gridNet`).

Feige and Ofek bound the spectral norm of a random graph through such a net
(`External.FeigeOfek.opNorm_adjMatrix_sub_le`). The bound on the number of points is the exponential-moment
count `#{z : ∑ zᵢ² ≤ 16 n} ≤ e^(t · 16 n) (∑_{m ∈ ℤ} e^(−t m²))ⁿ` with `t = 1/16`, and
`∑_{m ∈ ℤ} e^(−m²/16) ≤ 1 + 2 / (e^(1/16) − 1) ≤ 33`.
-/

@[expose] public section

noncomputable section

/-- The grid net of the unit ball of `ℝⁿ`: the points `z / (4√n)` with `z ∈ ℤⁿ` and
`∑ zᵢ² ≤ 16 n` (the coordinates of such `z` lie in `[−4n, 4n]`). -/
def gridNet (n : ℕ) : Finset (Fin n → ℝ) := by
  classical
  exact ((Fintype.piFinset fun _ : Fin n => Finset.Icc (-(4 * n : ℤ)) (4 * n)).filter
      fun z => ∑ i, z i ^ 2 ≤ 16 * (n : ℤ)).image fun z i => (z i : ℝ) / (4 * Real.sqrt n)

/-- The origin (`z = 0`) is a point of the net. -/
theorem zero_mem_gridNet (n : ℕ) : (0 : Fin n → ℝ) ∈ gridNet n := by
  unfold gridNet
  refine Finset.mem_image.mpr ⟨0, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩,
    ?_⟩
  · simp only [Pi.zero_apply, Finset.mem_Icc]
    constructor <;> omega
  · simp only [Pi.zero_apply]
    simp
  · funext i
    simp

/-- Every point of the net lies in the unit ball. -/
theorem sum_sq_le_one_of_mem_gridNet {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ gridNet n) :
    ∑ i, x i ^ 2 ≤ 1 := by
  unfold gridNet at hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  have hz' := (Finset.mem_filter.mp hz).2
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · -- `∑ (zᵢ / (4√n))² = ∑ zᵢ² / (16 n) ≤ 1`
    have hzR : (∑ i, (z i : ℝ) ^ 2) ≤ 16 * n := by exact_mod_cast hz'
    have hs : (4 * Real.sqrt n) ^ 2 = 16 * n := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]; ring
    simp_rw [div_pow, hs, ← Finset.sum_div]
    rw [div_le_one (by positivity)]
    exact hzR

/-- `∑_{m ∈ s} e^(−m²/16) ≤ 33` for every finite set `s` of integers: with `r = e^(−1/16)`,
`e^(−m²/16) ≤ r^|m|` (as `m² ≥ |m|`), `∑_{m ∈ ℤ} r^|m| = 1 + 2r/(1 − r) = 1 + 2/(e^(1/16) − 1)`, and
`e^(1/16) − 1 ≥ 1/16`. -/
private theorem sum_exp_neg_sq_div_le (s : Finset ℤ) :
    ∑ m ∈ s, Real.exp (-(m : ℝ) ^ 2 / 16) ≤ 33 := by
  set r := Real.exp (-(1 / 16)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  -- `e^(1/16) ≥ 17/16`, i.e. `r ≤ 16/17`
  have hr1 : r ≤ 16 / 17 := by
    have h := Real.add_one_le_exp (1 / 16)
    rw [hr, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have hr1' : r < 1 := by linarith
  have hgeo : HasSum (fun k : ℕ => r * r ^ k) (r * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1').mul_left r
  -- the two-sided geometric series `∑_{m ∈ ℤ} r^|m| = r/(1 − r) + 1 + r/(1 − r)`
  have hf : HasSum (fun m : ℤ => r ^ m.natAbs)
      (r * (1 - r)⁻¹ + r ^ (0 : ℤ).natAbs + r * (1 - r)⁻¹) := by
    refine HasSum.of_add_one_of_neg_add_one ?_ ?_
    · convert hgeo using 2 with k
      rw [show ((k : ℤ) + 1).natAbs = k + 1 by omega, pow_succ']
    · convert hgeo using 2 with k
      rw [show (-((k : ℤ) + 1)).natAbs = k + 1 by omega, pow_succ']
  calc ∑ m ∈ s, Real.exp (-(m : ℝ) ^ 2 / 16) ≤ ∑ m ∈ s, r ^ m.natAbs := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [hr, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have h1 : ((m.natAbs : ℤ) : ℝ) ≤ ((m ^ 2 : ℤ) : ℝ) :=
          Int.cast_le.mpr (Int.natAbs_le_self_sq m)
        rw [Int.cast_natCast, Int.cast_pow] at h1
        linarith
    _ ≤ r * (1 - r)⁻¹ + r ^ (0 : ℤ).natAbs + r * (1 - r)⁻¹ :=
        sum_le_hasSum s (fun _ _ => by positivity) hf
    _ ≤ 33 := by
        simp only [Int.natAbs_zero, pow_zero]
        have : r * (1 - r)⁻¹ ≤ 16 := by
          rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
          linarith
        linarith

/-- Counting by an exponential moment: if `f ≥ 0` on `s` and `f ≥ 1` where `p` holds, then
`#{a ∈ s : p a} ≤ ∑_{a ∈ s} f a`. -/
private theorem card_filter_le_sum_of_one_le {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p]
    (f : α → ℝ) (hf0 : ∀ a ∈ s, 0 ≤ f a) (hf1 : ∀ a ∈ s, p a → 1 ≤ f a) :
    ((s.filter p).card : ℝ) ≤ ∑ a ∈ s, f a := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_le_sum fun a ha => ?_
  split_ifs with h
  · exact hf1 a ha h
  · exact hf0 a ha

/-- The net has at most `(33 e)ⁿ` points. -/
theorem card_gridNet_le (n : ℕ) : ((gridNet n).card : ℝ) ≤ (33 * Real.exp 1) ^ n := by
  unfold gridNet
  -- `#net ≤ #{z ∈ box : ∑ zᵢ² ≤ 16 n} ≤ ∑_{z ∈ box} ∏ᵢ e · e^(−zᵢ²/16)`
  refine (Nat.cast_le.mpr Finset.card_image_le).trans ((card_filter_le_sum_of_one_le _ _
    (fun z => ∏ i, (Real.exp 1 * Real.exp (-(z i : ℝ) ^ 2 / 16))) (fun z _ => by positivity)
    (fun z _ hz => ?_)).trans ?_)
  · -- `∏ᵢ e · e^(−zᵢ²/16) = e^(n − ∑ zᵢ²/16) ≥ 1` when `∑ zᵢ² ≤ 16 n`
    have hzR : (∑ i, (z i : ℝ) ^ 2) ≤ 16 * n := by exact_mod_cast hz
    simp only [← Real.exp_add, ← Real.exp_sum]
    apply Real.one_le_exp
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, ← Finset.sum_div, Finset.sum_neg_distrib]
    linarith
  · -- `∑_{z ∈ box} ∏ᵢ e · e^(−zᵢ²/16) = ∏ᵢ ∑_{m} e · e^(−m²/16) ≤ (33 e)ⁿ`
    calc ∑ z ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(4 * n : ℤ)) (4 * n),
          ∏ i, (Real.exp 1 * Real.exp (-(z i : ℝ) ^ 2 / 16))
        = ∏ _i : Fin n, ∑ m ∈ Finset.Icc (-(4 * n : ℤ)) (4 * n),
          Real.exp 1 * Real.exp (-(m : ℝ) ^ 2 / 16) :=
          (Finset.prod_univ_sum (fun _ => Finset.Icc (-(4 * n : ℤ)) (4 * n))
            (fun _ (m : ℤ) => Real.exp 1 * Real.exp (-(m : ℝ) ^ 2 / 16))).symm
      _ ≤ ∏ _i : Fin n, (33 * Real.exp 1) := by
          refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun _ _ => ?_
          rw [← Finset.mul_sum, mul_comm]
          exact mul_le_mul_of_nonneg_right (sum_exp_neg_sq_div_le _) (Real.exp_pos 1).le
      _ = (33 * Real.exp 1) ^ n := by simp

/-- Rounding toward zero: a point `v` of the unit ball lies within squared distance `1/16` of the
point `z / (4√n)` of the net, `zᵢ = sign(vᵢ) ⌊4√n |vᵢ|⌋`: `|zᵢ| ≤ 4√n |vᵢ|` (so `∑ zᵢ² ≤ 16 n`) and
`|vᵢ − zᵢ / (4√n)| ≤ 1 / (4√n)`. -/
theorem exists_mem_gridNet_sum_sq_sub_le {n : ℕ} (v : Fin n → ℝ) (hv : ∑ i, v i ^ 2 ≤ 1) :
    ∃ x ∈ gridNet n, ∑ i, (v i - x i) ^ 2 ≤ 1 / 16 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, zero_mem_gridNet 0, by simp⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set c := 4 * Real.sqrt n with hc_def
  have hc : 0 < c := by
    rw [hc_def]
    have : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
    positivity
  have hc2 : c ^ 2 = 16 * n := by rw [hc_def, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]; ring
  let z : Fin n → ℤ := fun i => if 0 ≤ v i then ⌊c * v i⌋ else ⌈c * v i⌉
  -- `zᵢ² ≤ (c vᵢ)²` and `(c vᵢ − zᵢ)² ≤ 1`
  have hz : ∀ i, (z i : ℝ) ^ 2 ≤ (c * v i) ^ 2 ∧ (c * v i - z i) ^ 2 ≤ 1 := by
    intro i
    by_cases h : 0 ≤ v i
    · have h1 : (z i : ℝ) = ⌊c * v i⌋ := by simp [z, h]
      have hcv : 0 ≤ c * v i := mul_nonneg hc.le h
      have f1 := Int.floor_le (c * v i)
      have f2 := Int.lt_floor_add_one (c * v i)
      have f3 : (0 : ℝ) ≤ ⌊c * v i⌋ := by exact_mod_cast Int.floor_nonneg.mpr hcv
      rw [h1]
      constructor <;> nlinarith
    · have h1 : (z i : ℝ) = ⌈c * v i⌉ := by simp [z, h]
      have hcv : c * v i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le (le_of_lt (not_le.mp h))
      have f1 := Int.le_ceil (c * v i)
      have f2 := Int.ceil_lt_add_one (c * v i)
      have f3 : (⌈c * v i⌉ : ℝ) ≤ 0 := by exact_mod_cast Int.ceil_le.mpr (by simpa using hcv)
      rw [h1]
      constructor <;> nlinarith
  have hsum : (∑ i, (z i : ℝ) ^ 2) ≤ 16 * n := by
    calc (∑ i, (z i : ℝ) ^ 2) ≤ ∑ i, (c * v i) ^ 2 := Finset.sum_le_sum fun i _ => (hz i).1
      _ = c ^ 2 * ∑ i, v i ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ c ^ 2 * 1 := by gcongr
      _ = 16 * n := by rw [hc2, mul_one]
  refine ⟨fun i => (z i : ℝ) / (4 * Real.sqrt n), ?_, ?_⟩
  · -- membership: `∑ zᵢ² ≤ 16 n`, and `zᵢ² ≤ 16 n ≤ (4n)²` puts `z` in the box
    unfold gridNet
    refine Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr
      ⟨Fintype.mem_piFinset.mpr fun i => ?_, by exact_mod_cast hsum⟩, rfl⟩
    have hvi : v i ^ 2 ≤ 1 :=
      (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)).trans hv
    have hzi : (z i : ℝ) ^ 2 ≤ (4 * n) ^ 2 := by
      calc (z i : ℝ) ^ 2 ≤ (c * v i) ^ 2 := (hz i).1
        _ = c ^ 2 * v i ^ 2 := by ring
        _ ≤ c ^ 2 * 1 := by gcongr
        _ ≤ (4 * n) ^ 2 := by nlinarith
    have h4 := abs_le_of_sq_le_sq' hzi (by positivity)
    rw [Finset.mem_Icc]
    constructor
    · exact_mod_cast h4.1
    · exact_mod_cast h4.2
  · -- distance: `∑ (vᵢ − zᵢ/c)² = ∑ (c vᵢ − zᵢ)² / c² ≤ n / (16 n)`
    calc ∑ i, (v i - (z i : ℝ) / (4 * Real.sqrt n)) ^ 2 = ∑ i, (c * v i - z i) ^ 2 / c ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hc_def]
          field_simp
      _ ≤ ∑ _i : Fin n, 1 / c ^ 2 :=
          Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_right (hz i).2 (by positivity)
      _ = 1 / 16 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc2]
          field_simp

open scoped RealInnerProductSpace in
/-- The operator norm of a square matrix is at most twice the largest value of its bilinear form
on the net. -/
theorem Matrix.norm_toEuclideanCLM_le_of_gridNet {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) {B : ℝ}
    (h : ∀ x ∈ gridNet n, ∀ y ∈ gridNet n, |∑ u, ∑ v, x u * W u v * y v| ≤ B) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) W‖ ≤ 2 * B := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) W with hT
  -- `B ≥ 0`: the net contains `0`
  have hB : 0 ≤ B := (abs_nonneg _).trans (h 0 (zero_mem_gridNet n) 0 (zero_mem_gridNet n))
  -- the bilinear form is the inner product `⟨x, W y⟩`
  have hbil : ∀ x y : Fin n → ℝ, ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)),
      T (WithLp.toLp 2 y)⟫ = ∑ u, ∑ v, x u * W u v * y v := by
    intro x y
    rw [hT, Matrix.inner_toEuclideanCLM]
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  -- the points of the net have norm at most `1`
  have hnorm : ∀ x ∈ gridNet n, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
    intro x hx
    refine le_of_pow_le_pow_left₀ two_ne_zero zero_le_one ?_
    rw [EuclideanSpace.real_norm_sq_eq, one_pow]
    exact sum_sq_le_one_of_mem_gridNet hx
  -- every point of the unit ball lies within `1/4` of a point of the net
  have hround : ∀ a : EuclideanSpace ℝ (Fin n), ‖a‖ ≤ 1 →
      ∃ x ∈ gridNet n, ‖a - WithLp.toLp 2 x‖ ≤ 1 / 4 := by
    intro a ha
    have ha2 : ∑ i, a i ^ 2 ≤ 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq]
      nlinarith [norm_nonneg a]
    obtain ⟨x, hx, hd⟩ := exists_mem_gridNet_sum_sq_sub_le (fun i => a i) ha2
    refine ⟨x, hx, le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) ?_⟩
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num
    simpa using hd
  -- for `‖a‖ = ‖b‖ = 1`, rounding both gives `⟨a, W b⟩ ≤ B + ‖W‖/4 + ‖W‖/4`; so `‖W‖ ≤ B + ‖W‖/2`
  have key : ‖T‖ ≤ B + ‖T‖ / 2 := by
    refine ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity) fun b a hb ha => ?_
    rw [RCLike.re_to_real, real_inner_comm]
    obtain ⟨x, hx, hax⟩ := hround a ha.le
    obtain ⟨y, hy, hby⟩ := hround b hb.le
    have e : ⟪a, T b⟫ = ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)), T (WithLp.toLp 2 y)⟫ +
        ⟪a - WithLp.toLp 2 x, T b⟫ +
          ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)), T (b - WithLp.toLp 2 y)⟫ := by
      rw [map_sub, inner_sub_left, inner_sub_right]
      ring
    have h1 : ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)), T (WithLp.toLp 2 y)⟫ ≤ B := by
      rw [hbil]
      exact (le_abs_self _).trans (h x hx y hy)
    have h2 : ⟪a - WithLp.toLp 2 x, T b⟫ ≤ ‖T‖ / 4 :=
      calc ⟪a - WithLp.toLp 2 x, T b⟫ ≤ ‖a - WithLp.toLp 2 x‖ * ‖T b‖ := real_inner_le_norm _ _
        _ ≤ 1 / 4 * (‖T‖ * ‖b‖) :=
          mul_le_mul hax (T.le_opNorm b) (norm_nonneg _) (by norm_num)
        _ = ‖T‖ / 4 := by rw [hb]; ring
    have h3 : ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)), T (b - WithLp.toLp 2 y)⟫ ≤ ‖T‖ / 4 :=
      calc ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)), T (b - WithLp.toLp 2 y)⟫
          ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ * ‖T (b - WithLp.toLp 2 y)‖ :=
            real_inner_le_norm _ _
        _ ≤ 1 * (‖T‖ * (1 / 4)) :=
          mul_le_mul (hnorm x hx) ((T.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left hby (norm_nonneg _))) (norm_nonneg _) zero_le_one
        _ = ‖T‖ / 4 := by ring
    linarith
  linarith

end
