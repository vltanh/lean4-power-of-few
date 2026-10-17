module

public import PowerOfFew.External.FeigeOfek.Heavy
public import PowerOfFew.External.FeigeOfek.Properties
public import PowerOfFew.External.FeigeOfek.Light

/-!
# Feige and Ofek's bound on the spectral norm of `G(n, p)`

U. Feige and E. Ofek, *Spectral techniques applied to sparse random graphs*, Random Structures &
Algorithms 27 (2005) 251–275, Section 2: for `pn ≥ c log n`, the adjacency matrix `A` of `G(n, p)`
satisfies `‖A − E A‖ = O(√(pn))` with high probability. The proof:

* the operator norm is at most twice the largest value of `xᵀ (A − E A) y` over the grid net
  (`Matrix.norm_toEuclideanCLM_le_of_gridNet`);
* `xᵀ (A − E A) y` is the sum of its light part (`lightSum`) and its heavy part; the light part is
  at most `21 √(pn)` for all points of the net at once, except with probability `2e^(−n)`
  (`lightSum_le`);
* the heavy part is at most `heavySum G (pn) x y + p ∑_{heavy} |xᵤ y_v|`, and
  `p ∑_{heavy} |xᵤ y_v| ≤ p (n / √(pn)) ∑ xᵤ² y_v² ≤ √(pn)`; on the event of bounded degrees and
  discrepancy (`exists_degreeBound_discrepancy`), `heavySum ≤ K √(pn)` (`heavySum_le`);
* for `n` below a threshold `N`, `‖A − E A‖ ≤ ‖A − E A‖_F ≤ n < N ≤ (N / √(c log 2)) √(pn)`
  (and `n ≤ 1` is trivial).

The sparse paper's Lemma A.7 has exactly this statement; the formalization proves it from this
theorem (`PowerOfFew.Sparse.lemmaA_7`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.FeigeOfek

/-! ### Small `n`: the Frobenius norm -/

/-- The spectral norm is at most the Frobenius norm (Cauchy–Schwarz, row by row). -/
private theorem fo6Aux_specNorm_le_frobenius {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    specNorm M ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) := by
  unfold specNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  rw [← Real.sqrt_sq (norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) M x)),
    ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have : (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) M x) i = ∑ j, M i j * x j := by
    simp [Matrix.mulVec, dotProduct]
  rw [this]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- `‖A − E A‖ ≤ ‖A − E A‖_F ≤ n`, as the entries of `A − E A` lie in `[−1, 1]`. -/
private theorem fo6Aux_specNorm_le_card {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (G : SimpleGraph (Fin n)) : specNorm (adjMat G - meanAdj n p) ≤ n := by
  have hentry : ∀ u v, (adjMat G - meanAdj n p) u v ^ 2 ≤ 1 := by
    intro u v
    simp only [Matrix.sub_apply, adjMat, meanAdj, Matrix.of_apply]
    split_ifs <;> nlinarith
  have h2 : ∑ u, ∑ v, (adjMat G - meanAdj n p) u v ^ 2 ≤ (n : ℝ) ^ 2 := by
    calc ∑ u, ∑ v, (adjMat G - meanAdj n p) u v ^ 2
        ≤ ∑ _u : Fin n, ∑ _v : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hentry u v
      _ = (n : ℝ) ^ 2 := by simp [sq]
  refine (fo6Aux_specNorm_le_frobenius _).trans ?_
  rw [← Real.sqrt_sq (Nat.cast_nonneg n)]
  exact Real.sqrt_le_sqrt h2

/-! ### The bilinear form on the net: light and heavy parts -/

/-- `xᵀ (A − E A) y` is its light part plus its heavy part: the diagonal terms vanish, and
`(A − E A)ᵤᵥ = Aᵤᵥ − p` for `u ≠ v`. -/
private theorem fo6Aux_bilin_eq {n : ℕ} (G : SimpleGraph (Fin n)) (p d : ℝ)
    (x y : Fin n → ℝ) :
    ∑ u, ∑ v, x u * (adjMat G - meanAdj n p) u v * y v =
      lightSum G p d x y +
        ∑ u, ∑ v, if u ≠ v ∧ Real.sqrt d / n < |x u * y v| then
          x u * (adjMat G u v - p) * y v else 0 := by
  unfold lightSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases huv : u = v
  · subst huv
    simp [adjMat, meanAdj]
  · have hentry : (adjMat G - meanAdj n p) u v = adjMat G u v - p := by
      simp [meanAdj, huv]
    rw [hentry]
    by_cases hl : |x u * y v| ≤ Real.sqrt d / n
    · have hh : ¬ (Real.sqrt d / n < |x u * y v|) := not_lt.mpr hl
      rw [ite_eq_left ⟨huv, hl⟩, ite_eq_right fun h => hh h.2, add_zero]
    · have hh : Real.sqrt d / n < |x u * y v| := lt_of_not_ge hl
      rw [ite_eq_right fun h => hl h.2, ite_eq_left ⟨huv, hh⟩, zero_add]

/-- The heavy part is at most `heavySum G d x y + p ∑_{heavy} |xᵤ y_v|`, as
`|Aᵤᵥ − p| ≤ Aᵤᵥ + p`. -/
private theorem fo6Aux_heavy_le {n : ℕ} (G : SimpleGraph (Fin n)) {p : ℝ} (hp0 : 0 ≤ p)
    (d : ℝ) (x y : Fin n → ℝ) :
    |∑ u, ∑ v, if u ≠ v ∧ Real.sqrt d / n < |x u * y v| then
        x u * (adjMat G u v - p) * y v else 0| ≤
      heavySum G d x y +
        p * ∑ u, ∑ v, if Real.sqrt d / n < |x u * y v| then |x u * y v| else 0 := by
  unfold heavySum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  have hA0 : 0 ≤ adjMat G u v := by
    simp only [adjMat, Matrix.of_apply]
    split_ifs <;> norm_num
  by_cases hh : Real.sqrt d / n < |x u * y v|
  · rw [ite_eq_left hh, ite_eq_left hh]
    by_cases huv : u = v
    · rw [ite_eq_right fun h => h.1 huv, abs_zero]
      positivity
    · rw [ite_eq_left ⟨huv, hh⟩]
      have hAp : |adjMat G u v - p| ≤ adjMat G u v + p := by
        rw [abs_le]
        constructor <;> linarith
      simp only [abs_mul]
      calc |x u| * |adjMat G u v - p| * |y v| ≤ |x u| * (adjMat G u v + p) * |y v| := by
            gcongr
        _ = |x u| * adjMat G u v * |y v| + p * (|x u| * |y v|) := by ring
  · rw [ite_eq_right fun h => hh h.2, ite_eq_right hh, ite_eq_right hh, abs_zero, mul_zero,
      add_zero]

/-- On the heavy pairs `|xᵤ y_v| ≤ (n / √d) (xᵤ y_v)²`, so for `x, y` in the unit ball
`∑_{heavy} |xᵤ y_v| ≤ n / √d`. -/
private theorem fo6Aux_heavy_abs_le {n : ℕ} {d : ℝ} (hd : 0 < d) (hn : 0 < n)
    (x y : Fin n → ℝ) (hx : ∑ u, x u ^ 2 ≤ 1) (hy : ∑ v, y v ^ 2 ≤ 1) :
    ∑ u, ∑ v, (if Real.sqrt d / n < |x u * y v| then |x u * y v| else 0) ≤
      n / Real.sqrt d := by
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hterm : ∀ u v, (if Real.sqrt d / n < |x u * y v| then |x u * y v| else 0) ≤
      n / Real.sqrt d * (x u ^ 2 * y v ^ 2) := by
    intro u v
    split_ifs with h
    · have h1 : x u ^ 2 * y v ^ 2 = |x u * y v| ^ 2 := by rw [sq_abs]; ring
      rw [h1]
      rw [div_lt_iff₀ hnr] at h
      rw [div_mul_eq_mul_div, le_div_iff₀ hsd]
      nlinarith [abs_nonneg (x u * y v)]
    · positivity
  calc ∑ u, ∑ v, (if Real.sqrt d / n < |x u * y v| then |x u * y v| else 0)
      ≤ ∑ u, ∑ v, n / Real.sqrt d * (x u ^ 2 * y v ^ 2) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hterm u v
    _ = n / Real.sqrt d * ((∑ u, x u ^ 2) * ∑ v, y v ^ 2) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        simp_rw [Finset.mul_sum]
    _ ≤ n / Real.sqrt d * (1 * 1) := by
        gcongr
    _ = n / Real.sqrt d := by ring

/-- `p (n / √(pn)) = √(pn)`. -/
private theorem fo6Aux_mul_div_sqrt {n : ℕ} {p : ℝ} (hd : 0 < p * n) :
    p * (n / Real.sqrt (p * n)) = Real.sqrt (p * n) := by
  have hsd : 0 < Real.sqrt (p * n) := Real.sqrt_pos.mpr hd
  rw [← mul_div_assoc, div_eq_iff hsd.ne', Real.mul_self_sqrt hd.le]

/-! ### The failure probabilities -/

/-- For large `n`, `n^(−a−1) + 2e^(−n) ≤ n^(−a)`. -/
private theorem fo6Aux_tail (a : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) ^ (-(a + 1)) + 2 * Real.exp (-(n : ℝ)) ≤ (n : ℝ) ^ (-a) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a 1 one_pos
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, x ^ a * Real.exp (-1 * x) < 1 / 4 :=
    h1.eventually (gt_mem_nhds (by norm_num))
  have h3 : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ x := Filter.eventually_ge_atTop 2
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually (h2.and h3))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hlt, h2n⟩ := hN n hn
  have hx : (0 : ℝ) < n := by linarith
  have hpa : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hx a
  have hr : (n : ℝ) ^ (-a) = ((n : ℝ) ^ a)⁻¹ := Real.rpow_neg hx.le a
  have h5 : (n : ℝ) ^ (-(a + 1)) = (n : ℝ) ^ (-a) * (n : ℝ)⁻¹ := by
    rw [show -(a + 1) = -a + -1 by ring, Real.rpow_add hx, Real.rpow_neg_one]
  rw [h5, hr]
  have h6 : Real.exp (-(n : ℝ)) * (n : ℝ) ^ a ≤ 1 / 4 := by
    rw [show -(n : ℝ) = -1 * (n : ℝ) by ring, mul_comm]
    exact hlt.le
  have h7 : Real.exp (-(n : ℝ)) ≤ 1 / 4 * ((n : ℝ) ^ a)⁻¹ := by
    calc Real.exp (-(n : ℝ)) = Real.exp (-(n : ℝ)) * (n : ℝ) ^ a * ((n : ℝ) ^ a)⁻¹ := by
          field_simp
      _ ≤ 1 / 4 * ((n : ℝ) ^ a)⁻¹ := by gcongr
  have hinv : (n : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2n
  have h8 : ((n : ℝ) ^ a)⁻¹ * (n : ℝ)⁻¹ ≤ ((n : ℝ) ^ a)⁻¹ * (1 / 2) :=
    mul_le_mul_of_nonneg_left hinv (inv_nonneg.mpr hpa.le)
  linarith

/-! ### The theorem -/

/-- **Feige–Ofek (2005)**: for all `c, a > 0` there is a constant `C` such that, whenever
`pn ≥ c log n`, the adjacency matrix `A` of `G ∼ G(n, p)` satisfies `‖A − E A‖_op ≤ C √(pn)` with
probability at least `1 − n^(−a)`. -/
theorem feigeOfek {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ∃ C : ℝ, ∀ (n : ℕ) (p : ℝ), 0 < p → p ≤ 1 → c * Real.log n ≤ p * n →
      1 - (n : ℝ) ^ (-a) ≤
        gnpProb n p (fun G => specNorm (adjMat G - meanAdj n p) ≤ C * Real.sqrt (p * n)) := by
  -- The constants: degrees and discrepancy with failure probability `n^(−a−1)`, the heavy-pair
  -- constant `K`, the threshold `N₀`, and `C = max (2 (22 + K)) (N₀ / √(c log 2))`.
  obtain ⟨c₁, c₂, c₃, hc₁, hc₂, hc₃, hprop⟩ :=
    exists_degreeBound_discrepancy hc (a := a + 1) (by linarith)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * (24 + 8 * c₁ + 16 * c₂ + 64 * c₃) := ⟨_, rfl⟩
  obtain ⟨N₁, hN₁⟩ := fo6Aux_tail a
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, N₀ = max N₁ 2 := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = N₀ / Real.sqrt (c * Real.log 2) := ⟨_, rfl⟩
  refine ⟨max (2 * (22 + K)) C₂, fun n p hp0 hp1 hpn => ?_⟩
  have hsure : (∀ G : SimpleGraph (Fin n),
      specNorm (adjMat G - meanAdj n p) ≤ max (2 * (22 + K)) C₂ * Real.sqrt (p * n)) →
      1 - (n : ℝ) ^ (-a) ≤
        gnpProb n p (fun G => specNorm (adjMat G - meanAdj n p) ≤
          max (2 * (22 + K)) C₂ * Real.sqrt (p * n)) := by
    intro h
    have h1 := gnpProb_mono (n := n) (p := p) (P := fun _ => True) (fun G _ => h G)
    rw [gnpProb_true] at h1
    have : 0 ≤ (n : ℝ) ^ (-a) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    linarith
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · -- `n ≤ 1`
    interval_cases n
    · apply hsure
      intro G
      have h := fo6Aux_specNorm_le_card hp0.le hp1 G
      simpa using h
    · simp only [Nat.cast_one, Real.one_rpow, sub_self]
      exact gnpProb_nonneg _
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := by linarith
  rcases Nat.lt_or_ge n N₀ with hnN | hnN
  · -- `2 ≤ n < N₀`: `‖A − E A‖ ≤ n < N₀ ≤ (N₀ / √(c log 2)) √(pn)`, surely.
    apply hsure
    intro G
    have hlog2 : c * Real.log 2 ≤ p * n :=
      (mul_le_mul_of_nonneg_left (Real.log_le_log two_pos hn2') hc.le).trans hpn
    have hpos : 0 < Real.sqrt (c * Real.log 2) :=
      Real.sqrt_pos.mpr (mul_pos hc (Real.log_pos one_lt_two))
    have h4 : (N₀ : ℝ) ≤ C₂ * Real.sqrt (p * n) := by
      rw [hC₂, div_mul_eq_mul_div, le_div_iff₀ hpos]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlog2) (Nat.cast_nonneg _)
    calc specNorm (adjMat G - meanAdj n p) ≤ n := fo6Aux_specNorm_le_card hp0.le hp1 G
      _ ≤ N₀ := by exact_mod_cast hnN.le
      _ ≤ C₂ * Real.sqrt (p * n) := h4
      _ ≤ max (2 * (22 + K)) C₂ * Real.sqrt (p * n) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
  -- `n ≥ N₀`.
  have hN1n : N₁ ≤ n := le_trans (by rw [hN₀]; exact le_max_left _ _) hnN
  have htail := hN₁ n hN1n
  have hd : 0 < p * n := mul_pos hp0 hnpos
  have hsd : 0 < Real.sqrt (p * n) := Real.sqrt_pos.mpr hd
  -- On the event of bounded degrees, discrepancy and light sums at most `21 √(pn)` on the net,
  -- `|xᵀ (A − E A) y| ≤ (21 + K + 1) √(pn)` on the net, so `‖A − E A‖ ≤ 2 (22 + K) √(pn)`.
  have hdet : ∀ G : SimpleGraph (Fin n),
      DegreeBound G (p * n) c₁ ∧ Discrepancy G (p * n) c₂ c₃ →
      (∀ x ∈ gridNet n, ∀ y ∈ gridNet n,
        |lightSum G p (p * n) x y| ≤ 21 * Real.sqrt (p * n)) →
      specNorm (adjMat G - meanAdj n p) ≤ max (2 * (22 + K)) C₂ * Real.sqrt (p * n) := by
    rintro G ⟨hdeg, hdisc⟩ hlight
    have hbil : ∀ x ∈ gridNet n, ∀ y ∈ gridNet n,
        |∑ u, ∑ v, x u * (adjMat G - meanAdj n p) u v * y v| ≤
          (22 + K) * Real.sqrt (p * n) := by
      intro x hx y hy
      have hx1 := sum_sq_le_one_of_mem_gridNet hx
      have hy1 := sum_sq_le_one_of_mem_gridNet hy
      rw [fo6Aux_bilin_eq G p (p * n) x y]
      have h1 := hlight x hx y hy
      have h2 := fo6Aux_heavy_le G hp0.le (p * n) x y
      have h3 := heavySum_le G hd hc₁ hc₂ hc₃ hdeg hdisc x y hx1 hy1
      have h4 := fo6Aux_heavy_abs_le hd (by omega) x y hx1 hy1
      have h5 := fo6Aux_mul_div_sqrt hd
      have h6 : p * ∑ u, ∑ v, (if Real.sqrt (p * n) / n < |x u * y v| then |x u * y v| else 0)
          ≤ Real.sqrt (p * n) :=
        (mul_le_mul_of_nonneg_left h4 hp0.le).trans h5.le
      rw [← hK] at h3
      calc _ ≤ |lightSum G p (p * n) x y| + |∑ u, ∑ v, if u ≠ v ∧
              Real.sqrt (p * n) / n < |x u * y v| then x u * (adjMat G u v - p) * y v else 0| :=
            abs_add_le _ _
        _ ≤ 21 * Real.sqrt (p * n) + (K * Real.sqrt (p * n) + Real.sqrt (p * n)) := by
            gcongr
            linarith
        _ = (22 + K) * Real.sqrt (p * n) := by ring
    have hnorm := Matrix.norm_toEuclideanCLM_le_of_gridNet (adjMat G - meanAdj n p) hbil
    unfold specNorm
    calc _ ≤ 2 * ((22 + K) * Real.sqrt (p * n)) := hnorm
      _ = 2 * (22 + K) * Real.sqrt (p * n) := by ring
      _ ≤ max (2 * (22 + K)) C₂ * Real.sqrt (p * n) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hsd.le
  -- The failure probability: `n^(−a−1) + 2e^(−n) ≤ n^(−a)`.
  apply le_gnpProb_of_not_le
  calc gnpProb n p (fun G => ¬ specNorm (adjMat G - meanAdj n p) ≤
        max (2 * (22 + K)) C₂ * Real.sqrt (p * n))
      ≤ gnpProb n p (fun G => ¬ (DegreeBound G (p * n) c₁ ∧ Discrepancy G (p * n) c₂ c₃) ∨
          ∃ x ∈ gridNet n, ∃ y ∈ gridNet n,
            21 * Real.sqrt (p * n) < |lightSum G p (p * n) x y|) := by
        refine gnpProb_mono fun G hG => ?_
        by_contra hcon
        rw [not_or, not_not] at hcon
        exact hG (hdet G hcon.1 fun x hx y hy => not_lt.mp fun h => hcon.2 ⟨x, hx, y, hy, h⟩)
    _ ≤ gnpProb n p (fun G => ¬ (DegreeBound G (p * n) c₁ ∧ Discrepancy G (p * n) c₂ c₃)) +
        gnpProb n p (fun G => ∃ x ∈ gridNet n, ∃ y ∈ gridNet n,
          21 * Real.sqrt (p * n) < |lightSum G p (p * n) x y|) := gnpProb_or_le _ _
    _ ≤ (n : ℝ) ^ (-(a + 1)) + 2 * Real.exp (-(n : ℝ)) :=
        add_le_add (hprop n p hn2 hp0 hp1 hpn) (lightSum_le (by omega) hp0 hp1)
    _ ≤ (n : ℝ) ^ (-a) := htail

end PowerOfFew.FeigeOfek
