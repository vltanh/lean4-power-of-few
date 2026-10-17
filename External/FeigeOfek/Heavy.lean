module

public import External.FeigeOfek.Defs
public import External.FeigeOfek.SixCases

/-!
# Feige and Ofek's bound for the heavy pairs

If every degree of `G` is at most `c₁ d` and `G` has the discrepancy property with constants
`c₂, c₃`, then for all `x, y` in the unit ball the heavy pairs (`|xᵤ y_v| > √d / n`) contribute
`∑ |xᵤ| A_{uv} |y_v| ≤ 2 (24 + 8 c₁ + 16 c₂ + 64 c₃) √d`, where `A = G.adjMatrix ℝ`
(Feige–Ofek 2005, Section 2.2; Chin–Rao–Vu 2015, their heavy-pair lemma). The proof groups the
coordinates into dyadic blocks `S_i = {u : xᵤ ≠ 0, 2^(i−1) < √n |xᵤ| ≤ 2^i}` (the integer `i` is
`Int.clog 2 (√n |xᵤ|)`) and `T_j` for `y`, bounds the heavy pairs by
`∑_{2^(i+j) > √d} e(S_i, T_j) 2^(i+j) / n`, and applies the six cases (`sum_blocks_le`).
-/

@[expose] public section

noncomputable section

namespace External.FeigeOfek

/-! ### Dyadic blocks of a vector -/

/-- The dyadic index `i = ⌈log₂ (√n |xᵤ|)⌉` of the coordinate `u` of `x`, so that
`2^(i−1) < √n |xᵤ| ≤ 2^i` when `xᵤ ≠ 0`. -/
private def fo3bAux_idx {n : ℕ} (x : Fin n → ℝ) (u : Fin n) : ℤ :=
  Int.clog 2 (Real.sqrt n * |x u|)

/-- The support `{u : xᵤ ≠ 0}` of `x`. -/
private def fo3bAux_supp {n : ℕ} (x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun u => x u ≠ 0

/-- The dyadic block `S_i = {u : xᵤ ≠ 0, 2^(i−1) < √n |xᵤ| ≤ 2^i}` of `x`. -/
private def fo3bAux_block {n : ℕ} (x : Fin n → ℝ) (i : ℤ) : Finset (Fin n) :=
  (fo3bAux_supp x).filter fun u => fo3bAux_idx x u = i

/-- The indices of the nonempty dyadic blocks of `x`. -/
private def fo3bAux_ind {n : ℕ} (x : Fin n → ℝ) : Finset ℤ :=
  (fo3bAux_supp x).image (fo3bAux_idx x)

private lemma fo3bAux_mem_supp {n : ℕ} {x : Fin n → ℝ} {u : Fin n} :
    u ∈ fo3bAux_supp x ↔ x u ≠ 0 := by
  simp [fo3bAux_supp]

private lemma fo3bAux_mem_block {n : ℕ} {x : Fin n → ℝ} {i : ℤ} {u : Fin n} :
    u ∈ fo3bAux_block x i ↔ x u ≠ 0 ∧ fo3bAux_idx x u = i := by
  simp [fo3bAux_block, fo3bAux_mem_supp]

/-- The upper end of a block: `√n |xᵤ| ≤ 2^i`. -/
private lemma fo3bAux_le_zpow_idx {n : ℕ} (x : Fin n → ℝ) (u : Fin n) :
    Real.sqrt n * |x u| ≤ (2 : ℝ) ^ fo3bAux_idx x u := by
  have h := Int.self_le_zpow_clog (R := ℝ) (b := 2) (by norm_num) (Real.sqrt n * |x u|)
  rw [Nat.cast_ofNat] at h
  exact h

/-- The lower end of a block: `2^(i−1) < √n |xᵤ|`, that is `2^i < 2 √n |xᵤ|`. -/
private lemma fo3bAux_zpow_idx_lt {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) {u : Fin n}
    (hu : x u ≠ 0) : (2 : ℝ) ^ fo3bAux_idx x u < 2 * (Real.sqrt n * |x u|) := by
  have hr : 0 < Real.sqrt n * |x u| :=
    mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hn)) (abs_pos.2 hu)
  have h := Int.zpow_pred_clog_lt_self (R := ℝ) (b := 2) (by norm_num) hr
  rw [Nat.cast_ofNat, zpow_sub_one₀ two_ne_zero] at h
  change (2 : ℝ) ^ Int.clog 2 (Real.sqrt n * |x u|) < 2 * (Real.sqrt n * |x u|)
  linarith

/-- Summing over the blocks is summing over the support. -/
private lemma fo3bAux_sum_fiber {n : ℕ} (x : Fin n → ℝ) (f : Fin n → ℝ) :
    ∑ i ∈ fo3bAux_ind x, ∑ u ∈ fo3bAux_block x i, f u = ∑ u ∈ fo3bAux_supp x, f u :=
  Finset.sum_fiberwise_of_maps_to (fun _ hu => Finset.mem_image_of_mem _ hu) f

/-- Regrouping a double sum over the supports of `x` and `y` by pairs of blocks. -/
private lemma fo3bAux_sum_supp_eq {n : ℕ} (x y : Fin n → ℝ) (f : Fin n → Fin n → ℝ) :
    ∑ u ∈ fo3bAux_supp x, ∑ v ∈ fo3bAux_supp y, f u v =
      ∑ i ∈ fo3bAux_ind x, ∑ j ∈ fo3bAux_ind y,
        ∑ u ∈ fo3bAux_block x i, ∑ v ∈ fo3bAux_block y j, f u v := by
  rw [← fo3bAux_sum_fiber x]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc ∑ u ∈ fo3bAux_block x i, ∑ v ∈ fo3bAux_supp y, f u v
      = ∑ u ∈ fo3bAux_block x i, ∑ j ∈ fo3bAux_ind y, ∑ v ∈ fo3bAux_block y j, f u v :=
        Finset.sum_congr rfl fun u _ => (fo3bAux_sum_fiber y (f u)).symm
    _ = ∑ j ∈ fo3bAux_ind y, ∑ u ∈ fo3bAux_block x i, ∑ v ∈ fo3bAux_block y j, f u v :=
        Finset.sum_comm

/-- The blocks of `I` are nonempty, and have at most `n` elements. -/
private lemma fo3bAux_card_block {n : ℕ} (x : Fin n → ℝ) {i : ℤ} (hi : i ∈ fo3bAux_ind x) :
    1 ≤ ((fo3bAux_block x i).card : ℝ) ∧ ((fo3bAux_block x i).card : ℝ) ≤ n := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hi
  constructor
  · have h : 0 < (fo3bAux_block x (fo3bAux_idx x u)).card :=
      Finset.card_pos.2 ⟨u, fo3bAux_mem_block.2 ⟨fo3bAux_mem_supp.1 hu, rfl⟩⟩
    exact_mod_cast h
  · have h := Finset.card_le_univ (fo3bAux_block x (fo3bAux_idx x u))
    rw [Fintype.card_fin] at h
    exact_mod_cast h

/-- `∑ᵢ |S_i| 4^i / n ≤ 4`: each `u ∈ S_i` has `4^i / n < 4 xᵤ²`. -/
private lemma fo3bAux_sum_alpha {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hx : ∑ u, x u ^ 2 ≤ 1) :
    ∑ i ∈ fo3bAux_ind x, ((fo3bAux_block x i).card : ℝ) * (4 : ℝ) ^ i / n ≤ 4 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ∀ u, x u ≠ 0 → (4 : ℝ) ^ fo3bAux_idx x u / n ≤ 4 * x u ^ 2 := by
    intro u hu
    have h1 := fo3bAux_zpow_idx_lt hn x hu
    have hpos : 0 < (2 : ℝ) ^ fo3bAux_idx x u := zpow_pos two_pos _
    have h4 : (4 : ℝ) ^ fo3bAux_idx x u =
        (2 : ℝ) ^ fo3bAux_idx x u * (2 : ℝ) ^ fo3bAux_idx x u := by
      rw [← mul_zpow]; norm_num
    have hsq : (Real.sqrt n * |x u|) ^ 2 = n * x u ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hn'.le, sq_abs]
    have h5 := mul_self_lt_mul_self hpos.le h1
    rw [div_le_iff₀ hn', h4]
    nlinarith [h5, hsq]
  calc ∑ i ∈ fo3bAux_ind x, ((fo3bAux_block x i).card : ℝ) * (4 : ℝ) ^ i / n
      = ∑ i ∈ fo3bAux_ind x, ∑ u ∈ fo3bAux_block x i, (4 : ℝ) ^ i / n := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, mul_div_assoc]
    _ = ∑ i ∈ fo3bAux_ind x, ∑ u ∈ fo3bAux_block x i, (4 : ℝ) ^ fo3bAux_idx x u / n := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u hu => ?_
        rw [(fo3bAux_mem_block.1 hu).2]
    _ ≤ ∑ i ∈ fo3bAux_ind x, ∑ u ∈ fo3bAux_block x i, 4 * x u ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun u hu =>
          key u (fo3bAux_mem_block.1 hu).1
    _ = ∑ u ∈ fo3bAux_supp x, 4 * x u ^ 2 := fo3bAux_sum_fiber x _
    _ ≤ ∑ u, 4 * x u ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun u _ _ => by positivity
    _ = 4 * ∑ u, x u ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 4 := by linarith

/-! ### Edge counts -/

open Classical in
private lemma fo3bAux_adjMatrix_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    0 ≤ G.adjMatrix ℝ u v := by
  rw [SimpleGraph.adjMatrix_apply]
  split_ifs <;> norm_num

open Classical in
private lemma fo3bAux_adjMatrix_comm {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    G.adjMatrix ℝ u v = G.adjMatrix ℝ v u := by
  by_cases h : G.Adj u v
  · simp [h, h.symm]
  · have h' : ¬ G.Adj v u := fun h' => h h'.symm
    simp [h, h']

private lemma fo3bAux_edgeCount_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n)) :
    0 ≤ edgeCount G S T :=
  Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => fo3bAux_adjMatrix_nonneg G u v

private lemma fo3bAux_edgeCount_comm {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n)) :
    edgeCount G S T = edgeCount G T S := by
  unfold edgeCount
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ =>
    fo3bAux_adjMatrix_comm G u v

/-- Bounded degrees: `e(S, T) ≤ c₁ d |S|`. -/
private lemma fo3bAux_edgeCount_le {n : ℕ} {G : SimpleGraph (Fin n)} {d c₁ : ℝ}
    (hdeg : DegreeBound G d c₁) (S T : Finset (Fin n)) :
    edgeCount G S T ≤ c₁ * d * S.card := by
  classical
  unfold edgeCount
  calc ∑ u ∈ S, ∑ v ∈ T, G.adjMatrix ℝ u v ≤ ∑ u ∈ S, ∑ v, G.adjMatrix ℝ u v :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ T) fun v _ _ => fo3bAux_adjMatrix_nonneg G u v
    _ ≤ ∑ _u ∈ S, c₁ * d := Finset.sum_le_sum fun u _ => hdeg u
    _ = c₁ * d * S.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-! ### From the pairs of coordinates to the pairs of blocks -/

/-- With `i, j` the dyadic indices of `u` and `v`: `|xᵤ| |y_v| ≤ 2^(i+j) / n`, so a heavy pair
`(u, v)` has `√d < 2^(i+j)` and `|xᵤ| a |y_v| ≤ a 2^(i+j) / n` (for `a ≥ 0`). -/
private lemma fo3bAux_term_le {n : ℕ} (hn : 0 < n) {d a : ℝ} (ha : 0 ≤ a) (x y : Fin n → ℝ)
    {u v : Fin n} :
    (if Real.sqrt d / n < |x u * y v| then |x u| * a * |y v| else 0) ≤
      if Real.sqrt d < (2 : ℝ) ^ (fo3bAux_idx x u + fo3bAux_idx y v) then
        a * (2 : ℝ) ^ (fo3bAux_idx x u + fo3bAux_idx y v) / n else 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := fo3bAux_le_zpow_idx x u
  have h2 := fo3bAux_le_zpow_idx y v
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn'.le
  have hKpos : 0 < (2 : ℝ) ^ (fo3bAux_idx x u + fo3bAux_idx y v) := zpow_pos two_pos _
  have hprod : n * (|x u| * |y v|) ≤ (2 : ℝ) ^ (fo3bAux_idx x u + fo3bAux_idx y v) := by
    rw [zpow_add₀ two_ne_zero]
    calc n * (|x u| * |y v|) = (Real.sqrt n * Real.sqrt n) * (|x u| * |y v|) := by rw [hsq]
      _ = (Real.sqrt n * |x u|) * (Real.sqrt n * |y v|) := by ring
      _ ≤ (2 : ℝ) ^ fo3bAux_idx x u * (2 : ℝ) ^ fo3bAux_idx y v :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
  by_cases h3 : Real.sqrt d / n < |x u * y v|
  · have h4 : Real.sqrt d < (2 : ℝ) ^ (fo3bAux_idx x u + fo3bAux_idx y v) := by
      rw [abs_mul, div_lt_iff₀ hn'] at h3
      linarith
    rw [ite_eq_left h3, ite_eq_left h4, le_div_iff₀ hn']
    calc |x u| * a * |y v| * n = a * (n * (|x u| * |y v|)) := by ring
      _ ≤ a * (2 : ℝ) ^ (fo3bAux_idx x u + fo3bAux_idx y v) :=
          mul_le_mul_of_nonneg_left hprod ha
  · rw [ite_eq_right h3]
    split_ifs
    · exact div_nonneg (mul_nonneg ha hKpos.le) hn'.le
    · exact le_rfl

open Classical in
/-- The pairs `(u, v) ∈ S_i × T_j` together contribute
`[√d < 2^(i+j)] e(S_i, T_j) 2^(i+j) / n`. -/
private lemma fo3bAux_block_sum_eq {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℝ) (x y : Fin n → ℝ)
    (i j : ℤ) :
    ∑ u ∈ fo3bAux_block x i, ∑ v ∈ fo3bAux_block y j,
        (if Real.sqrt d < (2 : ℝ) ^ (fo3bAux_idx x u + fo3bAux_idx y v) then
          G.adjMatrix ℝ u v * (2 : ℝ) ^ (fo3bAux_idx x u + fo3bAux_idx y v) / n else 0) =
      if Real.sqrt d < (2 : ℝ) ^ (i + j) then
        edgeCount G (fo3bAux_block x i) (fo3bAux_block y j) * (2 : ℝ) ^ (i + j) / n else 0 := by
  have h : ∀ u ∈ fo3bAux_block x i, ∀ v ∈ fo3bAux_block y j,
      (if Real.sqrt d < (2 : ℝ) ^ (fo3bAux_idx x u + fo3bAux_idx y v) then
        G.adjMatrix ℝ u v * (2 : ℝ) ^ (fo3bAux_idx x u + fo3bAux_idx y v) / n else 0) =
      if Real.sqrt d < (2 : ℝ) ^ (i + j) then G.adjMatrix ℝ u v * (2 : ℝ) ^ (i + j) / n
        else 0 := by
    intro u hu v hv
    rw [(fo3bAux_mem_block.1 hu).2, (fo3bAux_mem_block.1 hv).2]
  rw [Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => h u hu v hv]
  split_ifs
  · simp only [edgeCount, Finset.sum_mul, Finset.sum_div]
  · simp

/-- **Feige–Ofek, the heavy pairs.** If every degree is at most `c₁ d` and the discrepancy property
holds with `c₂ ≥ e` and `c₃ ≥ 0`, then for all `x, y` with `∑ xᵤ² ≤ 1` and `∑ y_v² ≤ 1`,
`∑_{|xᵤ y_v| > √d/n} |xᵤ| A_{uv} |y_v| ≤ 2 (24 + 8 c₁ + 16 c₂ + 64 c₃) √d`. -/
theorem heavySum_le {n : ℕ} (G : SimpleGraph (Fin n)) {d c₁ c₂ c₃ : ℝ} (hd : 0 < d)
    (hc₁ : 0 ≤ c₁) (hc₂ : Real.exp 1 ≤ c₂) (hc₃ : 0 ≤ c₃) (hdeg : DegreeBound G d c₁)
    (hdisc : Discrepancy G d c₂ c₃) (x y : Fin n → ℝ) (hx : ∑ u, x u ^ 2 ≤ 1)
    (hy : ∑ v, y v ^ 2 ≤ 1) :
    heavySum G d x y ≤ 2 * (24 + 8 * c₁ + 16 * c₂ + 64 * c₃) * Real.sqrt d := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hc₂0 : 0 < c₂ := (Real.exp_pos 1).trans_le hc₂
    have h0 : heavySum G d x y = 0 := by simp [heavySum]
    rw [h0]
    exact mul_nonneg (by linarith) (Real.sqrt_nonneg d)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- (a) the heavy pairs are at most the block sum
  have hstep : heavySum G d x y ≤ ∑ i ∈ fo3bAux_ind x, ∑ j ∈ fo3bAux_ind y,
      (if Real.sqrt d < (2 : ℝ) ^ (i + j) then
        edgeCount G (fo3bAux_block x i) (fo3bAux_block y j) * (2 : ℝ) ^ (i + j) / n else 0) := by
    calc heavySum G d x y
        = ∑ u, ∑ v,
            (if Real.sqrt d / n < |x u * y v| then |x u| * G.adjMatrix ℝ u v * |y v| else 0) :=
          rfl
      _ = ∑ u ∈ fo3bAux_supp x, ∑ v,
            (if Real.sqrt d / n < |x u * y v| then |x u| * G.adjMatrix ℝ u v * |y v| else 0) := by
          refine (Finset.sum_subset (Finset.subset_univ _) fun u _ hu => ?_).symm
          have hu0 : x u = 0 := by simpa [fo3bAux_mem_supp] using hu
          simp [hu0]
      _ = ∑ u ∈ fo3bAux_supp x, ∑ v ∈ fo3bAux_supp y,
            (if Real.sqrt d / n < |x u * y v| then |x u| * G.adjMatrix ℝ u v * |y v| else 0) := by
          refine Finset.sum_congr rfl fun u _ =>
            (Finset.sum_subset (Finset.subset_univ _) fun v _ hv => ?_).symm
          have hv0 : y v = 0 := by simpa [fo3bAux_mem_supp] using hv
          simp [hv0]
      _ ≤ ∑ u ∈ fo3bAux_supp x, ∑ v ∈ fo3bAux_supp y,
            (if Real.sqrt d < (2 : ℝ) ^ (fo3bAux_idx x u + fo3bAux_idx y v) then
              G.adjMatrix ℝ u v * (2 : ℝ) ^ (fo3bAux_idx x u + fo3bAux_idx y v) / n else 0) :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
            fo3bAux_term_le hn (fo3bAux_adjMatrix_nonneg G u v) x y
      _ = _ := by
          rw [fo3bAux_sum_supp_eq]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
            fo3bAux_block_sum_eq G d x y i j
  -- (b) the six cases on the block data
  refine hstep.trans (sum_blocks_le hn' hd hc₁ hc₂ hc₃ (fo3bAux_ind x) (fo3bAux_ind y)
    (fun i => ((fo3bAux_block x i).card : ℝ)) (fun j => ((fo3bAux_block y j).card : ℝ))
    (fun i j => edgeCount G (fo3bAux_block x i) (fo3bAux_block y j))
    (fun _ hi => fo3bAux_card_block x hi) (fun _ hj => fo3bAux_card_block y hj)
    (fo3bAux_sum_alpha hn x hx) (fo3bAux_sum_alpha hn y hy)
    (fun _ _ _ _ => fo3bAux_edgeCount_nonneg G _ _)
    (fun _ _ _ _ => ⟨fo3bAux_edgeCount_le hdeg _ _, ?_⟩)
    (fun _ _ _ _ => hdisc _ _))
  rw [fo3bAux_edgeCount_comm]
  exact fo3bAux_edgeCount_le hdeg _ _

end External.FeigeOfek
