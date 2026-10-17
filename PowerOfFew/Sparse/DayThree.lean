module

public import PowerOfFew.Sparse.Degrees
public import PowerOfFew.Sparse.MatrixNorm

/-!
# Sparse paper, Section 2.4: Step 3, the third day onwards

Lemma 2.5 (deterministic, spectral) and Lemma 2.6 of the sparse paper. Lemma 2.6 uses the spectral
bound of Lemma A.7 and the minimum degree bound of Lemma A.4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- The all-ones `n × n` matrix `𝟏𝟏ᵀ`. -/
def onesMat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun _ _ => 1

/-! ### Helpers for Lemma 2.5 -/

open Classical in
/-- `∑_u 1_B(u) = |B|`. -/
private theorem mainAux_sum_indicator {n : ℕ} (B : Set (Fin n)) :
    ∑ u, (if u ∈ B then (1 : ℝ) else 0) = B.ncard := by
  classical
  rw [Finset.sum_boole]
  have hB : B = ↑(Finset.univ.filter fun u => u ∈ B) := by ext u; simp
  conv_rhs => rw [hB]
  rw [Set.ncard_coe_finset]

open Classical in
/-- The vector `v = 1_B − b_t 𝟏` of the proof of Lemma 2.5, `b_t = |B|/n`, is orthogonal to `𝟏`. -/
private theorem mainAux_sum_v {n : ℕ} (hn : 0 < n) (B : Set (Fin n)) :
    ∑ u, ((if u ∈ B then (1 : ℝ) else 0) - B.ncard / n) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_sub_distrib, mainAux_sum_indicator, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

open Classical in
/-- `‖v‖² = b_t(1 − b_t) n = (1 − b_t)|B|` for `v = 1_B − b_t 𝟏`, `b_t = |B|/n`. -/
private theorem mainAux_sum_v_sq {n : ℕ} (hn : 0 < n) (B : Set (Fin n)) :
    ∑ u, ((if u ∈ B then (1 : ℝ) else 0) - B.ncard / n) ^ 2 = (1 - B.ncard / n) * B.ncard := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h : ∀ u, ((if u ∈ B then (1 : ℝ) else 0) - B.ncard / n) ^ 2 =
      (1 - 2 * ((B.ncard : ℝ) / n)) * (if u ∈ B then (1 : ℝ) else 0) + ((B.ncard : ℝ) / n) ^ 2 := by
    intro u
    by_cases hu : u ∈ B
    · rw [ite_eq_left hu]; ring
    · rw [ite_eq_right hu]; ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, mainAux_sum_indicator, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

open Classical in
/-- `(A_G v)_w = d_B(w) − c d(w)` for `v = 1_B − c 𝟏`. -/
private theorem mainAux_adjMat_mulVec {n : ℕ} (G : SimpleGraph (Fin n)) (B : Set (Fin n))
    (c : ℝ) (w : Fin n) :
    Matrix.mulVec (adjMat G) (fun u => (if u ∈ B then (1 : ℝ) else 0) - c) w =
      (nbrCount G B w : ℝ) - c * degree G w := by
  classical
  have hB : (nbrCount G B w : ℝ) = ∑ u, if G.Adj w u ∧ u ∈ B then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole]
    have : {u | G.Adj w u ∧ u ∈ B} = ↑(Finset.univ.filter fun u => G.Adj w u ∧ u ∈ B) := by
      ext u; simp
    simp only [nbrCount, this, Set.ncard_coe_finset]
  have hd : (degree G w : ℝ) = ∑ u, if G.Adj w u then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole]
    have : G.neighborSet w = ↑(Finset.univ.filter fun u => G.Adj w u) := by
      ext u; simp
    simp only [degree, this, Set.ncard_coe_finset]
  rw [hB, hd, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [Matrix.mulVec, dotProduct, adjMat, Matrix.of_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases h1 : G.Adj w u <;> by_cases h2 : u ∈ B <;> simp [h1, h2]

/-- The operator norm bound `‖M v‖² ≤ ‖M‖²_op ‖v‖²`, in coordinates. -/
private theorem mainAux_sum_sq_mulVec_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) : ∑ w, Matrix.mulVec M v w ^ 2 ≤ specNorm M ^ 2 * ∑ u, v u ^ 2 := by
  have h := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) M).le_opNorm (WithLp.toLp 2 v)
  rw [Matrix.toEuclideanCLM_toLp] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at h2
  exact h2

/-- **Lemma 2.5** (`S:lem:hypo-blue-bound-2`). For any Blue set `B_t` and any
`1/2 > b ≥ |B_t| / n`, either `B_{t+1} = ∅` or
`|B_{t+1}| (avg_{v ∈ B_{t+1}} d(v))² ≤ inf_x ‖A_G − x 𝟏𝟏ᵀ‖²_op (1 − b)/(1/2 − b)² |B_t|`. -/
theorem lemma2_5 {n : ℕ} (G : SimpleGraph (Fin n)) (B : Set (Fin n)) {b : ℝ} (hb : b < 1 / 2)
    (hBb : (B.ncard : ℝ) ≤ b * n) :
    majorityStep G B = ∅ ∨
      (∑ᶠ v ∈ majorityStep G B, (degree G v : ℝ)) ^ 2 / (majorityStep G B).ncard ≤
        (⨅ x : ℝ, specNorm (adjMat G - x • onesMat n) ^ 2) * ((1 - b) / (1 / 2 - b) ^ 2) *
          B.ncard := by
  classical
  rcases Set.eq_empty_or_nonempty (majorityStep G B) with hS | ⟨w₀, hw₀⟩
  · exact Or.inl hS
  right
  have hn : 0 < n := w₀.pos
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  -- `b_t = |B_t|/n` and `v = 1_{B_t} − b_t 𝟏`
  set c : ℝ := (B.ncard : ℝ) / n with hc
  have hc0 : 0 ≤ c := by positivity
  have hcb : c ≤ b := by rw [hc, div_le_iff₀ hnR]; exact hBb
  have hc2 : 0 < 1 / 2 - c := by linarith
  set v : Fin n → ℝ := fun u => (if u ∈ B then (1 : ℝ) else 0) - c with hv
  -- `𝟏ᵀ v = 0` and `‖v‖² = b_t(1 − b_t)n = (1 − b_t)|B_t|`
  have hsumv : ∑ u, v u = 0 := mainAux_sum_v hn B
  have hnormv : ∑ u, v u ^ 2 = (1 - c) * B.ncard := mainAux_sum_v_sq hn B
  -- `B_{t+1}` as a finset
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin n), (T : Set (Fin n)) = majorityStep G B :=
    ⟨Finset.univ.filter (· ∈ majorityStep G B), by ext; simp⟩
  have hTpos : (0 : ℝ) < T.card := by
    have : w₀ ∈ T := by rw [← Finset.mem_coe, hT]; exact hw₀
    exact_mod_cast Finset.card_pos.2 ⟨w₀, this⟩
  rw [← hT, finsum_mem_coe_finset, Set.ncard_coe_finset]
  -- for every `x`, `‖A v‖² = ‖(A − x 𝟏𝟏ᵀ) v‖² ≤ ‖A − x 𝟏𝟏ᵀ‖² (1 − b_t)|B_t|`
  have hup : ∀ x : ℝ, ∑ w, Matrix.mulVec (adjMat G) v w ^ 2 ≤
      specNorm (adjMat G - x • onesMat n) ^ 2 * ((1 - c) * B.ncard) := by
    intro x
    have hMv : Matrix.mulVec (adjMat G - x • onesMat n) v = Matrix.mulVec (adjMat G) v := by
      have h1 : Matrix.mulVec (onesMat n) v = 0 := by
        ext w
        simp only [onesMat, Matrix.mulVec, dotProduct, Matrix.of_apply, one_mul, Pi.zero_apply]
        exact hsumv
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, h1, smul_zero, sub_zero]
    rw [← hnormv, ← hMv]
    exact mainAux_sum_sq_mulVec_le _ v
  -- `‖A v‖² = ∑_w (d_{B_t}(w) − b_t d(w))² ≥ (1/2 − b_t)² ∑_{w ∈ B_{t+1}} d(w)²`
  have hlow : (1 / 2 - c) ^ 2 * ∑ w ∈ T, (degree G w : ℝ) ^ 2 ≤
      ∑ w, Matrix.mulVec (adjMat G) v w ^ 2 := by
    rw [Finset.mul_sum]
    calc ∑ w ∈ T, (1 / 2 - c) ^ 2 * (degree G w : ℝ) ^ 2
        ≤ ∑ w ∈ T, Matrix.mulVec (adjMat G) v w ^ 2 := by
          refine Finset.sum_le_sum fun w hw => ?_
          have hw' : w ∈ majorityStep G B := by rw [← hT]; exact hw
          rw [hv, mainAux_adjMat_mulVec]
          -- a vertex of `B_{t+1}` has `d_{B_t}(w) ≥ d(w)/2`
          have hmaj : (degree G w : ℝ) ≤ 2 * nbrCount G B w := by
            have hle : nbrCount G Bᶜ w ≤ nbrCount G B w := by
              have hw'' : nbrCount G Bᶜ w < nbrCount G B w ∨
                  (nbrCount G Bᶜ w = nbrCount G B w ∧ w ∈ B) := hw'
              rcases hw'' with h | ⟨h, _⟩
              · exact h.le
              · exact h.le
            have hsum := nbrCount_add_nbrCount_compl G B w
            have : degree G w ≤ 2 * nbrCount G B w := by omega
            exact_mod_cast this
          have hd0 : (0 : ℝ) ≤ degree G w := Nat.cast_nonneg _
          have h1 : 0 ≤ (1 / 2 - c) * degree G w := mul_nonneg hc2.le hd0
          have h2 : (1 / 2 - c) * degree G w ≤ nbrCount G B w - c * degree G w := by linarith
          calc (1 / 2 - c) ^ 2 * (degree G w : ℝ) ^ 2 = ((1 / 2 - c) * degree G w) ^ 2 := by ring
            _ ≤ ((nbrCount G B w : ℝ) - c * degree G w) ^ 2 := pow_le_pow_left₀ h1 h2 2
      _ ≤ ∑ w, Matrix.mulVec (adjMat G) v w ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun w _ _ => sq_nonneg _)
  -- Cauchy–Schwarz: `|B_{t+1}| (avg d)² ≤ ∑_{w ∈ B_{t+1}} d(w)²`
  have hCS : (∑ w ∈ T, (degree G w : ℝ)) ^ 2 / T.card ≤ ∑ w ∈ T, (degree G w : ℝ) ^ 2 := by
    rw [div_le_iff₀ hTpos]
    have := sq_sum_le_card_mul_sum_sq (s := T) (f := fun w => (degree G w : ℝ))
    linarith
  -- `(1 − b_t)/(1/2 − b_t)² ≤ (1 − b)/(1/2 − b)²` since `b_t ≤ b < 1/2`
  have hratio : (1 - c) / (1 / 2 - c) ^ 2 ≤ (1 - b) / (1 / 2 - b) ^ 2 := by
    have hb2 : 0 < 1 / 2 - b := by linarith
    rw [div_le_div_iff₀ (pow_pos hc2 2) (pow_pos hb2 2)]
    have key : 0 ≤ (b - c) * ((1 / 2 - c + (1 / 2 - b)) / 2 + (1 / 2 - c) * (1 / 2 - b)) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [key]
  -- pass to the infimum over `x`
  have hK : 0 ≤ (1 - b) / (1 / 2 - b) ^ 2 * B.ncard := by
    have : 0 < 1 - b := by linarith
    positivity
  rw [mul_assoc, Real.iInf_mul_of_nonneg hK]
  refine le_ciInf fun x => ?_
  have hfx : 0 ≤ specNorm (adjMat G - x • onesMat n) ^ 2 := sq_nonneg _
  calc (∑ w ∈ T, (degree G w : ℝ)) ^ 2 / T.card ≤ ∑ w ∈ T, (degree G w : ℝ) ^ 2 := hCS
    _ ≤ specNorm (adjMat G - x • onesMat n) ^ 2 * ((1 - c) / (1 / 2 - c) ^ 2 * B.ncard) := by
        rw [show specNorm (adjMat G - x • onesMat n) ^ 2 * ((1 - c) / (1 / 2 - c) ^ 2 * B.ncard)
            = specNorm (adjMat G - x • onesMat n) ^ 2 * ((1 - c) * B.ncard) / (1 / 2 - c) ^ 2 by
              ring, le_div_iff₀ (pow_pos hc2 2)]
        linarith [hlow, hup x]
    _ ≤ specNorm (adjMat G - x • onesMat n) ^ 2 * ((1 - b) / (1 / 2 - b) ^ 2 * B.ncard) := by
        gcongr

/-! ### Helpers for Lemma 2.6 -/

/-- `‖A_G − p 𝟏𝟏ᵀ‖_op ≤ ‖A_G − E A_G‖_op + ‖p I‖_op ≤ ‖A_G − E A_G‖_op + p`, since
`A_G − p 𝟏𝟏ᵀ = (A_G − E A_G) − p I` (the first display of the proof of Lemma 2.6). -/
private theorem mainAux_specNorm_sub_onesMat_le {n : ℕ} (G : SimpleGraph (Fin n)) {p : ℝ}
    (hp : 0 ≤ p) : specNorm (adjMat G - p • onesMat n) ≤ specNorm (adjMat G - meanAdj n p) + p := by
  have hM : adjMat G - p • onesMat n =
      (adjMat G - meanAdj n p) - p • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext u v
    simp only [Matrix.sub_apply, Matrix.smul_apply, onesMat, meanAdj, Matrix.of_apply,
      Matrix.one_apply, smul_eq_mul]
    split_ifs <;> ring
  rw [hM]
  unfold specNorm
  rw [map_sub, map_smul, map_one]
  have h1 : ‖(1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp)
  calc _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (adjMat G - meanAdj n p)‖ +
        ‖p • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_smul, Real.norm_of_nonneg hp]
      nlinarith

/-- The deterministic step of Lemma 2.6: on the events `‖A_G − E A_G‖ ≤ C √(pn)` (Lemma A.7) and
`min_v d(v) ≥ α p n` (Lemma A.4), Lemma 2.5 with `x = p` gives
`|B_{t+1}| (α p n)² ≤ (C + 1)² p n (1 − b)/(1/2 − b)² |B_t|` whenever `|B_t| ≤ b n`, that is
`|B_{t+1}| ≤ (A/(pn)) |B_t|` with `A = (C + 1)² (1 − b) / (α² (1/2 − b)²)`. -/
private theorem mainAux_step {n : ℕ} (G : SimpleGraph (Fin n)) {p b C α : ℝ} (hb : b < 1 / 2)
    (hα : 0 < α) (hp0 : 0 < p) (hp1 : p ≤ 1) (hn : 1 ≤ (n : ℝ))
    (hspec : specNorm (adjMat G - meanAdj n p) ≤ C * Real.sqrt (p * n))
    (hdeg : ∀ v, α * p * n ≤ degree G v) (B : Set (Fin n)) (hB : (B.ncard : ℝ) ≤ b * n) :
    ((majorityStep G B).ncard : ℝ) ≤
      (C + 1) ^ 2 * ((1 - b) / (1 / 2 - b) ^ 2) / α ^ 2 / (p * n) * B.ncard := by
  classical
  have hpn : 0 < p * n := by positivity
  have hK₀ : 0 < (1 - b) / (1 / 2 - b) ^ 2 := div_pos (by linarith) (pow_pos (by linarith) 2)
  rcases Set.eq_empty_or_nonempty (majorityStep G B) with hS | ⟨w₀, hw₀⟩
  · rw [hS, Set.ncard_empty, Nat.cast_zero]
    positivity
  rcases lemma2_5 G B hb hB with hS | hS
  · exact absurd (hS ▸ hw₀) (Set.notMem_empty w₀)
  -- `‖A_G − p 𝟏𝟏ᵀ‖ ≤ ‖A_G − E A_G‖ + ‖p I‖ ≤ (C + 1) √(pn)` (first display of the proof)
  have hsq : Real.sqrt (p * n) ^ 2 = p * n := Real.sq_sqrt hpn.le
  have hp_le : p ≤ Real.sqrt (p * n) := by
    rw [Real.le_sqrt hp0.le hpn.le]; nlinarith
  have hspec' : specNorm (adjMat G - p • onesMat n) ≤ (C + 1) * Real.sqrt (p * n) := by
    have := mainAux_specNorm_sub_onesMat_le G hp0.le
    linarith
  have hf : specNorm (adjMat G - p • onesMat n) ^ 2 ≤ (C + 1) ^ 2 * (p * n) := by
    have h0 : 0 ≤ specNorm (adjMat G - p • onesMat n) := norm_nonneg _
    calc _ ≤ ((C + 1) * Real.sqrt (p * n)) ^ 2 := pow_le_pow_left₀ h0 hspec' 2
      _ = _ := by rw [mul_pow, hsq]
  have hinf : (⨅ x : ℝ, specNorm (adjMat G - x • onesMat n) ^ 2) ≤ (C + 1) ^ 2 * (p * n) :=
    (ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact sq_nonneg _⟩ p).trans hf
  -- the average degree in `B_{t+1}` is at least the minimum degree `α p n`
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin n), (T : Set (Fin n)) = majorityStep G B :=
    ⟨Finset.univ.filter (· ∈ majorityStep G B), by ext; simp⟩
  have hTpos : (0 : ℝ) < T.card := by
    have : w₀ ∈ T := by rw [← Finset.mem_coe, hT]; exact hw₀
    exact_mod_cast Finset.card_pos.2 ⟨w₀, this⟩
  rw [← hT, finsum_mem_coe_finset, Set.ncard_coe_finset] at hS
  rw [← hT, Set.ncard_coe_finset]
  have hsum : (T.card : ℝ) * (α * p * n) ≤ ∑ w ∈ T, (degree G w : ℝ) := by
    have := Finset.card_nsmul_le_sum T (fun w => (degree G w : ℝ)) (α * p * n)
      (fun w _ => hdeg w)
    simpa [nsmul_eq_mul] using this
  have hαpn : 0 < α * p * n := by positivity
  have hlow : (T.card : ℝ) * (α * p * n) ^ 2 ≤ (∑ w ∈ T, (degree G w : ℝ)) ^ 2 / T.card := by
    rw [le_div_iff₀ hTpos]
    have h0 : 0 ≤ (T.card : ℝ) * (α * p * n) := by positivity
    nlinarith [pow_le_pow_left₀ h0 hsum 2]
  -- `|B_{t+1}| (α p n)² ≤ (C + 1)² p n (1 − b)/(1/2 − b)² |B_t|`
  have hB0 : (0 : ℝ) ≤ B.ncard := Nat.cast_nonneg _
  have key : (T.card : ℝ) * (α * p * n) ^ 2 ≤
      (C + 1) ^ 2 * (p * n) * ((1 - b) / (1 / 2 - b) ^ 2) * B.ncard := by
    calc _ ≤ _ := hlow
      _ ≤ _ := hS
      _ ≤ _ := by gcongr
  rw [show (C + 1) ^ 2 * ((1 - b) / (1 / 2 - b) ^ 2) / α ^ 2 / (p * n) * B.ncard =
      (C + 1) ^ 2 * (p * n) * ((1 - b) / (1 / 2 - b) ^ 2) * B.ncard / (α * p * n) ^ 2 by
    field_simp, le_div_iff₀ (by positivity)]
  exact key

/-- Iterating the step of Lemma 2.6: if every Blue set of at most `m` vertices shrinks by the
factor `r ≤ 1` in one day, then a Blue set of at most `m` vertices has at most `r^t |B|` Blue
vertices after `t` days (the invariant `|B_t| ≤ b n` persists). -/
private theorem mainAux_iter {n : ℕ} (G : SimpleGraph (Fin n)) {r m : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1)
    (hstep : ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ m → ((majorityStep G B).ncard : ℝ) ≤ r * B.ncard)
    (B : Set (Fin n)) (hB : (B.ncard : ℝ) ≤ m) (t : ℕ) :
    ((blueAfter G B t).ncard : ℝ) ≤ r ^ t * B.ncard := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [blueAfter_succ]
    have hB0 : (0 : ℝ) ≤ B.ncard := Nat.cast_nonneg _
    have h1 : ((blueAfter G B t).ncard : ℝ) ≤ m :=
      ih.trans ((mul_le_of_le_one_left hB0 (pow_le_one₀ hr0 hr1)).trans hB)
    calc ((majorityStep G (blueAfter G B t)).ncard : ℝ) ≤ r * (blueAfter G B t).ncard :=
          hstep _ h1
      _ ≤ r * (r ^ t * B.ncard) := by gcongr
      _ = r ^ (t + 1) * B.ncard := by ring

/-- The deterministic part of Lemma 2.6: on the events of Lemmas A.7 and A.4, every Blue set of
at most `b n` vertices shrinks by the factor `r = A/(pn) ≤ 1` each day (`mainAux_step`), so that it
vanishes after `T = ⌊log_{pn/A}(b n)⌋ + 1` days, and `T ≤ 3 log n / log(pn)` because
`pn ≥ A² + 1` gives `log(pn/A) ≥ log(pn)/2`. Here `A ≥ 1` bounds the paper's
`(C + 1)² (1 − b)/(α² (1/2 − b)²)`. -/
private theorem mainAux_vanish {n : ℕ} (G : SimpleGraph (Fin n)) {p b C α A : ℝ} (hb0 : 0 ≤ b)
    (hb : b < 1 / 2) (hα : 0 < α) (hp0 : 0 < p) (hp1 : p ≤ 1) (hn : 1 ≤ (n : ℝ)) (hA1 : 1 ≤ A)
    (hA : (C + 1) ^ 2 * ((1 - b) / (1 / 2 - b) ^ 2) / α ^ 2 ≤ A) (hpnA : A ^ 2 + 1 ≤ p * n)
    (hspec : specNorm (adjMat G - meanAdj n p) ≤ C * Real.sqrt (p * n))
    (hdeg : ∀ v, α * p * n ≤ degree G v) (B : Set (Fin n)) (hB : (B.ncard : ℝ) ≤ b * n) :
    ∃ t : ℕ, (t : ℝ) ≤ 3 * (Real.log n / Real.log (p * n)) ∧ blueAfter G B t = ∅ := by
  have hnpos : (0 : ℝ) < n := by linarith
  have hA0 : 0 < A := by linarith
  have hpn0 : 0 < p * n := by positivity
  have hAA : A ≤ A ^ 2 := by nlinarith
  have hpnA' : A < p * n := by linarith
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn
  -- every Blue set of at most `b n` vertices shrinks by the factor `r = A/(pn) ≤ 1`
  set r : ℝ := A / (p * n) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by rw [hr, div_le_one hpn0]; exact hpnA'.le
  have hstep : ∀ B' : Set (Fin n), (B'.ncard : ℝ) ≤ b * n →
      ((majorityStep G B').ncard : ℝ) ≤ r * B'.ncard := by
    intro B' hB'
    refine (mainAux_step G hb hα hp0 hp1 hn hspec hdeg B' hB').trans ?_
    rw [hr]
    gcongr
  -- `T = ⌊log_{pn/A} (b n)⌋ + 1` days
  have hlogpn : 0 < Real.log (p * n) := Real.log_pos (by nlinarith)
  have hlogpn_le : Real.log (p * n) ≤ Real.log n :=
    Real.log_le_log hpn0 (mul_le_of_le_one_left hnpos.le hp1)
  have hratio1 : 1 ≤ Real.log n / Real.log (p * n) := by rw [le_div_iff₀ hlogpn]; linarith
  have hlogA : 2 * Real.log A ≤ Real.log (p * n) := by
    have h := Real.log_le_log (by positivity : 0 < A ^ 2) (by linarith : A ^ 2 ≤ p * n)
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  have hlogdiv : Real.log (p * n / A) = Real.log (p * n) - Real.log A :=
    Real.log_div hpn0.ne' hA0.ne'
  have hlogdiv2 : Real.log (p * n) / 2 ≤ Real.log (p * n / A) := by rw [hlogdiv]; linarith
  have hlogdivpos : 0 < Real.log (p * n / A) := by linarith
  have hbn0 : 0 ≤ b * n := mul_nonneg hb0 hnpos.le
  have hlogbn : Real.log (b * n) ≤ Real.log n := by
    rcases hbn0.eq_or_lt with h | h
    · rw [← h, Real.log_zero]; exact hlogn0
    · exact Real.log_le_log h (mul_le_of_le_one_left hnpos.le (by linarith))
  set x : ℝ := Real.log (b * n) / Real.log (p * n / A) with hx
  have hx2 : x ≤ 2 * (Real.log n / Real.log (p * n)) := by
    calc x ≤ Real.log n / Real.log (p * n / A) :=
          div_le_div_of_nonneg_right hlogbn hlogdivpos.le
      _ ≤ Real.log n / (Real.log (p * n) / 2) :=
          div_le_div_of_nonneg_left hlogn0 (by positivity) hlogdiv2
      _ = 2 * (Real.log n / Real.log (p * n)) := by field_simp
  refine ⟨⌊x⌋₊ + 1, ?_, ?_⟩
  · -- `T ≤ 2 log n / log(pn) + 1 ≤ 3 log n / log(pn)`
    have hfloor : (⌊x⌋₊ : ℝ) ≤ 2 * (Real.log n / Real.log (p * n)) := by
      rcases le_or_gt 0 x with h | h
      · exact (Nat.floor_le h).trans hx2
      · rw [Nat.floor_eq_zero.2 (by linarith), Nat.cast_zero]; positivity
    push_cast
    linarith
  · -- `|B_T| ≤ (A/(pn))^T |B| ≤ (A/(pn))^T b n < 1`
    have hdecay := mainAux_iter G hr0 hr1 hstep B hB (⌊x⌋₊ + 1)
    have hlt : r ^ (⌊x⌋₊ + 1) * (b * n) < 1 := by
      rcases hbn0.eq_or_lt with h | h
      · rw [← h, mul_zero]; exact one_pos
      have hfl : x < (⌊x⌋₊ + 1 : ℕ) := by push_cast; exact Nat.lt_floor_add_one x
      have hlog : Real.log (b * n) < ((⌊x⌋₊ + 1 : ℕ) : ℝ) * Real.log (p * n / A) := by
        rw [hx, div_lt_iff₀ hlogdivpos] at hfl; exact hfl
      have hpow : b * n < (p * n / A) ^ (⌊x⌋₊ + 1) := by
        rw [← Real.log_lt_log_iff h (by positivity), Real.log_pow]; exact hlog
      have hrpow : r ^ (⌊x⌋₊ + 1) = ((p * n / A) ^ (⌊x⌋₊ + 1))⁻¹ := by
        rw [hr, ← inv_pow, inv_div]
      rw [hrpow, inv_mul_eq_div, div_lt_one (by positivity)]
      exact hpow
    have hcard : ((blueAfter G B (⌊x⌋₊ + 1)).ncard : ℝ) < 1 := by
      have hpow0 : 0 ≤ r ^ (⌊x⌋₊ + 1) := by positivity
      calc _ ≤ r ^ (⌊x⌋₊ + 1) * B.ncard := hdecay
        _ ≤ r ^ (⌊x⌋₊ + 1) * (b * n) := by gcongr
        _ < 1 := hlt
    have hzero : (blueAfter G B (⌊x⌋₊ + 1)).ncard = 0 := by
      have : (blueAfter G B (⌊x⌋₊ + 1)).ncard < 1 := by exact_mod_cast hcard
      omega
    exact (Set.ncard_eq_zero).1 hzero

/-- **Lemma 2.6** (`S:lem:step3`). Consider majority dynamics on `G ∼ G(n, p)` with
`pn ≥ (1 + λ) log n`, and assume `|B₂| ≤ b n` for a constant `b < 1/2`. Then with probability at
least `1 − 2 n^(−λ/2)` there is a time `t* = O(log_{pn} n)` with `B_{t*} = ∅`.

Reading: the event is that of the proof: the graph empties every Blue set of at most `b n`
vertices within `K log n / log(pn)` days; `K` and the threshold `N` for `n` depend on `λ` and `b`
(the proof takes `n` large enough).

Departure from the paper (an off-by-one in the number of days): the paper stops after
`T = ⌈log_{pn/A}(b n)⌉` days, but `|B_T| ≤ (A/(pn))^T b n` is only at most `1` (not less than `1`)
when `log_{pn/A}(b n)` is an integer. The proof here runs `⌊log_{pn/A}(b n)⌋ + 1` days, after which
`|B_T| < 1`. It takes `n` large enough that `log n ≥ A² + 1`, so that `pn/A ≥ √(pn)` and the number
of days is at most `3 log n / log(pn)`, and it replaces `A` by `max{A, 1}`. -/
theorem lemma2_6 {lam b : ℝ} (hlam : 0 < lam)
    (hb0 : 0 ≤ b) (hb : b < 1 / 2) :
    ∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ p : ℝ, 0 < p → p ≤ 1 → (1 + lam) * Real.log n ≤ p * n →
      1 - 2 * (n : ℝ) ^ (-(lam / 2)) ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
        (B.ncard : ℝ) ≤ b * n →
          ∃ t : ℕ, (t : ℝ) ≤ K * (Real.log n / Real.log (p * n)) ∧ blueAfter G B t = ∅) := by
  -- Lemma A.7 with `c = 1 + λ`, `a = λ`, and Lemma A.4 with `ε = λ`, `α = α_λ = e^{−(8/λ + 7)}`
  obtain ⟨C, hC⟩ := lemmaA_7 (c := 1 + lam) (a := lam) (by linarith) hlam
  have hα0 : 0 < Real.exp (-(8 / lam + 7)) := Real.exp_pos _
  -- `A ≥ (C + 1)² (1 − b) / (α² (1/2 − b)²)`, taken at least `1`
  obtain ⟨A, hA1, hA⟩ : ∃ A : ℝ, 1 ≤ A ∧
      (C + 1) ^ 2 * ((1 - b) / (1 / 2 - b) ^ 2) / Real.exp (-(8 / lam + 7)) ^ 2 ≤ A :=
    ⟨max ((C + 1) ^ 2 * ((1 - b) / (1 / 2 - b) ^ 2) / Real.exp (-(8 / lam + 7)) ^ 2) 1,
      le_max_right _ _, le_max_left _ _⟩
  refine ⟨3, max ⌈4 / lam + 4⌉₊ ⌈Real.exp (A ^ 2 + 1)⌉₊, ?_⟩
  intro n hn p hp0 hp1 hpn
  -- `n` is large: `n ≥ N_λ = 4/λ + 4` and `log n ≥ A² + 1`, so that `pn ≥ A² + 1`
  have hn1 : (4 / lam + 4 : ℝ) ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_left hn)
  have hn2 : Real.exp (A ^ 2 + 1) ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hn)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hn2
  have hlogn : A ^ 2 + 1 ≤ Real.log n := by rw [Real.le_log_iff_exp_le hnpos]; exact hn2
  have hn1' : (1 : ℝ) ≤ n := by
    have := Real.add_one_le_exp (A ^ 2 + 1)
    nlinarith [sq_nonneg A]
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1'
  have hpnA : A ^ 2 + 1 ≤ p * n := by nlinarith
  have hrpow : (n : ℝ) ^ (-lam) ≤ (n : ℝ) ^ (-(lam / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hn1' (by linarith)
  -- the two events: probability at least `1 − n^{−λ} − n^{−λ/2} ≥ 1 − 2 n^{−λ/2}`
  have h7 := hC n p hp0 hp1 hpn
  have h4 := lemmaA_4 hlam hn1 hp0 hp1 hpn
  have hand := gnpProb_and_ge (n := n) (p := p)
    (fun G => specNorm (adjMat G - meanAdj n p) ≤ C * Real.sqrt (p * n))
    (fun G => ∀ v, Real.exp (-(8 / lam + 7)) * p * n ≤ degree G v)
  -- on both events, every Blue set of at most `b n` vertices vanishes (`mainAux_vanish`)
  refine le_trans ?_ (le_trans hand (gnpProb_mono fun G hG B hB =>
    mainAux_vanish G hb0 hb hα0 hp0 hp1 hn1' hA1 hA hpnA hG.1 hG.2 B hB))
  linarith

end PowerOfFew.Sparse

end
