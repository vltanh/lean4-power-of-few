module

public import PowerOfFew.Dense.BinomialDifference
public import PowerOfFew.Model.Gnp
public import PowerOfFew.Model.Majority
public import PowerOfFew.Model.EdgeConditioning
public import Basic.Probability.Concentration

/-!
# Dense paper, Section 2: Day One

Lemma 2.1 and Claims 2.5 and 2.6 of the dense paper (journal version): after the first day, the
Red camp has gained about `√n` vertices, by Chebyshev's inequality applied to `|R₁|`.

Notation: `σ = √(p(1 − p))`, so that `1 − 2σ² = 1 − 2p + 2p²`; `R₁ = (blueAfter G B₀ 1)ᶜ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Dense

variable {n : ℕ} {p : ℝ}

/-! ### Helpers: indicators, neighbour counts and edge indicators -/

/-- Every function of the edge variables is measurable. -/
theorem dayOneAux_measurable {β : Type*} [MeasurableSpace β] (f : EdgeVars n → β) :
    Measurable f :=
  fun _ _ => measurableSet_edgeVars _

/-- Bounded functions of the edge variables are in every `Lᵠ`. -/
theorem dayOneAux_memLp {f : EdgeVars n → ℝ} {C : ℝ} (hf : ∀ ω, |f ω| ≤ C) (q : ENNReal) :
    MemLp f q (edgeLaw n p) :=
  MemLp.of_bound (dayOneAux_measurable f).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hf ω)

/-- Bounded functions of the edge variables are integrable. -/
theorem dayOneAux_integrable {f : EdgeVars n → ℝ} {C : ℝ} (hf : ∀ ω, |f ω| ≤ C) :
    Integrable f (edgeLaw n p) :=
  (dayOneAux_memLp hf 1).integrable le_rfl

open Classical in
/-- The expectation of the indicator of an event of the edge variables is its probability. -/
theorem dayOneAux_integral_ite (P : EdgeVars n → Prop) :
    ∫ ω, (if P ω then (0 : ℝ) else 1) ∂(edgeLaw n p) = (edgeLaw n p).real {ω | ¬ P ω} := by
  have h : (fun ω => if P ω then (0 : ℝ) else 1) = Set.indicator {ω | ¬ P ω} 1 := by
    ext ω
    by_cases hP : P ω <;> simp [hP]
  rw [h, integral_indicator_one (measurableSet_edgeVars _)]

open Classical in
/-- The size of the complement of `T` is the sum of the indicators of `v ∉ T`. -/
theorem dayOneAux_ncard_compl (T : Set (Fin n)) :
    ((Tᶜ.ncard : ℕ) : ℝ) = ∑ v, if v ∈ T then (0 : ℝ) else 1 := by
  rw [Set.ncard_eq_toFinset_card', Finset.sum_ite, Finset.sum_const_zero, zero_add,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext v
  simp

/-- The number of neighbours of `v` in `S` is the sum of the indicators of the edges `vu`, over the
vertices `u ≠ v` in `S`, indexed by the subtype `{u // u ≠ v}`. -/
theorem dayOneAux_nbrCount_eq_sum (ω : EdgeVars n) (S : Set (Fin n)) [DecidablePred (· ∈ S)]
    (v : Fin n) :
    (nbrCount (graphOfEdges ω) S v : ℝ) =
      ∑ u ∈ (Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ S),
        edgeInd s(v, u.1) ω := by
  classical
  rw [nbrCount_graphOfEdges]
  have h := Finset.sum_subtype_eq_sum_filter (s := Finset.univ.filter (fun u : Fin n => u ∈ S))
    (fun u => edgeInd s(v, u) ω) (p := fun u => u ≠ v)
  rw [Finset.filter_filter] at h
  have hidx : (Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ S) =
      (Finset.univ.filter (fun u : Fin n => u ∈ S)).subtype (fun u => u ≠ v) := by
    ext u; simp
  rw [hidx, h]
  exact Finset.sum_congr (by ext u; simp) (fun _ _ => rfl)

/-- `|S|` as the number of vertices in `S`. -/
theorem dayOneAux_ncard_eq_card_filter (S : Set (Fin n)) [DecidablePred (· ∈ S)] :
    S.ncard = (Finset.univ.filter (fun u : Fin n => u ∈ S)).card := by
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext u
  simp

open Classical in
/-- The number of vertices `u ≠ v` in `S` is `|S| − 1_{v ∈ S}`. -/
theorem dayOneAux_card_filter (S : Set (Fin n)) [DecidablePred (· ∈ S)] (v : Fin n) :
    ((((Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ S)).card : ℕ) : ℝ) =
      S.ncard - (if v ∈ S then 1 else 0) := by
  have h1 : ((Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ S)).card =
      ((Finset.univ.filter (fun u : Fin n => u ∈ S)).erase v).card := by
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    congr 1
    ext u
    simp [and_comm]
  rw [h1, dayOneAux_ncard_eq_card_filter S]
  by_cases hv : v ∈ S
  · rw [Finset.card_erase_of_mem (by simpa using hv), ite_eq_left hv]
    have : 0 < (Finset.univ.filter (fun u : Fin n => u ∈ S)).card :=
      Finset.card_pos.2 ⟨v, by simpa using hv⟩
    push_cast [Nat.cast_sub this]
    ring
  · rw [Finset.erase_eq_of_notMem (by simpa using hv), ite_eq_right hv]
    ring

open Classical in
/-- Equation (2.1) of the paper, in the form of Lemma 2.3: `v ∈ R₁` iff
`d_{B₀}(v) − I₀(v) < d_{R₀}(v)`, the degrees being sums of edge indicators at `v`. -/
theorem dayOneAux_notMem_iff (ω : EdgeVars n) (B : Set (Fin n)) (v : Fin n) :
    v ∉ majorityStep (graphOfEdges ω) B ↔
      ∑ u ∈ (Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ B),
          edgeInd s(v, u.1) ω + -(if v ∈ B then (0 : ℝ) else 1) <
        ∑ u ∈ (Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ Bᶜ),
          edgeInd s(v, u.1) ω := by
  rw [notMem_majorityStep_iff, ← dayOneAux_nbrCount_eq_sum ω B v,
    ← dayOneAux_nbrCount_eq_sum ω Bᶜ v]
  by_cases hv : v ∈ B
  · simp only [hv, ite_true, neg_zero, add_zero]
    exact_mod_cast Iff.rfl
  · simp only [hv, ite_false]
    constructor
    · intro h
      have h' : ((nbrCount (graphOfEdges ω) B v : ℤ) : ℝ) <
          (((nbrCount (graphOfEdges ω) Bᶜ v : ℤ) + 1 : ℤ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      linarith
    · intro h
      have h' : ((nbrCount (graphOfEdges ω) B v : ℤ) : ℝ) <
          (((nbrCount (graphOfEdges ω) Bᶜ v : ℤ) + 1 : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast h'

/-! ### Claim 2.5 -/

/-- `1 − 2σ² ≥ σ` for `σ = √(p(1 − p))`, `p ∈ [0, 1]`. -/
theorem dayOneAux_sqrt_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.sqrt (p * (1 - p)) ≤ 1 - 2 * p + 2 * p ^ 2 := by
  rw [Real.sqrt_le_left (by nlinarith [sq_nonneg (2 * p - 1)])]
  have h1 : 0 ≤ 1 - p * (1 - p) := by nlinarith
  nlinarith [mul_nonneg h1 (sq_nonneg (2 * p - 1))]

/-- `F(n, p, c) > 0` forces `c ≥ 1` (since `F(n, p, 0) < 0`) and `n ≥ 8` (since `Φ₀ < 1/2`,
`(1 − 2σ²)/σ ≥ 1` and `0.8/p > 0.8`). -/
theorem dayOneAux_of_F_pos (hp0 : 0 < p) (hp1 : p < 1) {c : ℕ}
    (hF : 0 < denseF n p c) : 1 ≤ c ∧ 8 ≤ n := by
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  have hσ : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.2 hpq
  have hK : Real.sqrt (p * (1 - p)) ≤ 1 - 2 * p + 2 * p ^ 2 := dayOneAux_sqrt_le hp0.le hp1.le
  have hKσ : 1 ≤ (1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p)) := by
    rw [le_div_iff₀ hσ]; linarith
  have h08 : 0.8 < 0.8 / p := by
    rw [lt_div_iff₀ hp0]; nlinarith
  have hsn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  unfold denseF at hF
  have hdiv : 0.6 * (1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p)) =
      0.6 * ((1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p))) := by ring
  rw [hdiv] at hF
  constructor
  · by_contra hc
    have hc0 : c = 0 := by omega
    subst hc0
    -- `√n Φ₀(min{p, 1 − p} / (σ √n)) ≤ min{p, 1 − p} / σ ≤ 1`
    set m := min p (1 - p) with hm
    have hm0 : 0 ≤ m := le_min hp0.le (by linarith)
    have hmσ : m ≤ Real.sqrt (p * (1 - p)) := by
      rw [Real.le_sqrt hm0 hpq.le, sq]
      exact mul_le_mul (min_le_left _ _) (min_le_right _ _) hm0 hp0.le
    have harg : 0 ≤ m / Real.sqrt (p * (1 - p) * n) := div_nonneg hm0 (Real.sqrt_nonneg _)
    have hΦ := Φ₀_le_div harg
    have h2π : 1 ≤ Real.sqrt (2 * Real.pi) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
    have hle1 : Real.sqrt n * Φ₀ (m / Real.sqrt (p * (1 - p) * n)) ≤ 1 := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
        have hsnpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
        have hsplit : Real.sqrt (p * (1 - p) * n) = Real.sqrt (p * (1 - p)) * Real.sqrt n :=
          Real.sqrt_mul hpq.le _
        calc Real.sqrt n * Φ₀ (m / Real.sqrt (p * (1 - p) * n))
            ≤ Real.sqrt n * (m / Real.sqrt (p * (1 - p) * n) / Real.sqrt (2 * Real.pi)) :=
              mul_le_mul_of_nonneg_left hΦ hsn
          _ ≤ Real.sqrt n * (m / Real.sqrt (p * (1 - p) * n)) := by
              apply mul_le_mul_of_nonneg_left _ hsn
              exact div_le_self harg h2π
          _ = m / Real.sqrt (p * (1 - p)) := by
              rw [hsplit]; field_simp
          _ ≤ 1 := by rw [div_le_one hσ]; exact hmσ
    simp only [Nat.cast_zero, mul_zero, zero_add] at hF
    linarith
  · by_contra hn
    have hn7 : (n : ℝ) ≤ 7 := by exact_mod_cast (by omega : n ≤ 7)
    have hsq : Real.sqrt n < 2.8 := by
      rw [Real.sqrt_lt' (by norm_num)]; linarith
    have hΦ := Φ₀_lt_half ((2 * p * c + min p (1 - p)) / Real.sqrt (p * (1 - p) * n))
    have : Real.sqrt n * Φ₀ ((2 * p * c + min p (1 - p)) / Real.sqrt (p * (1 - p) * n)) ≤
        Real.sqrt n * (1 / 2) := mul_le_mul_of_nonneg_left hΦ.le hsn
    linarith

/-- `|B₀ᶜ| = n − |B₀|`. -/
theorem dayOneAux_ncard_compl_eq (B : Set (Fin n)) : ((Bᶜ.ncard : ℕ) : ℝ) = n - B.ncard := by
  have h := Set.ncard_add_ncard_compl B
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have h' : ((B.ncard + Bᶜ.ncard : ℕ) : ℝ) = n := by exact_mod_cast h
  push_cast at h'
  linarith

open Classical in
/-- The per-vertex bound in the proof of Claim 2.5:
`P(v ∈ R₁) ≥ 1/2 + Φ₀((2pc + min{p, 1 − p}) / (σ √n)) − 0.6 (1 − 2σ²) / (σ √n)`.
As in the paper: by equation (2.1), `v ∈ R₁` iff `d_{R₀}(v) > d_{B₀}(v) − I₀(v)`, where
`d_{R₀}(v) ∼ Bin(|R₀| − I₀(v), p)` and `d_{B₀}(v) ∼ Bin(|B₀| + I₀(v) − 1, p)` are independent; Lemma 2.3
with `d = −I₀(v)` gives the bound with `p(n₁ − n₂) − d = p(|R₀| − |B₀|) + p_v`,
`p_v ≥ min{p, 1 − p}`, and `σ √(n − 1)` in the denominators. Where the paper writes
`|R₀| − |B₀| = 2c`, here `|R₀| − |B₀| ≥ 2c` and `Φ₀` is increasing; `√(n − 1) ≤ √n` and
`0.56/√(n − 1) ≤ 0.6/√n` (`n ≥ 8`) finish. -/
theorem dayOneAux_prob_red_ge (hBE : ShevtsovaBerryEsseen) {c : ℕ} (hp0 : 0 < p) (hp1 : p < 1)
    (hc : 1 ≤ c) (hn : 8 ≤ n) {B₀ : Set (Fin n)} (hB₀ : (B₀.ncard : ℝ) ≤ n / 2 - c)
    (v : Fin n) :
    1 / 2 + Φ₀ ((2 * p * c + min p (1 - p)) / Real.sqrt (p * (1 - p) * n)) -
        0.6 * (1 - 2 * p + 2 * p ^ 2) / (Real.sqrt (p * (1 - p)) * Real.sqrt n) ≤
      (edgeLaw n p).real {ω | v ∉ majorityStep (graphOfEdges ω) B₀} := by
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  -- `d_{R₀}(v)` and `d_{B₀}(v)` are sums of the Bernoulli family of the edges at `v`
  set Y : {u : Fin n // u ≠ v} → EdgeVars n → ℝ := fun u => edgeInd s(v, u.1) with hYdef
  have hY : IsBernoulliFamily (edgeLaw n p) p Y := isBernoulliFamily_edgesAt hp0.le hp1.le v
  set S₁ := (Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ B₀ᶜ) with hS₁
  set S₂ := (Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ B₀) with hS₂
  -- `I₀(v)`
  set I : ℝ := if v ∈ B₀ then 0 else 1 with hI
  have hS : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_filter]; intro u _ h1 h2; exact h1 h2
  -- `n₁ = |R₀| − I₀(v)`, `n₂ = |B₀| + I₀(v) − 1`
  have hcard1 : (S₁.card : ℝ) = (n - B₀.ncard) - I := by
    rw [hS₁, dayOneAux_card_filter B₀ᶜ v, dayOneAux_ncard_compl_eq]
    by_cases hv : v ∈ B₀ <;> simp [hI, hv]
  have hcard2 : (S₂.card : ℝ) = B₀.ncard - (1 - I) := by
    rw [hS₂, dayOneAux_card_filter B₀ v]
    by_cases hv : v ∈ B₀ <;> simp [hI, hv]
  have hI01 : I = 0 ∨ I = 1 := by by_cases hv : v ∈ B₀ <;> simp [hI, hv]
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  -- `n₁ > n₂`, since `n₁ − n₂ ≥ 2c − 1 ≥ 1`
  have h21 : S₂.card < S₁.card := by
    have : (S₂.card : ℝ) < S₁.card := by
      rw [hcard1, hcard2]; rcases hI01 with h | h <;> rw [h] <;> linarith
    exact_mod_cast this
  -- Lemma 2.3 with `d = −I₀(v)`
  have hL := lemma2_3 hBE hp0 hp1 hY hS h21 (-I)
  have hset : {ω | ∑ i ∈ S₂, Y i ω + -I < ∑ i ∈ S₁, Y i ω} =
      {ω | v ∉ majorityStep (graphOfEdges ω) B₀} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [dayOneAux_notMem_iff]
  rw [hset] at hL
  refine le_trans ?_ hL
  -- `n₁ + n₂ = n − 1`
  have hN : (S₁.card : ℝ) + S₂.card = n - 1 := by rw [hcard1, hcard2]; ring
  rw [hN]
  have hn1 : (0 : ℝ) < n - 1 := by
    have : (8 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hnpos : (0 : ℝ) < n := by linarith
  set σ := Real.sqrt (p * (1 - p)) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hpq
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hsn1 : 0 < Real.sqrt (n - 1) := Real.sqrt_pos.2 hn1
  have hsn1n : Real.sqrt (n - 1) ≤ Real.sqrt n := Real.sqrt_le_sqrt (by linarith)
  rw [Real.sqrt_mul hpq.le, Real.sqrt_mul hpq.le]
  -- `p(n₁ − n₂) − d = p(|R₀| − |B₀|) + p_v ≥ 2pc + min{p, 1 − p}`
  set A := 2 * p * c + min p (1 - p) with hA
  have hA0 : 0 ≤ A := by
    have : 0 ≤ min p (1 - p) := le_min hp0.le (by linarith)
    positivity
  have hAE : A ≤ p * ((S₁.card : ℝ) - S₂.card) - -I := by
    rw [hcard1, hcard2]
    have h2c : 2 * c ≤ (n : ℝ) - 2 * B₀.ncard := by linarith
    rcases hI01 with h | h <;> rw [h]
    · nlinarith [min_le_left p (1 - p)]
    · nlinarith [min_le_right p (1 - p)]
  have hΦ : Φ₀ (A / (σ * Real.sqrt n)) ≤
      Φ₀ ((p * ((S₁.card : ℝ) - S₂.card) - -I) / (σ * Real.sqrt (n - 1))) := by
    apply strictMono_Φ₀.monotone
    calc A / (σ * Real.sqrt n) ≤ A / (σ * Real.sqrt (n - 1)) :=
          div_le_div_of_nonneg_left hA0 (by positivity) (mul_le_mul_of_nonneg_left hsn1n hσ.le)
      _ ≤ _ := div_le_div_of_nonneg_right hAE (by positivity)
  -- `0.56 / √(n − 1) ≤ 0.6 / √n` for `n ≥ 8`
  have hK : 0 < 1 - 2 * p + 2 * p ^ 2 := by nlinarith [sq_nonneg (2 * p - 1)]
  have hsq : 0.56 * Real.sqrt n ≤ 0.6 * Real.sqrt (n - 1) := by
    have h8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
    have := Real.sqrt_le_sqrt (show (0.56 : ℝ) ^ 2 * n ≤ 0.6 ^ 2 * (n - 1) by nlinarith)
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)] at this
  have herr : 0.56 * (1 - 2 * p + 2 * p ^ 2) / (σ * Real.sqrt (n - 1)) ≤
      0.6 * (1 - 2 * p + 2 * p ^ 2) / (σ * Real.sqrt n) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hsq (mul_nonneg hK.le hσ.le)
    nlinarith
  linarith

/-- **Claim 2.5** (`D:claim:day-1-expection`). Under the hypotheses of Lemma 2.1,
`E|R₁| ≥ n/2 + F₁(n, p, c) √n`, where
`F₁(n, p, c) = √n Φ₀((2pc + min{p, 1 − p}) / (σ √n)) − 0.6 (1 − 2σ²) / σ`.

Reading: the paper also writes `F₁ = F(n, p, c) + 0.8 √n / p`; by the definitions,
`F₁ = F(n, p, c) + 0.8 / p`, which is what its Chebyshev step uses. -/
theorem claim2_5 (hBE : ShevtsovaBerryEsseen) {n c : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hF : 0 < denseF n p c) {B₀ : Set (Fin n)} (hB₀ : (B₀.ncard : ℝ) ≤ n / 2 - c) :
    (n : ℝ) / 2 + (Real.sqrt n * Φ₀ ((2 * p * c + min p (1 - p)) / Real.sqrt (p * (1 - p) * n)) -
        0.6 * (1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p))) * Real.sqrt n ≤
      gnpExp n p (fun G => ((blueAfter G B₀ 1)ᶜ.ncard : ℝ)) := by
  classical
  obtain ⟨hc, hn⟩ := dayOneAux_of_F_pos hp0 hp1 hF
  -- `E|R₁| = ∑_v P(v ∈ R₁)`
  rw [gnpExp_eq]
  have hfun : (fun ω : EdgeVars n => (((blueAfter (graphOfEdges ω) B₀ 1)ᶜ.ncard : ℕ) : ℝ)) =
      fun ω => ∑ v, (if v ∈ majorityStep (graphOfEdges ω) B₀ then (0 : ℝ) else 1) := by
    funext ω
    rw [dayOneAux_ncard_compl]
    rfl
  rw [hfun, integral_finsetSum _ (fun v _ => dayOneAux_integrable (C := 1)
    (fun ω => by split_ifs <;> simp))]
  simp only [dayOneAux_integral_ite]
  -- summing the per-vertex bound over the `n` vertices
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hσ : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.2 (mul_pos hp0 (by linarith))
  calc _ = ∑ _v : Fin n, (1 / 2 + Φ₀ ((2 * p * c + min p (1 - p)) / Real.sqrt (p * (1 - p) * n)) -
        0.6 * (1 - 2 * p + 2 * p ^ 2) / (Real.sqrt (p * (1 - p)) * Real.sqrt n)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hnn : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hnpos.le).symm
        set Φv := Φ₀ ((2 * p * c + min p (1 - p)) / Real.sqrt (p * (1 - p) * n))
        set s := Real.sqrt n
        set σ := Real.sqrt (p * (1 - p))
        rw [hnn]
        field_simp
        ring
    _ ≤ _ := Finset.sum_le_sum (fun v _ => dayOneAux_prob_red_ge hBE hp0 hp1 hc hn hB₀ v)

/-! ### Claim 2.6: conditioning on the edge `v₁v₂` -/

open Classical in
/-- Setting the edge variable of `vw` changes, among the indicators of the edges at `v`, only that
of `vw`. -/
theorem dayOneAux_sum_update {v w : Fin n} (hvw : v ≠ w) (S : Set (Fin n))
    [DecidablePred (· ∈ S)] (ω : EdgeVars n) (b : Prop) :
    ∑ u ∈ (Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ S),
        edgeInd s(v, u.1) (Function.update ω s(v, w) b) =
      (if w ∈ S ∧ b then 1 else 0) +
        ∑ u ∈ ((Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ S)).filter
          (fun u => u.1 ≠ w), edgeInd s(v, u.1) ω := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun u : {u : Fin n // u ≠ v} => u.1 = w)]
  congr 1
  · by_cases hw : w ∈ S
    · have hset : ((Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ S)).filter
          (fun u => u.1 = w) = {⟨w, hvw.symm⟩} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨-, h⟩; exact Subtype.ext h
        · rintro rfl; exact ⟨hw, rfl⟩
      rw [hset, Finset.sum_singleton]
      by_cases hb : b
      · simp [edgeInd, hw, hb]
      · simp [edgeInd, hw, hb]
    · have hset : ((Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ S)).filter
          (fun u => u.1 = w) = ∅ := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
          not_and]
        intro hu h
        exact hw (h ▸ hu)
      rw [hset, Finset.sum_empty]
      simp [hw]
  · apply Finset.sum_congr rfl
    intro u hu
    have hne : s(v, u.1) ≠ s(v, w) := by
      intro h
      rw [Sym2.congr_right] at h
      exact (Finset.mem_filter.1 hu).2 h
    simp only [edgeInd, Function.update_of_ne hne]

open Classical in
/-- The number of neighbours of `v` in `S` once the edge variable of `vw` is set to `b`. -/
theorem dayOneAux_nbrCount_update {v w : Fin n} (hvw : v ≠ w) (S : Set (Fin n))
    [DecidablePred (· ∈ S)] (ω : EdgeVars n) (b : Prop) :
    (nbrCount (graphOfEdges (Function.update ω s(v, w) b)) S v : ℝ) =
      (if w ∈ S ∧ b then 1 else 0) +
        ∑ u ∈ ((Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ S)).filter
          (fun u => u.1 ≠ w), edgeInd s(v, u.1) ω := by
  rw [dayOneAux_nbrCount_eq_sum _ S v, dayOneAux_sum_update hvw S ω b]

open Classical in
/-- With the edge `vw` present, `v` has one more neighbour in `S` if `w ∈ S`. -/
theorem dayOneAux_nbrCount_update_true {v w : Fin n} (hvw : v ≠ w) (S : Set (Fin n))
    [DecidablePred (· ∈ S)] (ω : EdgeVars n) :
    nbrCount (graphOfEdges (Function.update ω s(v, w) True)) S v =
      nbrCount (graphOfEdges (Function.update ω s(v, w) False)) S v +
        (if w ∈ S then 1 else 0) := by
  have h1 := dayOneAux_nbrCount_update hvw S ω True
  have h2 := dayOneAux_nbrCount_update hvw S ω False
  by_cases hw : w ∈ S
  · have : (nbrCount (graphOfEdges (Function.update ω s(v, w) True)) S v : ℝ) =
        nbrCount (graphOfEdges (Function.update ω s(v, w) False)) S v + 1 := by
      rw [h1, h2]; simp [hw]; ring
    rw [ite_eq_left hw]
    exact_mod_cast this
  · have : (nbrCount (graphOfEdges (Function.update ω s(v, w) True)) S v : ℝ) =
        nbrCount (graphOfEdges (Function.update ω s(v, w) False)) S v := by
      rw [h1, h2]; simp [hw]
    rw [ite_eq_right hw, add_zero]
    exact_mod_cast this

open Classical in
/-- **The computation of `a₁ − b₁`** in the proof of Claim 2.6 (`v₁ = v`, `v₂ = w`). With
`X` (resp. `Y`) the number of Red (resp. Blue) neighbours of `v` other than `w`,
`a₁ − b₁ = P(v ∈ R₁ | v ∼ w) − P(v ∈ R₁ | v ≁ w) = J₀(w) P(X − Y = 1 − I₀(v) − I₀(w))`, where
`J₀(w) = 1` if `w` is Red and `−1` if `w` is Blue. -/
theorem dayOneAux_condExp_sub_eq {v w : Fin n} (hvw : v ≠ w) (B : Set (Fin n)) :
    edgeCondExp n p s(v, w) True
          (fun ω => if v ∈ majorityStep (graphOfEdges ω) B then (0 : ℝ) else 1) -
        edgeCondExp n p s(v, w) False
          (fun ω => if v ∈ majorityStep (graphOfEdges ω) B then (0 : ℝ) else 1) =
      (if w ∈ B then -1 else 1) *
        (edgeLaw n p).real {ω |
          ∑ u ∈ ((Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ Bᶜ)).filter
              (fun u => u.1 ≠ w), edgeInd s(v, u.1) ω =
            ∑ u ∈ ((Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ B)).filter
              (fun u => u.1 ≠ w), edgeInd s(v, u.1) ω +
              (((1 - (if v ∈ B then 0 else 1) - (if w ∈ B then 0 else 1) : ℤ)) : ℝ)} := by
  simp only [edgeCondExp]
  rw [dayOneAux_integral_ite, dayOneAux_integral_ite]
  -- `X` and `Y`: the Red and Blue neighbours of `v` other than `w`
  set NB : EdgeVars n → ℕ :=
    fun ω => nbrCount (graphOfEdges (Function.update ω s(v, w) False)) B v with hNB
  set NR : EdgeVars n → ℕ :=
    fun ω => nbrCount (graphOfEdges (Function.update ω s(v, w) False)) Bᶜ v with hNR
  have hR : ∀ ω, (NR ω : ℝ) =
      ∑ u ∈ ((Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ Bᶜ)).filter
        (fun u => u.1 ≠ w), edgeInd s(v, u.1) ω := by
    intro ω
    rw [hNR, dayOneAux_nbrCount_update hvw Bᶜ ω False]
    simp
  have hB : ∀ ω, (NB ω : ℝ) =
      ∑ u ∈ ((Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ B)).filter
        (fun u => u.1 ≠ w), edgeInd s(v, u.1) ω := by
    intro ω
    rw [hNB, dayOneAux_nbrCount_update hvw B ω False]
    simp
  -- `I₀(v)`
  obtain ⟨I, hI⟩ : ∃ I : ℤ, I = if v ∈ B then 0 else 1 := ⟨_, rfl⟩
  rw [← hI]
  -- the events, through `X` and `Y`
  have hsetE : {ω | ∑ u ∈ ((Finset.univ : Finset {u : Fin n // u ≠ v}).filter
        (fun u => u.1 ∈ Bᶜ)).filter (fun u => u.1 ≠ w), edgeInd s(v, u.1) ω =
      ∑ u ∈ ((Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ B)).filter
        (fun u => u.1 ≠ w), edgeInd s(v, u.1) ω +
        (((1 - I - (if w ∈ B then 0 else 1) : ℤ)) : ℝ)} =
      {ω | (NR ω : ℤ) = NB ω + (1 - I - (if w ∈ B then 0 else 1))} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [← hR ω, ← hB ω]
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  have hsetT : {ω | ¬ v ∈ majorityStep (graphOfEdges (Function.update ω s(v, w) True)) B} =
      {ω | (NB ω : ℤ) + (if w ∈ B then 1 else 0) < NR ω + (if w ∈ B then 0 else 1) + I} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [notMem_majorityStep_iff, dayOneAux_nbrCount_update_true hvw B ω,
      dayOneAux_nbrCount_update_true hvw Bᶜ ω, ← hI]
    by_cases hw : w ∈ B
    · simp [hw, hNB, hNR]
    · simp [hw, hNB, hNR]
  have hsetF : {ω | ¬ v ∈ majorityStep (graphOfEdges (Function.update ω s(v, w) False)) B} =
      {ω | (NB ω : ℤ) < NR ω + I} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [notMem_majorityStep_iff, ← hI]
  rw [hsetE, hsetT, hsetF]
  by_cases hw : w ∈ B
  · -- `w` Blue: `a₁ − b₁ = −P(X − Y = 1 − I₀(v))`
    simp only [hw, ite_true]
    have hsub : {ω | (NB ω : ℤ) + 1 < NR ω + 0 + I} ⊆ {ω | (NB ω : ℤ) < NR ω + I} := by
      intro ω h
      simp only [Set.mem_ofPred_eq] at h ⊢
      omega
    have hdiff : {ω | (NB ω : ℤ) < NR ω + I} \ {ω | (NB ω : ℤ) + 1 < NR ω + 0 + I} =
        {ω | (NR ω : ℤ) = NB ω + (1 - I - 0)} := by
      ext ω
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
      omega
    rw [← hdiff, measureReal_sdiff hsub (measurableSet_edgeVars _)]
    ring
  · -- `w` Red: `a₁ − b₁ = P(X − Y = −I₀(v))`
    simp only [hw, ite_false]
    have hsub : {ω | (NB ω : ℤ) < NR ω + I} ⊆ {ω | (NB ω : ℤ) + 0 < NR ω + 1 + I} := by
      intro ω h
      simp only [Set.mem_ofPred_eq] at h ⊢
      omega
    have hdiff : {ω | (NB ω : ℤ) + 0 < NR ω + 1 + I} \ {ω | (NB ω : ℤ) < NR ω + I} =
        {ω | (NR ω : ℤ) = NB ω + (1 - I - 1)} := by
      ext ω
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
      omega
    rw [← hdiff, measureReal_sdiff hsub (measurableSet_edgeVars _)]
    ring

open Classical in
/-- `X` and `Y` in the proof of Claim 2.6 count the `n − 2` vertices other than `v₁, v₂`. -/
theorem dayOneAux_card_pair {v w : Fin n} (hvw : v ≠ w) (B : Set (Fin n)) :
    ((((Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ Bᶜ)).filter
        (fun u => u.1 ≠ w)).card : ℝ) +
      (((Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ B)).filter
        (fun u => u.1 ≠ w)).card = n - 2 := by
  have hn2 : 2 ≤ n := by
    have h1 := v.isLt; have h2 := w.isLt
    have h3 : v.val ≠ w.val := fun h => hvw (Fin.ext h)
    omega
  have hdisj : Disjoint (((Finset.univ : Finset {u : Fin n // u ≠ v}).filter
      (fun u => u.1 ∈ Bᶜ)).filter (fun u => u.1 ≠ w))
      (((Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ B)).filter
        (fun u => u.1 ≠ w)) := by
    rw [Finset.disjoint_left]
    intro u h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_compl_iff] at h1 h2
    exact h1.1 h2.1
  rw [← Nat.cast_add, ← Finset.card_union_of_disjoint hdisj]
  have hunion : (((Finset.univ : Finset {u : Fin n // u ≠ v}).filter
      (fun u => u.1 ∈ Bᶜ)).filter (fun u => u.1 ≠ w)) ∪
      (((Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ B)).filter
        (fun u => u.1 ≠ w)) = (Finset.univ : Finset {u : Fin n // u ≠ v}).erase ⟨w, hvw.symm⟩ := by
    ext u
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_compl_iff, Finset.mem_erase, ne_eq, Subtype.ext_iff, and_true]
    tauto
  rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  push_cast [Nat.cast_sub (by omega : 1 ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
  ring

open Classical in
/-- **The covariance bound** in the proof of Claim 2.6: for `v₁ ≠ v₂`,
`Cov(I₁(v₁), I₁(v₂)) = σ² (a₁ − b₁)(a₂ − b₂)` is at most `0` if `v₁, v₂` have different initial
colours, and at most `σ² (1.12 (1 − 2σ²) / (σ √(n − 2)))² ≤ 1.4 (1 − 2σ²)² / n` (Lemma 2.4,
`n ≥ 20`) if they have the same colour. -/
theorem dayOneAux_cov_le (hBE : ShevtsovaBerryEsseen) (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 20 ≤ n) {v w : Fin n} (hvw : v ≠ w) (B : Set (Fin n)) :
    ∫ ω, (if v ∈ majorityStep (graphOfEdges ω) B then (0 : ℝ) else 1) *
          (if w ∈ majorityStep (graphOfEdges ω) B then (0 : ℝ) else 1) ∂(edgeLaw n p) -
        (∫ ω, (if v ∈ majorityStep (graphOfEdges ω) B then (0 : ℝ) else 1) ∂(edgeLaw n p)) *
          ∫ ω, (if w ∈ majorityStep (graphOfEdges ω) B then (0 : ℝ) else 1) ∂(edgeLaw n p) ≤
      if (v ∈ B ↔ w ∈ B) then 1.4 * (1 - 2 * p + 2 * p ^ 2) ^ 2 / n else 0 := by
  have he : ¬ (s(v, w)).IsDiag := by rw [Sym2.mk_isDiag_iff]; exact hvw
  have hmemv : s(v, w) ∈ edgesAt v := ⟨w, hvw.symm, rfl⟩
  have hmemw : s(v, w) ∈ edgesAt w := ⟨v, hvw, Sym2.eq_swap⟩
  -- `I₁(v₁)` depends on the edges at `v₁`, `I₁(v₂)` on those at `v₂`
  have hfdep : DependsOn
      (fun ω : EdgeVars n => if v ∈ majorityStep (graphOfEdges ω) B then (0 : ℝ) else 1)
      (insert s(v, w) (edgesAt v \ {s(v, w)})) := by
    rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hmemv]
    intro x y hxy
    have h := dependsOn_mem_majorityStep B v hxy
    simp only at h
    simp only [h]
  have hgdep : DependsOn
      (fun ω : EdgeVars n => if w ∈ majorityStep (graphOfEdges ω) B then (0 : ℝ) else 1)
      (insert s(v, w) (edgesAt w \ {s(v, w)})) := by
    rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hmemw]
    intro x y hxy
    have h := dependsOn_mem_majorityStep B w hxy
    simp only at h
    simp only [h]
  -- after revealing `v₁v₂`, the other edges at `v₁` and at `v₂` are disjoint
  have hst : Disjoint (edgesAt v \ {s(v, w)}) (edgesAt w \ {s(v, w)}) := by
    rw [Set.disjoint_left]
    intro e he1 he2
    have h : e ∈ edgesAt v ∩ edgesAt w := ⟨he1.1, he2.1⟩
    rw [edgesAt_inter_edgesAt hvw] at h
    exact he1.2 h
  -- equation (2.3): `Cov = σ² (a₁ − b₁)(a₂ − b₂)`
  rw [covariance_shared_edge hp0.le hp1.le he hfdep hgdep hst (by simp) (by simp) (C := 1)
    (fun ω => by split_ifs <;> simp) (fun ω => by split_ifs <;> simp)]
  rw [dayOneAux_condExp_sub_eq hvw B]
  have h2 := dayOneAux_condExp_sub_eq (p := p) hvw.symm B
  rw [show s(w, v) = s(v, w) from Sym2.eq_swap] at h2
  rw [h2]
  -- Lemma 2.4 bounds both probabilities by `1.12 (1 − 2σ²) / (σ √(n − 2))`
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  have hn' : (20 : ℝ) ≤ n := by exact_mod_cast hn
  set K := 1 - 2 * p + 2 * p ^ 2 with hK
  have hK0 : 0 < K := by nlinarith [sq_nonneg (2 * p - 1)]
  set β := 1.12 * K / Real.sqrt (p * (1 - p) * (n - 2)) with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hq : ∀ {x y : Fin n} (hxy : x ≠ y) (k : ℤ),
      (edgeLaw n p).real {ω |
          ∑ u ∈ ((Finset.univ : Finset {u : Fin n // u ≠ x}).filter (fun u => u.1 ∈ Bᶜ)).filter
              (fun u => u.1 ≠ y), edgeInd s(x, u.1) ω =
            ∑ u ∈ ((Finset.univ : Finset {u : Fin n // u ≠ x}).filter (fun u => u.1 ∈ B)).filter
              (fun u => u.1 ≠ y), edgeInd s(x, u.1) ω + (k : ℝ)} ≤ β := by
    intro x y hxy k
    have hY := isBernoulliFamily_edgesAt (n := n) hp0.le hp1.le x
    have hdisj : Disjoint (((Finset.univ : Finset {u : Fin n // u ≠ x}).filter
        (fun u => u.1 ∈ Bᶜ)).filter (fun u => u.1 ≠ y))
        (((Finset.univ : Finset {u : Fin n // u ≠ x}).filter (fun u => u.1 ∈ B)).filter
          (fun u => u.1 ≠ y)) := by
      rw [Finset.disjoint_left]
      intro u h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_compl_iff] at h1 h2
      exact h1.1 h2.1
    have hcard := dayOneAux_card_pair hxy B
    have hne : 0 < (((Finset.univ : Finset {u : Fin n // u ≠ x}).filter
        (fun u => u.1 ∈ Bᶜ)).filter (fun u => u.1 ≠ y)).card +
        (((Finset.univ : Finset {u : Fin n // u ≠ x}).filter (fun u => u.1 ∈ B)).filter
          (fun u => u.1 ≠ y)).card := by
      have : (0 : ℝ) < (((((Finset.univ : Finset {u : Fin n // u ≠ x}).filter
          (fun u => u.1 ∈ Bᶜ)).filter (fun u => u.1 ≠ y)).card +
          (((Finset.univ : Finset {u : Fin n // u ≠ x}).filter (fun u => u.1 ∈ B)).filter
            (fun u => u.1 ≠ y)).card : ℕ) : ℝ) := by
        push_cast; rw [hcard]; linarith
      exact_mod_cast this
    have h24 := lemma2_4 hBE hp0 hp1 hY hdisj hne k
    rw [hcard] at h24
    exact h24
  set qv := (edgeLaw n p).real {ω |
          ∑ u ∈ ((Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ Bᶜ)).filter
              (fun u => u.1 ≠ w), edgeInd s(v, u.1) ω =
            ∑ u ∈ ((Finset.univ : Finset {u : Fin n // u ≠ v}).filter (fun u => u.1 ∈ B)).filter
              (fun u => u.1 ≠ w), edgeInd s(v, u.1) ω +
              (((1 - (if v ∈ B then 0 else 1) - (if w ∈ B then 0 else 1) : ℤ)) : ℝ)} with hqv
  set qw := (edgeLaw n p).real {ω |
          ∑ u ∈ ((Finset.univ : Finset {u : Fin n // u ≠ w}).filter (fun u => u.1 ∈ Bᶜ)).filter
              (fun u => u.1 ≠ v), edgeInd s(w, u.1) ω =
            ∑ u ∈ ((Finset.univ : Finset {u : Fin n // u ≠ w}).filter (fun u => u.1 ∈ B)).filter
              (fun u => u.1 ≠ v), edgeInd s(w, u.1) ω +
              (((1 - (if w ∈ B then 0 else 1) - (if v ∈ B then 0 else 1) : ℤ)) : ℝ)} with hqw
  have hqv0 : 0 ≤ qv := measureReal_nonneg
  have hqw0 : 0 ≤ qw := measureReal_nonneg
  have hqvβ : qv ≤ β := hq hvw _
  have hqwβ : qw ≤ β := hq hvw.symm _
  -- `σ² β² = 1.2544 (1 − 2σ²)² / (n − 2) ≤ 1.4 (1 − 2σ²)² / n`
  have hσβ : p * (1 - p) * (qv * qw) ≤ 1.4 * K ^ 2 / n := by
    have hqq : qv * qw ≤ β * β := mul_le_mul hqvβ hqwβ hqw0 hβ0
    have hββ : p * (1 - p) * (β * β) = 1.2544 * K ^ 2 / (n - 2) := by
      have hn2 : (0 : ℝ) < n - 2 := by linarith
      rw [hβ, div_mul_div_comm, Real.mul_self_sqrt (by positivity)]
      field_simp
      ring
    have hle : 1.2544 * K ^ 2 / (n - 2) ≤ 1.4 * K ^ 2 / n := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [sq_nonneg K]
    calc p * (1 - p) * (qv * qw) ≤ p * (1 - p) * (β * β) :=
          mul_le_mul_of_nonneg_left hqq hpq.le
      _ = 1.2544 * K ^ 2 / (n - 2) := hββ
      _ ≤ 1.4 * K ^ 2 / n := hle
  have hneg : 0 ≤ p * (1 - p) * (qv * qw) := by positivity
  by_cases hvB : v ∈ B <;> by_cases hwB : w ∈ B <;> simp only [hvB, hwB, ite_true, ite_false,
    iff_true, iff_false, not_true_eq_false] <;> nlinarith

open Classical in
/-- The number of ordered pairs of distinct vertices of the same initial colour is
`|B₀|(|B₀| − 1) + |R₀|(|R₀| − 1)`. -/
theorem dayOneAux_sum_same_colour (B : Set (Fin n)) (γ : ℝ) :
    ∑ v, (1 / 4 + ∑ w ∈ Finset.univ.erase v, if (v ∈ B ↔ w ∈ B) then γ else 0) =
      n / 4 + γ * ((B.ncard : ℝ) * (B.ncard - 1) + (n - B.ncard) * (n - B.ncard - 1)) := by
  have hb := dayOneAux_ncard_eq_card_filter B
  have hbr : (Finset.univ.filter (fun u : Fin n => u ∈ B)).card +
      (Finset.univ.filter (fun u : Fin n => ¬ u ∈ B)).card = n := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hr : (n : ℝ) - B.ncard = (Finset.univ.filter (fun u : Fin n => ¬ u ∈ B)).card := by
    have h' : ((Finset.univ.filter (fun u : Fin n => u ∈ B)).card : ℝ) +
        (Finset.univ.filter (fun u : Fin n => ¬ u ∈ B)).card = n := by exact_mod_cast hbr
    rw [hb]; linarith
  have hv : ∀ v, ∑ w ∈ Finset.univ.erase v, (if (v ∈ B ↔ w ∈ B) then γ else 0) =
      if v ∈ B then γ * ((B.ncard : ℝ) - 1) else γ * ((n : ℝ) - B.ncard - 1) := by
    intro v
    by_cases hvB : v ∈ B
    · simp only [hvB, true_iff, ite_true]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        Finset.filter_erase, Finset.card_erase_of_mem (by simpa using hvB), hb]
      have : 0 < (Finset.univ.filter (fun u : Fin n => u ∈ B)).card :=
        Finset.card_pos.2 ⟨v, by simpa using hvB⟩
      push_cast [Nat.cast_sub this]
      ring
    · simp only [hvB, false_iff, ite_false]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        Finset.filter_erase, Finset.card_erase_of_mem (by simpa using hvB), hr]
      have : 0 < (Finset.univ.filter (fun u : Fin n => ¬ u ∈ B)).card :=
        Finset.card_pos.2 ⟨v, by simpa using hvB⟩
      push_cast [Nat.cast_sub this]
      ring
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  simp only [hv]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, ← hb]
  rw [show ((Finset.univ.filter (fun u : Fin n => ¬ u ∈ B)).card : ℝ) = n - B.ncard from hr.symm]
  ring

/-- **Counting the pairs of the same colour** (the paper's
`C(|R₀|, 2) + C(|B₀|, 2) = n²/4 + c² − n/2` for `|B₀| = n/2 − c`): for `|B₀| = ⌊n/2 − c⌋`,
`|B₀|(|B₀| − 1) + |R₀|(|R₀| − 1) ≤ 2(n²/4 + c²)`. -/
theorem dayOneAux_pair_count {c b : ℕ} (hb : b = ⌊(n : ℝ) / 2 - c⌋₊) :
    (b : ℝ) * (b - 1) + (n - b) * (n - b - 1) ≤ n ^ 2 / 2 + 2 * c ^ 2 := by
  have h1 : 2 * b ≤ n := by
    rcases le_or_gt 0 ((n : ℝ) / 2 - c) with h | h
    · have h' := Nat.floor_le h
      rw [← hb] at h'
      have : ((2 * b : ℕ) : ℝ) ≤ n := by push_cast; linarith
      exact_mod_cast this
    · rw [hb, Nat.floor_eq_zero.2 (by linarith)]
      omega
  have h2 : n ≤ 2 * b + 2 * c + 1 := by
    have h' := Nat.lt_floor_add_one ((n : ℝ) / 2 - c)
    rw [← hb] at h'
    have : ((n : ℕ) : ℝ) < ((2 * b + 2 * c + 2 : ℕ) : ℝ) := by push_cast; linarith
    have : n < 2 * b + 2 * c + 2 := by exact_mod_cast this
    omega
  have h1' : (2 * b : ℝ) ≤ n := by exact_mod_cast h1
  have h2' : (n : ℝ) ≤ 2 * b + 2 * c + 1 := by exact_mod_cast h2
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  -- `δ = |R₀| − |B₀| = n − 2|B₀|` satisfies `δ² ≤ 4c² + 2n`
  have key : ((n : ℝ) - 2 * b) ^ 2 ≤ 4 * c ^ 2 + 2 * n := by
    rcases le_or_gt ((n : ℝ) - 2 * b) (2 * c) with h | h
    · nlinarith
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * c + 1 - (n - 2 * b))
        (by linarith : (0 : ℝ) ≤ (n - 2 * b) + 2 * c)]
  nlinarith

-- The hypothesis `hc : 0 < c` of the statement is not needed by the proof.
set_option linter.unusedVariables false in
/-- **Claim 2.6** (`D:claim:day-1-covariance`).
`Var|R₁| ≤ 0.25 n + 0.7 (1 − 2σ²)² (n + 4c² / n)`.

Deviation (hypotheses the paper's computation uses, as for the sparse paper's Lemma 2.1): the
paper counts the pairs of vertices of the same initial colour as if `|R₀| = n/2 + c` and
`|B₀| = n/2 − c`, and bounds `1.2544/(n − 2) ≤ 1.4/n`, which needs `n ≥ 20`. The statement assumes
`|B₀| = ⌊n/2 − c⌋` (which also covers odd `n`) and `n ≥ 20`. Lemma 2.1, for every
`|B₀| ≤ n/2 − c`, reduces to this case by the monotonicity of majority dynamics. -/
theorem claim2_6 (hBE : ShevtsovaBerryEsseen) {n c : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 20 ≤ n) (hc : 0 < c) {B₀ : Set (Fin n)} (hB₀ : B₀.ncard = ⌊(n : ℝ) / 2 - c⌋₊) :
    gnpVar n p (fun G => ((blueAfter G B₀ 1)ᶜ.ncard : ℝ)) ≤
      0.25 * n + 0.7 * (1 - 2 * p + 2 * p ^ 2) ^ 2 * (n + 4 * (c : ℝ) ^ 2 / n) := by
  classical
  rw [gnpVar_eq]
  -- `|R₁| = ∑_v I₁(v)`
  set I : Fin n → EdgeVars n → ℝ :=
    fun v ω => if v ∈ majorityStep (graphOfEdges ω) B₀ then 0 else 1 with hIdef
  have hfun : (fun ω : EdgeVars n => (((blueAfter (graphOfEdges ω) B₀ 1)ᶜ.ncard : ℕ) : ℝ)) =
      fun ω => ∑ v, I v ω := by
    funext ω
    rw [dayOneAux_ncard_compl]
    rfl
  have hIb : ∀ v ω, |I v ω| ≤ 1 := fun v ω => by
    simp only [hIdef]; split_ifs <;> simp
  -- `Var|R₁| = ∑_{v, w} Cov(I₁(v), I₁(w))`
  rw [hfun, variance_fun_sum (fun v => dayOneAux_memLp (hIb v) 2)]
  have hcov : ∀ v w, cov[I v, I w; edgeLaw n p] = ∫ ω, I v ω * I w ω ∂(edgeLaw n p) -
      (∫ ω, I v ω ∂(edgeLaw n p)) * ∫ ω, I w ω ∂(edgeLaw n p) := by
    intro v w
    rw [covariance_eq_sub (dayOneAux_memLp (hIb v) 2) (dayOneAux_memLp (hIb w) 2)]
    rfl
  -- equation (2.2): `Var I₁(v) = E I₁(v) (1 − E I₁(v)) ≤ 1/4`
  have hdiag : ∀ v, cov[I v, I v; edgeLaw n p] ≤ 1 / 4 := by
    intro v
    rw [hcov]
    have hsq : ∀ ω, I v ω * I v ω = I v ω := fun ω => by
      simp only [hIdef]; split_ifs <;> simp
    simp only [hsq]
    nlinarith [sq_nonneg (∫ ω, I v ω ∂(edgeLaw n p) - 1 / 2)]
  set K := 1 - 2 * p + 2 * p ^ 2 with hK
  -- the covariances of distinct vertices
  have hoff : ∀ v w, v ≠ w → cov[I v, I w; edgeLaw n p] ≤
      if (v ∈ B₀ ↔ w ∈ B₀) then 1.4 * K ^ 2 / n else 0 := by
    intro v w hvw
    rw [hcov]
    exact dayOneAux_cov_le hBE hp0 hp1 hn hvw B₀
  have hn' : (20 : ℝ) ≤ n := by exact_mod_cast hn
  have hγ : 0 ≤ 1.4 * K ^ 2 / n := by positivity
  have hpair := dayOneAux_pair_count (n := n) (c := c) hB₀
  calc ∑ v, ∑ w, cov[I v, I w; edgeLaw n p]
      = ∑ v, (cov[I v, I v; edgeLaw n p] +
          ∑ w ∈ Finset.univ.erase v, cov[I v, I w; edgeLaw n p]) := by
        apply Finset.sum_congr rfl
        intro v _
        exact (Finset.add_sum_erase _ (fun w => cov[I v, I w; edgeLaw n p])
          (Finset.mem_univ v)).symm
    _ ≤ ∑ v, (1 / 4 + ∑ w ∈ Finset.univ.erase v,
          if (v ∈ B₀ ↔ w ∈ B₀) then 1.4 * K ^ 2 / n else 0) := by
        apply Finset.sum_le_sum
        intro v _
        apply add_le_add (hdiag v)
        apply Finset.sum_le_sum
        intro w hw
        exact hoff v w (Finset.ne_of_mem_erase hw).symm
    _ = n / 4 + 1.4 * K ^ 2 / n * ((B₀.ncard : ℝ) * (B₀.ncard - 1) +
          (n - B₀.ncard) * (n - B₀.ncard - 1)) := dayOneAux_sum_same_colour B₀ _
    _ ≤ n / 4 + 1.4 * K ^ 2 / n * (n ^ 2 / 2 + 2 * c ^ 2) := by gcongr
    _ = 0.25 * n + 0.7 * K ^ 2 * (n + 4 * (c : ℝ) ^ 2 / n) := by
        have hn0 : (n : ℝ) ≠ 0 := by positivity
        field_simp
        ring

/-! ### Lemma 2.1 -/

/-- `P₁(n, p, c) < 1` together with `F(n, p, c) > 0` forces `n ≥ 20`: then `F² > 0.425`, so
`F > 0.65`, while `F ≤ √n/2 − 1.6` since `Φ₀ < 1/2` and
`0.6 (1 − 2σ²)/σ + 0.8/p ≥ 1.6` for `p ∈ (0, 1)`. -/
theorem dayOneAux_twenty_le (hp0 : 0 < p) (hp1 : p < 1) {c : ℕ} (hF : 0 < denseF n p c)
    (hP1 : denseP1 n p c < 1) : 20 ≤ n := by
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  have hσ : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.2 hpq
  have hσsq : Real.sqrt (p * (1 - p)) ^ 2 = p * (1 - p) := Real.sq_sqrt hpq.le
  -- `0.6 (1 − 2σ²)/σ + 0.8/p ≥ 1.6`
  have hg : 1.6 ≤ 0.6 * (1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p)) + 0.8 / p := by
    have hsplit : 0.6 * (1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p)) =
        0.6 * ((1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p))) := by ring
    rw [hsplit]
    rcases le_or_gt p 0.8 with hp8 | hp8
    · have h1 : 1 ≤ (1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p)) := by
        rw [le_div_iff₀ hσ]; linarith [dayOneAux_sqrt_le hp0.le hp1.le]
      have h2 : 1 ≤ 0.8 / p := by rw [le_div_iff₀ hp0]; linarith
      linarith
    · have hσ4 : Real.sqrt (p * (1 - p)) ≤ 0.4 := by
        rw [Real.sqrt_le_left (by norm_num)]; nlinarith
      have h1 : 1.7 ≤ (1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p)) := by
        rw [le_div_iff₀ hσ]
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 0.4 - Real.sqrt (p * (1 - p)))
          (by linarith : (0 : ℝ) ≤ 2 * Real.sqrt (p * (1 - p)) + 2.5)]
      have h2 : 0.8 ≤ 0.8 / p := by rw [le_div_iff₀ hp0]; nlinarith
      linarith
  -- `F² > 0.425`, hence `F > 0.65`
  have hF2 : 0.425 < denseF n p c ^ 2 := by
    unfold denseP1 at hP1
    rw [div_lt_one (by positivity)] at hP1
    have hK2 : 1 / 4 ≤ (1 - 2 * p + 2 * p ^ 2) ^ 2 := by
      have : 1 / 2 ≤ 1 - 2 * p + 2 * p ^ 2 := by nlinarith [sq_nonneg (2 * p - 1)]
      nlinarith
    have h4 : 0 ≤ 4 * (c : ℝ) ^ 2 / (n : ℝ) ^ 2 := by positivity
    nlinarith
  have hF65 : 0.65 < denseF n p c := by nlinarith
  -- `F ≤ √n/2 − 1.6`
  have hFle : denseF n p c ≤ Real.sqrt n / 2 - 1.6 := by
    unfold denseF
    have hΦ := Φ₀_lt_half ((2 * p * c + min p (1 - p)) / Real.sqrt (p * (1 - p) * n))
    have : Real.sqrt n * Φ₀ ((2 * p * c + min p (1 - p)) / Real.sqrt (p * (1 - p) * n)) ≤
        Real.sqrt n * (1 / 2) := mul_le_mul_of_nonneg_left hΦ.le (Real.sqrt_nonneg _)
    linarith
  by_contra hn
  have hn19 : (n : ℝ) ≤ 19 := by exact_mod_cast (by omega : n ≤ 19)
  have : Real.sqrt n < 4.5 := by rw [Real.sqrt_lt' (by norm_num)]; linarith
  linarith

/-- **Lemma 2.1** (`D:lem:const-advantage-day-1`). Let `p ∈ (0, 1)` and `n, c ∈ ℕ` with
`F(n, p, c) > 0`. If `|B₀| ≤ n/2 − c`, then `P(|B₁| > n/2 − 0.8 √n / p) ≤ P₁(n, p, c)`.

Departure from the paper (minimal repair of a gap): the paper applies Chebyshev's inequality
with Claim 2.6, whose pair count assumes `|B₀| = n/2 − c` and whose bound
`1.2544/(n − 2) ≤ 1.4/n` needs `n ≥ 20`. The proof first disposes of the trivial case
`P₁ ≥ 1`; otherwise `P₁ < 1` and `F > 0` give `n ≥ 20` (`dayOneAux_twenty_le`) and `c ≥ 1`. It
then enlarges `B₀` to a set `B₀' ⊇ B₀` with `|B₀'| = ⌊n/2 − c⌋` (possible since `|B₀| ≤ n/2 − c`
is an integer); by the monotonicity of majority dynamics (`blueAfter_mono`), `|B₁|` can only grow,
so it suffices to bound the probability for `B₀'`, where Claims 2.5 and 2.6 apply. The Chebyshev
step for `B₀'` is the paper's. -/
theorem lemma2_1 (hBE : ShevtsovaBerryEsseen) {n c : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hF : 0 < denseF n p c) {B₀ : Set (Fin n)} (hB₀ : (B₀.ncard : ℝ) ≤ n / 2 - c) :
    gnpProb n p (fun G => (n : ℝ) / 2 - 0.8 * Real.sqrt n / p < (blueAfter G B₀ 1).ncard) ≤
      denseP1 n p c := by
  classical
  -- the trivial case `P₁ ≥ 1`
  by_cases hP1 : 1 ≤ denseP1 n p c
  · exact (gnpProb_le_one _).trans hP1
  rw [not_le] at hP1
  obtain ⟨hc, -⟩ := dayOneAux_of_F_pos hp0 hp1 hF
  have hn : 20 ≤ n := dayOneAux_twenty_le hp0 hp1 hF hP1
  have hn' : (20 : ℝ) ≤ n := by exact_mod_cast hn
  -- enlarge `B₀` to `B₀'` with `|B₀'| = ⌊n/2 − c⌋`
  have hfl : B₀.ncard ≤ ⌊(n : ℝ) / 2 - c⌋₊ := Nat.le_floor hB₀
  have hfln : ⌊(n : ℝ) / 2 - c⌋₊ ≤ (Set.univ : Set (Fin n)).ncard := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    apply Nat.floor_le_of_le
    have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    linarith
  obtain ⟨B₀', hsub, -, hcard⟩ := Set.exists_subsuperset_card_eq (Set.subset_univ B₀) hfl hfln
  have hB₀' : (B₀'.ncard : ℝ) ≤ n / 2 - c := by
    rw [hcard]
    exact Nat.floor_le (le_trans (Nat.cast_nonneg _) hB₀)
  -- by monotonicity, `|B₁|` can only grow
  have hmono : gnpProb n p
      (fun G => (n : ℝ) / 2 - 0.8 * Real.sqrt n / p < (blueAfter G B₀ 1).ncard) ≤
      gnpProb n p (fun G => (n : ℝ) / 2 - 0.8 * Real.sqrt n / p < (blueAfter G B₀' 1).ncard) := by
    apply gnpProb_mono
    intro G hG
    have h := Set.ncard_le_ncard (blueAfter_mono G hsub 1)
    have h' : ((blueAfter G B₀ 1).ncard : ℝ) ≤ (blueAfter G B₀' 1).ncard := by exact_mod_cast h
    linarith
  refine hmono.trans ?_
  -- Chebyshev's inequality for `|R₁| = n − |B₁|` (for `B₀'`)
  set μG := SimpleGraph.binomialRandom (Fin n) (toUnit p) with hμG
  set X : SimpleGraph (Fin n) → ℝ := fun G => ((blueAfter G B₀' 1)ᶜ.ncard : ℝ) with hX
  have hXc : ∀ G, (X G : ℝ) = n - (blueAfter G B₀' 1).ncard := by
    intro G
    have h := Set.ncard_add_ncard_compl (blueAfter G B₀' 1)
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
    have h' : (((blueAfter G B₀' 1).ncard + (blueAfter G B₀' 1)ᶜ.ncard : ℕ) : ℝ) = n := by
      exact_mod_cast h
    push_cast at h'
    simp only [hX]
    linarith
  have hXm : Measurable X := fun s _ => measurableSet_simpleGraph _
  have hXmem : MemLp X 2 μG := by
    refine MemLp.of_bound hXm.aestronglyMeasurable n (Filter.Eventually.of_forall fun G => ?_)
    have h := Set.ncard_le_card (blueAfter G B₀' 1)ᶜ
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
    have h' : (((blueAfter G B₀' 1)ᶜ.ncard : ℕ) : ℝ) ≤ n := by exact_mod_cast h
    simp only [hX, Real.norm_eq_abs, Nat.abs_cast]
    exact h'
  set t : ℝ := (n : ℝ) / 2 + 0.8 * Real.sqrt n / p with ht
  -- Claim 2.5: `E|R₁| − n/2 − 0.8 √n / p ≥ F √n > 0`
  have hE := claim2_5 hBE hp0 hp1 hF hB₀'
  have hEX : gnpExp n p (fun G => ((blueAfter G B₀' 1)ᶜ.ncard : ℝ)) = μG[X] := rfl
  rw [hEX] at hE
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hF1 : Real.sqrt n * Φ₀ ((2 * p * c + min p (1 - p)) / Real.sqrt (p * (1 - p) * n)) -
      0.6 * (1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p)) = denseF n p c + 0.8 / p := by
    unfold denseF; ring
  rw [hF1] at hE
  have hgap : denseF n p c * Real.sqrt n ≤ μG[X] - t := by
    rw [ht]
    have : 0.8 * Real.sqrt n / p = 0.8 / p * Real.sqrt n := by ring
    rw [this]
    nlinarith
  have hgap0 : 0 < denseF n p c * Real.sqrt n := mul_pos hF hsn
  have htE : t < μG[X] := by linarith
  -- Claim 2.6
  have hV := claim2_6 hBE hp0 hp1 hn (by omega) hcard
  have hVX : gnpVar n p (fun G => ((blueAfter G B₀' 1)ᶜ.ncard : ℝ)) = variance X μG := rfl
  rw [hVX] at hV
  -- the event `|B₁| > n/2 − 0.8 √n / p` is `|R₁| < n/2 + 0.8 √n / p`
  have hevent : gnpProb n p
      (fun G => (n : ℝ) / 2 - 0.8 * Real.sqrt n / p < (blueAfter G B₀' 1).ncard) ≤
      μG.real {G | X G ≤ t} := by
    apply gnpProb_mono
    intro G hG
    show X G ≤ t
    rw [hXc G, ht]
    linarith
  have hcheb := measureReal_le_le_variance_div_sq hXmem htE
  refine hevent.trans (hcheb.trans ?_)
  -- `Var / (E − t)² ≤ Var / (F² n) ≤ P₁`
  have hVnn : 0 ≤ variance X μG := variance_nonneg X μG
  have hsq : (denseF n p c * Real.sqrt n) ^ 2 ≤ (μG[X] - t) ^ 2 :=
    pow_le_pow_left₀ hgap0.le hgap 2
  have hnn : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (by linarith)).symm
  calc variance X μG / (μG[X] - t) ^ 2
      ≤ variance X μG / (denseF n p c * Real.sqrt n) ^ 2 :=
        div_le_div_of_nonneg_left hVnn (by positivity) hsq
    _ ≤ (0.25 * n + 0.7 * (1 - 2 * p + 2 * p ^ 2) ^ 2 * (n + 4 * (c : ℝ) ^ 2 / n)) /
          (denseF n p c * Real.sqrt n) ^ 2 := by gcongr
    _ = denseP1 n p c := by
        unfold denseP1
        have hn0 : (n : ℝ) ≠ 0 := by positivity
        have hF0 : denseF n p c ≠ 0 := hF.ne'
        rw [mul_pow, ← hnn]
        field_simp

end PowerOfFew.Dense

end
