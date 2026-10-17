module

public import Basic.Probability.BernoulliFamily

/-!
# Chernoff bounds for sums of independent Bernoulli variables

The Chernoff bounds that the sparse paper uses without proof, for `Z = ∑ i ∈ s, X i` with `X` a
family of independent Bernoulli(`p`) variables and `m = #s` (so `Z ∼ Bin(m, p)`):

* `IsBernoulliFamily.measureReal_sum_le_le_exp_klBern`: the lower tail
  `P(Z ≤ a m) ≤ exp(−m D(a ‖ p))` for `0 ≤ a ≤ p`, with the relative entropy
  `D(a ‖ p) = a log(a / p) + (1 − a) log((1 − a) / (1 − p))` (sparse paper, proof of Lemma A.4);
* `IsBernoulliFamily.measureReal_sum_ge_le_exp`, `IsBernoulliFamily.measureReal_sum_le_le_exp`:
  `P(Z ≥ T) ≤ exp(−(T − pm)² / (2T))` for `T > pm` and `P(Z ≤ T) ≤ exp(−(pm − T)² / (2pm))` for
  `T < pm` (sparse paper, proof of Lemma A.6, its equations (29) and (30));
* `IsBernoulliFamily.measureReal_sum_ge_le_exp_mul_log`: the upper tail
  `P(Z ≥ k) ≤ (e p m / k)^k` for `k > 0`, used by Feige and Ofek's argument
  (`External.FeigeOfek`) for the degrees and the discrepancy of `G(n, p)`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- The relative entropy `D(a ‖ p) = a log(a / p) + (1 − a) log((1 − a) / (1 − p))` of two
Bernoulli laws (with `0 log 0 = 0`). -/
noncomputable def klBern (a p : ℝ) : ℝ :=
  a * Real.log (a / p) + (1 - a) * Real.log ((1 - a) / (1 - p))

/-! ### Two classical lower bounds for the relative entropy -/

/-- `x + x² / 2 ≤ −log(1 − x)` for `0 ≤ x < 1`: the first two terms of the series
`−log(1 − x) = ∑ xᵏ / k`, whose terms are all nonnegative. -/
private lemma add_sq_div_two_le_neg_log {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x + x ^ 2 / 2 ≤ -Real.log (1 - x) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by rwa [abs_of_nonneg hx0])
  have h2 := sum_le_hasSum (Finset.range 2) (fun i _ => by positivity) h
  norm_num [Finset.sum_range_succ] at h2
  linarith

/-- `(1 − a) log((1 − a) / (1 − p)) ≥ p − a` for `a ≤ 1` and `p < 1` (from `log x ≥ 1 − 1/x`). -/
private lemma sub_le_mul_log_one_sub {a p : ℝ} (ha1 : a ≤ 1) (hp1 : p < 1) :
    p - a ≤ (1 - a) * Real.log ((1 - a) / (1 - p)) := by
  rcases ha1.eq_or_lt with rfl | ha1
  · simp only [sub_self, zero_mul]
    linarith
  · have h1a : 0 < 1 - a := by linarith
    have h1p : 0 < 1 - p := by linarith
    have h := Real.one_sub_inv_le_log_of_pos (div_pos h1a h1p)
    rw [inv_div] at h
    calc p - a = (1 - a) * (1 - (1 - p) / (1 - a)) := by field_simp; ring
      _ ≤ (1 - a) * Real.log ((1 - a) / (1 - p)) := by gcongr

/-- `D(a ‖ p) ≥ (a − p)² / (2a)` for `p ≤ a ≤ 1`. -/
private lemma sq_div_le_klBern_of_le {a p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hpa : p ≤ a)
    (ha1 : a ≤ 1) : (a - p) ^ 2 / (2 * a) ≤ klBern a p := by
  have ha0 : 0 < a := lt_of_lt_of_le hp0 hpa
  have h1 := sub_le_mul_log_one_sub ha1 hp1
  -- `log(a / p) = −log(1 − x) ≥ x + x² / 2` with `x = 1 − p / a ∈ [0, 1)`.
  have hx0 : 0 ≤ 1 - p / a := by rw [sub_nonneg, div_le_one ha0]; exact hpa
  have hx1 : 1 - p / a < 1 := by have : 0 < p / a := div_pos hp0 ha0; linarith
  have h2 := add_sq_div_two_le_neg_log hx0 hx1
  rw [sub_sub_cancel, ← Real.log_inv, inv_div] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 ha0.le
  have h4 : a * ((1 - p / a) + (1 - p / a) ^ 2 / 2) = (a - p) + (a - p) ^ 2 / (2 * a) := by
    field_simp
  unfold klBern
  linarith

/-- `D(a ‖ p) ≥ (p − a)² / (2p)` for `0 ≤ a ≤ p`. -/
private lemma sq_div_le_klBern_of_ge {a p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha0 : 0 ≤ a)
    (hap : a ≤ p) : (p - a) ^ 2 / (2 * p) ≤ klBern a p := by
  have h1 := sub_le_mul_log_one_sub (hap.trans hp1.le) hp1
  -- `a log(a / p) ≥ (a² / p − p) / 2`, from `sinh s ≤ s` for `s = log(a / p) ≤ 0`.
  have h2 : (a ^ 2 / p - p) / 2 ≤ a * Real.log (a / p) := by
    rcases ha0.eq_or_lt with rfl | ha0
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_sub,
        zero_mul]
      linarith
    · have hu : 0 < a / p := div_pos ha0 hp0
      have hs := Real.sinh_le_self_iff.mpr
        (Real.log_nonpos hu.le (by rw [div_le_one hp0]; exact hap))
      rw [Real.sinh_eq, Real.exp_log hu, Real.exp_neg, Real.exp_log hu, inv_div] at hs
      calc (a ^ 2 / p - p) / 2 = a * ((a / p - p / a) / 2) := by field_simp
        _ ≤ a * Real.log (a / p) := mul_le_mul_of_nonneg_left hs ha0.le
  have h3 : (p - a) ^ 2 / (2 * p) = (a ^ 2 / p - p) / 2 + (p - a) := by
    field_simp
    ring
  unfold klBern
  linarith

/-- The Chernoff bound at the optimal `t = log(a(1 − p) / (p(1 − a)))` equals `exp(−m D(a ‖ p))`. -/
private lemma exp_mul_pow_eq_exp_klBern {a p : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hp0 : 0 < p)
    (hp1 : p < 1) (m : ℕ) :
    Real.exp (-Real.log (a * (1 - p) / (p * (1 - a))) * (a * m)) *
        (1 - p + p * Real.exp (Real.log (a * (1 - p) / (p * (1 - a))))) ^ m =
      Real.exp (-(m * klBern a p)) := by
  have h1a : 1 - a ≠ 0 := by linarith
  have h1p : 1 - p ≠ 0 := by linarith
  have hlog : Real.log (a * (1 - p) / (p * (1 - a))) =
      Real.log (a / p) - Real.log ((1 - a) / (1 - p)) := by
    rw [← Real.log_div (div_ne_zero ha0.ne' hp0.ne') (div_ne_zero h1a h1p)]
    congr 1
    field_simp
  -- `1 − p + p eᵗ = (1 − p) / (1 − a)`.
  have hexp : 1 - p + p * Real.exp (Real.log (a * (1 - p) / (p * (1 - a)))) =
      Real.exp (-Real.log ((1 - a) / (1 - p))) := by
    have hpos : 0 < a * (1 - p) / (p * (1 - a)) :=
      div_pos (mul_pos ha0 (by linarith)) (mul_pos hp0 (by linarith))
    rw [Real.exp_log hpos, Real.exp_neg, Real.exp_log (div_pos (by linarith) (by linarith)),
      inv_div]
    field_simp
    ring
  rw [hexp, ← Real.exp_nat_mul, ← Real.exp_add, hlog]
  congr 1
  unfold klBern
  ring

namespace IsBernoulliFamily

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ℝ}
  {X : ι → Ω → ℝ}

/-! ### The moment generating function and the Chernoff bounds -/

omit [IsProbabilityMeasure μ] in
/-- The sum of a Bernoulli family over `s` lies in `[0, #s]`. -/
private lemma sum_mem_Icc (hX : IsBernoulliFamily μ p X) (s : Finset ι) (ω : Ω) :
    ∑ i ∈ s, X i ω ∈ Set.Icc 0 (s.card : ℝ) := by
  constructor
  · exact Finset.sum_nonneg fun i _ => by rcases hX.zero_or_one i ω with h | h <;> simp [h]
  · calc ∑ i ∈ s, X i ω ≤ ∑ i ∈ s, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => by rcases hX.zero_or_one i ω with h | h <;> simp [h]
      _ = s.card := by simp

/-- `E e^{t X i} = 1 − p + p eᵗ`. -/
private lemma mgf_eq (hX : IsBernoulliFamily μ p X) (i : ι) (t : ℝ) :
    mgf (X i) μ t = 1 - p + p * Real.exp t := by
  have hint : Integrable (X i) μ := Integrable.of_mem_Icc 0 1 (hX.measurable i).aemeasurable
    (ae_of_all _ fun ω => by rcases hX.zero_or_one i ω with h | h <;> simp [h])
  -- `e^{t X i} = 1 + (eᵗ − 1) X i` since `X i ∈ {0, 1}`.
  have hfun : (fun ω => Real.exp (t * X i ω)) = fun ω => 1 + (Real.exp t - 1) * X i ω := by
    ext ω
    rcases hX.zero_or_one i ω with h | h <;> simp [h]
  rw [mgf, hfun, integral_add (integrable_const _) (hint.const_mul _), integral_const,
    integral_const_mul, hX.integral_eq, probReal_univ]
  simp only [smul_eq_mul, one_mul]
  ring

/-- `E e^{t ∑ X i} = (1 − p + p eᵗ)^#s`, by independence. -/
private lemma mgf_sum_eq (hX : IsBernoulliFamily μ p X) (s : Finset ι) (t : ℝ) :
    mgf (fun ω => ∑ i ∈ s, X i ω) μ t = (1 - p + p * Real.exp t) ^ s.card := by
  have hfun : (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i := by
    ext ω
    simp
  rw [hfun, hX.indep.mgf_sum hX.measurable s, Finset.prod_congr rfl fun i _ => hX.mgf_eq i t,
    Finset.prod_const]

private lemma integrable_exp_mul_sum (hX : IsBernoulliFamily μ p X) (s : Finset ι) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * ∑ i ∈ s, X i ω)) μ :=
  integrable_exp_mul_of_mem_Icc
    (Finset.measurable_sum s fun i _ => hX.measurable i).aemeasurable
    (ae_of_all _ fun ω => hX.sum_mem_Icc s ω)

/-- Chernoff's bound for the upper tail: `P(∑ X i ≥ c) ≤ e^{−tc} (1 − p + p eᵗ)^#s`, `t ≥ 0`. -/
private lemma measureReal_sum_ge_le_exp_mul (hX : IsBernoulliFamily μ p X) (s : Finset ι)
    {t : ℝ} (ht : 0 ≤ t) (c : ℝ) :
    μ.real {ω | c ≤ ∑ i ∈ s, X i ω} ≤ Real.exp (-t * c) * (1 - p + p * Real.exp t) ^ s.card := by
  have h := measure_ge_le_exp_mul_mgf (X := fun ω => ∑ i ∈ s, X i ω) (μ := μ) c ht
    (hX.integrable_exp_mul_sum s t)
  rwa [hX.mgf_sum_eq s t] at h

/-- Chernoff's bound for the lower tail: `P(∑ X i ≤ c) ≤ e^{−tc} (1 − p + p eᵗ)^#s`, `t ≤ 0`. -/
private lemma measureReal_sum_le_le_exp_mul (hX : IsBernoulliFamily μ p X) (s : Finset ι)
    {t : ℝ} (ht : t ≤ 0) (c : ℝ) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ c} ≤ Real.exp (-t * c) * (1 - p + p * Real.exp t) ^ s.card := by
  have h := measure_le_le_exp_mul_mgf (X := fun ω => ∑ i ∈ s, X i ω) (μ := μ) c ht
    (hX.integrable_exp_mul_sum s t)
  rwa [hX.mgf_sum_eq s t] at h

/-- A number that is at most `e^{−tr}` for every `t ≥ 0`, where `r > 0`, is at most `0`. -/
private lemma le_zero_of_forall_le_exp {P r : ℝ} (hr : 0 < r)
    (h : ∀ t : ℝ, 0 ≤ t → P ≤ Real.exp (-(t * r))) : P ≤ 0 := by
  have hlim : Filter.Tendsto (fun t : ℝ => Real.exp (-(t * r))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp
      (Filter.tendsto_neg_atTop_atBot.comp (Filter.tendsto_id.atTop_mul_const hr))
  exact ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨0, h⟩)

/-- **Chernoff's bound** for the lower tail, in relative-entropy form:
`P(∑ i ∈ s, X i ≤ a #s) ≤ exp(−#s · D(a ‖ p))` for `0 ≤ a ≤ p < 1`. -/
theorem measureReal_sum_le_le_exp_klBern (hX : IsBernoulliFamily μ p X) (hp0 : 0 < p)
    (hp1 : p < 1) (s : Finset ι) {a : ℝ} (ha0 : 0 ≤ a) (hap : a ≤ p) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ a * s.card} ≤ Real.exp (-(s.card * klBern a p)) := by
  rcases ha0.eq_or_lt with rfl | ha0
  · -- `a = 0`: let `t → −∞` in `P(Z ≤ 0) ≤ (1 − p + p eᵗ)^#s`; the limit is
    -- `(1 − p)^#s = exp(−#s D(0 ‖ p))`.
    have hlim : Filter.Tendsto (fun t => (1 - p + p * Real.exp t) ^ s.card) Filter.atBot
        (nhds ((1 - p) ^ s.card)) := by
      have := ((Real.tendsto_exp_atBot.const_mul p).const_add (1 - p)).pow s.card
      rwa [mul_zero, add_zero] at this
    have hle : μ.real {ω | ∑ i ∈ s, X i ω ≤ 0 * s.card} ≤ (1 - p) ^ s.card := by
      refine ge_of_tendsto hlim (Filter.eventually_atBot.2 ⟨0, fun t ht => ?_⟩)
      have := hX.measureReal_sum_le_le_exp_mul s ht (0 * s.card)
      rwa [show -t * (0 * (s.card : ℝ)) = 0 by ring, Real.exp_zero, one_mul] at this
    have hkl : klBern 0 p = -Real.log (1 - p) := by
      simp [klBern, Real.log_inv]
    rw [hkl, mul_neg, neg_neg, Real.exp_nat_mul, Real.exp_log (by linarith)]
    exact hle
  · -- `0 < a ≤ p`: Chernoff's bound with `t = log(a(1 − p) / (p(1 − a))) ≤ 0`.
    have ha1 : a < 1 := lt_of_le_of_lt hap hp1
    have ht : Real.log (a * (1 - p) / (p * (1 - a))) ≤ 0 := by
      apply Real.log_nonpos (div_pos (mul_pos ha0 (by linarith)) (mul_pos hp0 (by linarith))).le
      rw [div_le_one (mul_pos hp0 (by linarith))]
      nlinarith
    calc μ.real {ω | ∑ i ∈ s, X i ω ≤ a * s.card}
        ≤ Real.exp (-Real.log (a * (1 - p) / (p * (1 - a))) * (a * s.card)) *
            (1 - p + p * Real.exp (Real.log (a * (1 - p) / (p * (1 - a))))) ^ s.card :=
          hX.measureReal_sum_le_le_exp_mul s ht _
      _ = Real.exp (-(s.card * klBern a p)) := exp_mul_pow_eq_exp_klBern ha0 ha1 hp0 hp1 s.card

/-- **Chernoff's bound** for the upper tail, in relative-entropy form:
`P(∑ i ∈ s, X i ≥ a #s) ≤ exp(−#s · D(a ‖ p))` for `0 < p ≤ a ≤ 1`, `p < 1`. -/
private lemma measureReal_sum_ge_le_exp_klBern (hX : IsBernoulliFamily μ p X) (hp0 : 0 < p)
    (hp1 : p < 1) (s : Finset ι) {a : ℝ} (hpa : p ≤ a) (ha1 : a ≤ 1) :
    μ.real {ω | a * s.card ≤ ∑ i ∈ s, X i ω} ≤ Real.exp (-(s.card * klBern a p)) := by
  rcases ha1.eq_or_lt with rfl | ha1
  · -- `a = 1`: let `t → ∞` in `P(Z ≥ #s) ≤ e^{−t #s} (1 − p + p eᵗ)^#s = ((1 − p) e^{−t} + p)^#s`;
    -- the limit is `p^#s = exp(−#s D(1 ‖ p))`.
    have hlim : Filter.Tendsto (fun t => ((1 - p) * Real.exp (-t) + p) ^ s.card) Filter.atTop
        (nhds (p ^ s.card)) := by
      have := ((Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (1 - p)).add_const p).pow s.card
      rwa [mul_zero, zero_add] at this
    have hle : μ.real {ω | 1 * s.card ≤ ∑ i ∈ s, X i ω} ≤ p ^ s.card := by
      refine ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨0, fun t ht => ?_⟩)
      refine (hX.measureReal_sum_ge_le_exp_mul s ht _).trans (le_of_eq ?_)
      rw [one_mul, show -t * (s.card : ℝ) = s.card * (-t) by ring, Real.exp_nat_mul, ← mul_pow]
      congr 1
      have : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      linear_combination p * this
    have hkl : klBern 1 p = -Real.log p := by
      simp [klBern, Real.log_inv]
    rw [hkl, mul_neg, neg_neg, Real.exp_nat_mul, Real.exp_log hp0]
    exact hle
  · -- `p ≤ a < 1`: Chernoff's bound with `t = log(a(1 − p) / (p(1 − a))) ≥ 0`.
    have ha0 : 0 < a := lt_of_lt_of_le hp0 hpa
    have ht : 0 ≤ Real.log (a * (1 - p) / (p * (1 - a))) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (mul_pos hp0 (by linarith))]
      nlinarith
    calc μ.real {ω | a * s.card ≤ ∑ i ∈ s, X i ω}
        ≤ Real.exp (-Real.log (a * (1 - p) / (p * (1 - a))) * (a * s.card)) *
            (1 - p + p * Real.exp (Real.log (a * (1 - p) / (p * (1 - a))))) ^ s.card :=
          hX.measureReal_sum_ge_le_exp_mul s ht _
      _ = Real.exp (-(s.card * klBern a p)) := exp_mul_pow_eq_exp_klBern ha0 ha1 hp0 hp1 s.card

/-- **Chernoff's bound** for the upper tail: `P(Z ≥ T) ≤ exp(−(T − pm)² / (2T))` for `T > pm`,
where `Z = ∑ i ∈ s, X i` and `m = #s` (sparse paper, equation (29)). -/
theorem measureReal_sum_ge_le_exp (hX : IsBernoulliFamily μ p X) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Finset ι) {T : ℝ} (hT : p * s.card < T) :
    μ.real {ω | T ≤ ∑ i ∈ s, X i ω} ≤ Real.exp (-((T - p * s.card) ^ 2 / (2 * T))) := by
  have hT0 : 0 < T := lt_of_le_of_lt (by positivity) hT
  by_cases hTm : (s.card : ℝ) < T
  · -- `Z ≤ #s < T`: the event is empty.
    have hempty : {ω | T ≤ ∑ i ∈ s, X i ω} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_le_of_lt (hX.sum_mem_Icc s ω).2 hTm
    rw [hempty, measureReal_empty]
    exact (Real.exp_pos _).le
  replace hTm : T ≤ s.card := not_lt.mp hTm
  rcases hp0.eq_or_lt with rfl | hp0
  · -- `p = 0`: `P(Z ≥ T) ≤ e^{−tT}` for every `t ≥ 0`, so `P(Z ≥ T) = 0`.
    refine (le_zero_of_forall_le_exp hT0 fun t ht => ?_).trans (Real.exp_pos _).le
    refine (hX.measureReal_sum_ge_le_exp_mul s ht T).trans (le_of_eq ?_)
    simp [neg_mul]
  · -- `0 < p < 1` and `pm < T ≤ m`: the relative-entropy bound with `a = T / m ∈ (p, 1]`,
    -- and `m D(a ‖ p) ≥ m (a − p)² / (2a) = (T − pm)² / (2T)`.
    have hm : (0 : ℝ) < s.card := lt_of_lt_of_le hT0 hTm
    have hp1' : p < 1 := lt_of_mul_lt_mul_right (by linarith : p * s.card < 1 * s.card) hm.le
    have ha : T / s.card * s.card = T := div_mul_cancel₀ _ hm.ne'
    have hpa : p ≤ T / s.card := by rw [le_div_iff₀ hm]; exact hT.le
    have ha1 : T / s.card ≤ 1 := by rw [div_le_one hm]; exact hTm
    have hkl := sq_div_le_klBern_of_le hp0 hp1' hpa ha1
    calc μ.real {ω | T ≤ ∑ i ∈ s, X i ω}
        = μ.real {ω | T / s.card * s.card ≤ ∑ i ∈ s, X i ω} := by rw [ha]
      _ ≤ Real.exp (-(s.card * klBern (T / s.card) p)) :=
          hX.measureReal_sum_ge_le_exp_klBern hp0 hp1' s hpa ha1
      _ ≤ Real.exp (-((T - p * s.card) ^ 2 / (2 * T))) := by
          gcongr
          calc (T - p * s.card) ^ 2 / (2 * T)
              = s.card * ((T / s.card - p) ^ 2 / (2 * (T / s.card))) := by
                field_simp
            _ ≤ s.card * klBern (T / s.card) p := by gcongr

/-- **Chernoff's bound** for the lower tail: `P(Z ≤ T) ≤ exp(−(pm − T)² / (2pm))` for `T < pm`,
where `Z = ∑ i ∈ s, X i` and `m = #s` (sparse paper, equation (30)). -/
theorem measureReal_sum_le_le_exp (hX : IsBernoulliFamily μ p X) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Finset ι) {T : ℝ} (hT : T < p * s.card) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ T} ≤ Real.exp (-((p * s.card - T) ^ 2 / (2 * (p * s.card)))) := by
  by_cases hT0 : T < 0
  · -- `Z ≥ 0 > T`: the event is empty.
    have hempty : {ω | ∑ i ∈ s, X i ω ≤ T} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hT0 (hX.sum_mem_Icc s ω).1
    rw [hempty, measureReal_empty]
    exact (Real.exp_pos _).le
  replace hT0 : 0 ≤ T := not_lt.mp hT0
  have hpm : 0 < p * s.card := lt_of_le_of_lt hT0 hT
  have hm : (0 : ℝ) < s.card := pos_of_mul_pos_right hpm hp0
  have hp0' : 0 < p := pos_of_mul_pos_left hpm hm.le
  rcases hp1.eq_or_lt with rfl | hp1
  · -- `p = 1`: `P(Z ≤ T) ≤ e^{t(m − T)}` for every `t ≤ 0`, so `P(Z ≤ T) = 0`.
    refine (le_zero_of_forall_le_exp (r := s.card - T) (by linarith) fun u hu => ?_).trans
      (Real.exp_pos _).le
    refine (hX.measureReal_sum_le_le_exp_mul s (neg_nonpos.mpr hu) T).trans (le_of_eq ?_)
    rw [show (1 : ℝ) - 1 + 1 * Real.exp (-u) = Real.exp (-u) by ring, ← Real.exp_nat_mul,
      ← Real.exp_add]
    congr 1
    ring
  · -- `0 < p < 1` and `0 ≤ T < pm`: the relative-entropy bound with `a = T / m ∈ [0, p)`,
    -- and `m D(a ‖ p) ≥ m (p − a)² / (2p) = (pm − T)² / (2pm)`.
    have ha : T / s.card * s.card = T := div_mul_cancel₀ _ hm.ne'
    have ha0 : 0 ≤ T / s.card := div_nonneg hT0 hm.le
    have hap : T / s.card ≤ p := by rw [div_le_iff₀ hm]; exact hT.le
    have hkl := sq_div_le_klBern_of_ge hp0' hp1 ha0 hap
    calc μ.real {ω | ∑ i ∈ s, X i ω ≤ T}
        = μ.real {ω | ∑ i ∈ s, X i ω ≤ T / s.card * s.card} := by rw [ha]
      _ ≤ Real.exp (-(s.card * klBern (T / s.card) p)) :=
          hX.measureReal_sum_le_le_exp_klBern hp0' hp1 s ha0 hap
      _ ≤ Real.exp (-((p * s.card - T) ^ 2 / (2 * (p * s.card)))) := by
          gcongr
          calc (p * s.card - T) ^ 2 / (2 * (p * s.card))
              = s.card * ((p - T / s.card) ^ 2 / (2 * p)) := by
                field_simp
            _ ≤ s.card * klBern (T / s.card) p := by gcongr

/-- The upper tail in the form `P(Z ≥ k) ≤ (e p m / k)^k` for `k > 0`, where `m = #s`, written
`exp(−k log(k / (e p m)))`: Markov's inequality for `e^(θ Z)` with `θ = log(k / (p m))`, and
`E e^(θ Z) = (1 − p + p e^θ)^m ≤ exp(p m (e^θ − 1))`. (When `k ≤ e p m` or `p m = 0`, the
right-hand side is at least `1`.) -/
theorem measureReal_sum_ge_le_exp_mul_log (hX : IsBernoulliFamily μ p X) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (s : Finset ι) {k : ℝ} (hk : 0 < k) :
    μ.real {ω | k ≤ ∑ i ∈ s, X i ω} ≤
      Real.exp (-(k * Real.log (k / (Real.exp 1 * (p * s.card))))) := by
  have hpm0 : 0 ≤ p * s.card := by positivity
  by_cases hle : k ≤ Real.exp 1 * (p * s.card)
  · -- `k ≤ e p m`: `log(k / (e p m)) ≤ 0`, so the right-hand side is at least `1`.
    refine measureReal_le_one.trans (Real.one_le_exp_iff.mpr ?_)
    have hlog : Real.log (k / (Real.exp 1 * (p * s.card))) ≤ 0 :=
      Real.log_nonpos (by positivity) (div_le_one_of_le₀ hle (by positivity))
    nlinarith
  push Not at hle
  rcases hpm0.eq_or_lt with hpm | hpm
  · -- `p m = 0`: `log(k / 0) = 0`, so the right-hand side is `1`.
    rw [← hpm, mul_zero, div_zero, Real.log_zero, mul_zero, neg_zero, Real.exp_zero]
    exact measureReal_le_one
  · -- `k > e p m > 0`: Chernoff's bound with `θ = log(k / (p m)) ≥ 0`, so `e^θ = k / (p m)`.
    have hkpm : p * s.card ≤ k := by
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    have hθ : 0 ≤ Real.log (k / (p * s.card)) :=
      Real.log_nonneg (by rw [le_div_iff₀ hpm, one_mul]; exact hkpm)
    have hexp : Real.exp (Real.log (k / (p * s.card))) = k / (p * s.card) :=
      Real.exp_log (div_pos hk hpm)
    -- `log(k / (e p m)) = log(k / (p m)) − 1`.
    have hlog : Real.log (k / (Real.exp 1 * (p * s.card))) = Real.log (k / (p * s.card)) - 1 := by
      rw [Real.log_div hk.ne' (by positivity), Real.log_mul (Real.exp_pos 1).ne' hpm.ne',
        Real.log_exp, Real.log_div hk.ne' hpm.ne']
      ring
    -- `1 − p + p e^θ ≤ exp(p (e^θ − 1))`.
    have hbase : 1 - p + p * Real.exp (Real.log (k / (p * s.card))) ≤
        Real.exp (p * (Real.exp (Real.log (k / (p * s.card))) - 1)) := by
      linarith [Real.add_one_le_exp (p * (Real.exp (Real.log (k / (p * s.card))) - 1))]
    have hbase0 : 0 ≤ 1 - p + p * Real.exp (Real.log (k / (p * s.card))) := by
      nlinarith [Real.exp_pos (Real.log (k / (p * s.card)))]
    calc μ.real {ω | k ≤ ∑ i ∈ s, X i ω}
        ≤ Real.exp (-Real.log (k / (p * s.card)) * k) *
            (1 - p + p * Real.exp (Real.log (k / (p * s.card)))) ^ s.card :=
          hX.measureReal_sum_ge_le_exp_mul s hθ k
      _ ≤ Real.exp (-Real.log (k / (p * s.card)) * k) *
            Real.exp (p * (Real.exp (Real.log (k / (p * s.card))) - 1)) ^ s.card := by
          gcongr
      _ = Real.exp (-Real.log (k / (p * s.card)) * k + (k - p * s.card)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, hexp]
          congr 2
          calc (s.card : ℝ) * (p * (k / (p * s.card) - 1))
              = p * s.card * (k / (p * s.card)) - p * s.card := by ring
            _ = k - p * s.card := by rw [mul_div_cancel₀ _ hpm.ne']
      _ ≤ Real.exp (-(k * Real.log (k / (Real.exp 1 * (p * s.card))))) := by
          rw [hlog]
          gcongr
          nlinarith

end IsBernoulliFamily

end ProbabilityTheory
