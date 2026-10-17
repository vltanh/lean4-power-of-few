module

public import PowerOfFew.Sparse.DayOne
public import PowerOfFew.Model.Lazy
public import Basic.Probability.Concentration

/-!
# Sparse paper, Section 4: the first day with random activations and updates

Proposition 4.2 of the sparse paper (proved in its Appendix B): the argument of Lemma 2.1 and
Proposition 2.2, run on the subgraph induced by the vertices active on day 1. See
`PowerOfFew/Sparse/Activation.lean` for the setting, the readings and the corrections of Section 4.

The proof follows Appendix B:

* the activation counts `|A₀ ∩ B₀|`, `|A₀ ∩ R₀|` are within `C_ε √(p_ac |·|)` of their means with
  probability at least `1 − ε/2` (the paper's (day1-lazy-pf-bound-Vac); Chebyshev's inequality,
  `lazyDayOneAux_act_dev`);
* for such activations `A₀ = A`, with `m = |A|`, the Blue active vertices of day 1 number
  `|B| = ∑_{i < m} (U_i 𝟙_H(i) + (1 − U_i) 𝟙_{B₀}(i))` (the paper's (lazy-b1-formula),
  `lazyDayOneAux_ncard_lazyStep`), where `H` is the Blue set after one day of majority dynamics on
  the active subgraph `G[A] ∼ G(m, p)` and `U_i` the update coins;
* Proposition 2.2 on `G[A]` bounds `E|H|` and `Var|H|`, whence `E|B|` (the paper's (lazy-b1-exp),
  `lazyDayOneAux_exp`) and `Var|B| ≤ m/4 + p_up² Var|H|` (the paper's (lazy-B-var),
  `lazyDayOneAux_var`), and Chebyshev's inequality bounds `|B|` (the paper's
  (day1-lazy-pf-bound-final), `lazyDayOneAux_cheb`);
* `|B₁| = |B| + |B₀| − |A ∩ B₀|` and the paper's arithmetic give `|B₁| ≤ n/2 − K √(n/(p p_ac))`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-! ### The constant `D₂` -/

/-- `D₂ = Φ₀(3/2) − 0.28 > 0`: `e^(−x²/2) ≥ 1 − x²/2` gives `∫₀^{3/2} e^(−x²/2) dx ≥ 15/16`, and
`√(2π) ≤ 3`, so `Φ₀(3/2) ≥ 5/16 > 0.28`. -/
private lemma lazyDayOneAux_Dc_two_pos : 0 < Dc 2 := by
  have hint : (15 / 16 : ℝ) ≤ ∫ x in (0:ℝ)..(3/2), Real.exp (-x ^ 2 / 2) := by
    have h1 : ∫ x in (0:ℝ)..(3/2), (1 - x ^ 2 / 2) = 15/16 := by
      rw [intervalIntegral.integral_sub, intervalIntegral.integral_div, integral_pow]
      · norm_num
      · exact intervalIntegrable_const
      · exact ((continuous_pow 2).div_const 2).intervalIntegrable _ _
    rw [← h1]
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ fun x _ => ?_
    · exact (by fun_prop : Continuous fun x : ℝ => 1 - x ^ 2 / 2).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun x : ℝ => Real.exp (-x ^ 2 / 2)).intervalIntegrable _ _
    · have := Real.add_one_le_exp (-x ^ 2 / 2)
      linarith
  have hsqrt : Real.sqrt (2 * Real.pi) ≤ 3 := by
    rw [show (3:ℝ) = Real.sqrt 9 by
      rw [show (9:ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_le_four])
  have hpos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hinv : (1 / 3 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
    rw [one_div]; exact inv_anti₀ hpos hsqrt
  unfold Dc Φ₀
  rw [show (2 : ℝ) - 1 / 2 = 3 / 2 by norm_num]
  have : (1 / 3 : ℝ) * (15 / 16) ≤ (Real.sqrt (2 * Real.pi))⁻¹ *
      ∫ x in (0:ℝ)..(3/2), Real.exp (-x ^ 2 / 2) :=
    mul_le_mul hinv hint (by norm_num) (inv_nonneg.2 hpos.le)
  norm_num at this ⊢
  linarith

/-! ### Measure-theoretic helpers -/

/-- A product with a finite discrete factor, as a sum over that factor. -/
private lemma lazyDayOneAux_prod_real_eq_sum {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Fintype β] [MeasurableSingletonClass β] (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hα : ∀ s : Set α, MeasurableSet s)
    (P : α → β → Prop) :
    (μ.prod ν).real {x | P x.1 x.2} = ∑ b, ν.real {b} * μ.real {a | P a b} := by
  have hS : MeasurableSet {x : α × β | P x.1 x.2} := by
    have : {x : α × β | P x.1 x.2} = ⋃ b : β, {a | P a b} ×ˢ {b} := by
      ext ⟨a, b⟩; simp
    rw [this]
    exact MeasurableSet.iUnion fun b => (hα _).prod (measurableSet_singleton b)
  rw [measureReal_def, Measure.prod_apply_symm hS, lintegral_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [ENNReal.toReal_mul, mul_comm]
    rfl
  · intro b _
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

/-- The integral of a function of the first coordinate, under a product with a probability
measure. -/
private lemma lazyDayOneAux_integral_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [IsProbabilityMeasure ν] (f : α → ℝ) :
    ∫ w, f w.1 ∂(μ.prod ν) = ∫ x, f x ∂μ := by
  simpa using integral_prod_mul (μ := μ) (ν := ν) f (fun _ => (1 : ℝ))

/-- Chebyshev's inequality for a sum `Z` of `k` independent Bernoulli(`q`) variables:
`P(|Z − qk| > C √(qk)) ≤ 1/C²` (the variance of `Z` is `qk(1 − q) ≤ qk`). -/
private lemma lazyDayOneAux_bernoulli_dev {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {q : ℝ} {X : ι → Ω → ℝ} (hX : IsBernoulliFamily μ q X)
    (hq0 : 0 < q) (s : Finset ι) {C : ℝ} (hC : 0 < C) :
    μ.real {ω | C * Real.sqrt (q * s.card) < |∑ i ∈ s, X i ω - q * s.card|} ≤ 1 / C ^ 2 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp; positivity
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hmem : ∀ i, MemLp (X i) 2 μ := fun i =>
    MemLp.of_bound (hX.measurable i).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rcases hX.zero_or_one i ω with h | h <;> simp [h])
  set S : Ω → ℝ := fun ω => ∑ i ∈ s, X i ω with hS_def
  have hS : S = ∑ i ∈ s, X i := (Finset.sum_fn s X).symm
  have hSmem : MemLp S 2 μ := by rw [hS]; exact memLp_finsetSum' s fun i _ => hmem i
  have hE : μ[S] = q * s.card := by
    rw [hS_def, integral_finsetSum s fun i _ => (hmem i).integrable one_le_two]
    simp [hX.integral_eq, mul_comm]
  have hvar1 : ∀ i, variance (X i) μ = q * (1 - q) := fun i => by
    rw [variance_eq_integral (hX.measurable i).aemeasurable, hX.integral_eq i,
      hX.integral_sq_sub i]
  have hV : variance S μ = s.card * (q * (1 - q)) := by
    rw [hS, IndepFun.variance_sum (fun i _ => hmem i)
      (fun i _ j _ hij => hX.indep.indepFun hij)]
    simp [hvar1]
  have hc : 0 < C * Real.sqrt (q * s.card) := by positivity
  have hcheb := meas_ge_le_variance_div_sq hSmem hc
  have hsq : (C * Real.sqrt (q * s.card)) ^ 2 = C ^ 2 * (q * s.card) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  calc μ.real {ω | C * Real.sqrt (q * s.card) < |∑ i ∈ s, X i ω - q * s.card|}
      ≤ μ.real {ω | C * Real.sqrt (q * s.card) ≤ |S ω - μ[S]|} := by
        refine measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)
        simp only [Set.mem_ofPred_eq] at hω ⊢
        rw [hE]; exact hω.le
    _ ≤ variance S μ / (C * Real.sqrt (q * s.card)) ^ 2 := by
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))
          hcheb
    _ = (1 - q) / C ^ 2 := by
        rw [hV, hsq]; field_simp
    _ ≤ 1 / C ^ 2 := by gcongr; linarith

/-- The coins of one kind (activation or update) of one day: independent Bernoulli(`q`). -/
private abbrev lazyDayOneAux_coins (n : ℕ) (q : ℝ) : Measure (Fin n → Bool) :=
  Measure.pi fun _ : Fin n => bernoulliMeasure true false (toUnit q)

/-- The paper's (day1-lazy-pf-bound-Vac), for one set `S`: the number of active vertices of `S`
deviates from `p_ac |S|` by more than `C √(p_ac |S|)` with probability at most `1/C²`
(Chebyshev's inequality). -/
private lemma lazyDayOneAux_act_dev {n : ℕ} {pac pup : ℝ} (hpac0 : 0 < pac) (hpac1 : pac ≤ 1)
    (S : Set (Fin n)) {C : ℝ} (hC : 0 < C) :
    (dayLaw n pac pup).real {d | C * Real.sqrt (pac * S.ncard) <
      |((S ∩ {v | d.1 v = true}).ncard : ℝ) - pac * S.ncard|} ≤ 1 / C ^ 2 := by
  classical
  have h := lazyDayOneAux_bernoulli_dev
    (isBernoulliFamily_act (n := n) (pup := pup) hpac0.le hpac1) hpac0 S.toFinset hC
  simp only [← Set.ncard_eq_toFinset_card'] at h
  convert h using 4 with d
  rw [ncard_inter_setOf_eq_sum]

/-! ### The Blue active vertices of day 1 -/

open Classical in
/-- The indicator `𝟙_S(i)`, as a real number. -/
private def lazyDayOneAux_ind {m : ℕ} (S : Set (Fin m)) (i : Fin m) : ℝ :=
  if i ∈ S then 1 else 0

private lemma lazyDayOneAux_ind_mem {m : ℕ} (S : Set (Fin m)) (i : Fin m) :
    0 ≤ lazyDayOneAux_ind S i ∧ lazyDayOneAux_ind S i ≤ 1 := by
  unfold lazyDayOneAux_ind; split_ifs <;> norm_num

private lemma lazyDayOneAux_sum_ind {m : ℕ} (S : Set (Fin m)) :
    ∑ i, lazyDayOneAux_ind S i = S.ncard := by
  classical
  calc ∑ i, lazyDayOneAux_ind S i = ((Finset.univ.filter (· ∈ S)).card : ℝ) := by
        simp only [lazyDayOneAux_ind]
        rw [Finset.sum_boole]
    _ = S.ncard := by
        rw [← Set.ncard_coe_finset]
        congr 2
        ext i; simp

/-- The number `|B|` of Blue active vertices on day 1, with the active vertices renumbered by
`e : Fin m → Fin n`: an active vertex `i` that updates (`u (e i)`) is Blue iff it is Blue after one
day of majority dynamics on the active subgraph `G`, and one that does not update keeps its colour
(the paper's equation (lazy-b1-formula)). -/
private def lazyDayOneAux_X {n m : ℕ} (e : Fin m → Fin n) (B' : Set (Fin m))
    (G : SimpleGraph (Fin m)) (u : Fin n → Bool) : ℝ :=
  ∑ i, if u (e i) = true then lazyDayOneAux_ind (majorityStep G B') i
    else lazyDayOneAux_ind B' i

/-- The paper's last display: `|B₁| = |B| + |B₀| − |A ∩ B₀|` where `B = B₁ ∩ A`, with `|B|`
written as `lazyDayOneAux_X` on the active subgraph (from equation (main-lazy-details-temp0),
`lazyStep_eq`, and `enumSet_mem_hypoStep_iff`). -/
private lemma lazyDayOneAux_ncard_lazyStep {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Set (Fin n)) (u : Fin n → Bool) (B₀ : Set (Fin n)) :
    ((lazyStep G A {v | u v = true} B₀).ncard : ℝ) =
      B₀.ncard - (A ∩ B₀).ncard +
        lazyDayOneAux_X (enumSet A) (enumSet A ⁻¹' B₀) (inducedOn G A) u := by
  classical
  set L := lazyStep G A {v | u v = true} B₀ with hL
  have hLeq := lazyStep_eq G A {v | u v = true} B₀
  have h1 := Set.ncard_inter_add_ncard_sdiff_eq_ncard L A (Set.toFinite L)
  have h2 : L \ A = B₀ \ A := by
    ext x
    rw [hL, hLeq]
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  have h3 := Set.ncard_inter_add_ncard_sdiff_eq_ncard B₀ A (Set.toFinite B₀)
  have h4 : (L ∩ A).ncard = (enumSet A ⁻¹' L).ncard := by
    rw [ncard_preimage_enumSet, Set.inter_comm]
  have hmemA : ∀ i, enumSet A i ∈ A := fun i =>
    Eq.subset (range_enumSet A) (Set.mem_range_self i)
  have h5 : ∀ i, lazyDayOneAux_ind (enumSet A ⁻¹' L) i =
      if u (enumSet A i) = true then
        lazyDayOneAux_ind (majorityStep (inducedOn G A) (enumSet A ⁻¹' B₀)) i
      else lazyDayOneAux_ind (enumSet A ⁻¹' B₀) i := fun i => by
    have hA := hmemA i
    by_cases hu : u (enumSet A i) = true
    · rw [ite_eq_left hu]
      have : enumSet A i ∈ L ↔ enumSet A i ∈ hypoStep G A B₀ := by
        rw [hL, hLeq]
        simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq, hA, hu,
          and_self, not_true_eq_false, and_false, true_and, false_or]
      simp only [lazyDayOneAux_ind, Set.mem_preimage, this, enumSet_mem_hypoStep_iff]
    · rw [ite_eq_right hu]
      have : enumSet A i ∈ L ↔ enumSet A i ∈ B₀ := by
        rw [hL, hLeq]
        simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq, hA, hu,
          Bool.false_eq_true, and_false, not_false_eq_true, and_true, false_and, or_false]
      simp only [lazyDayOneAux_ind, Set.mem_preimage, this]
  have h6 : ((enumSet A ⁻¹' L).ncard : ℝ) =
      lazyDayOneAux_X (enumSet A) (enumSet A ⁻¹' B₀) (inducedOn G A) u := by
    rw [← lazyDayOneAux_sum_ind, lazyDayOneAux_X]
    exact Finset.sum_congr rfl fun i _ => h5 i
  rw [h2] at h1
  rw [Set.inter_comm A B₀, ← h6, ← h4]
  have h1' : ((L ∩ A).ncard : ℝ) + ((B₀ \ A).ncard : ℝ) = L.ncard := by exact_mod_cast h1
  have h3' : ((B₀ ∩ A).ncard : ℝ) + ((B₀ \ A).ncard : ℝ) = B₀.ncard := by exact_mod_cast h3
  linarith

/-! ### Mean and variance of `|B|` on `G(m, p) ⊗ Bernoulli(p_up)^n` -/

section Moments

/-- Every set of graphs on `Fin m` is measurable. -/
local instance lazyDayOneAux_msc (m : ℕ) : MeasurableSingletonClass (SimpleGraph (Fin m)) :=
  ⟨fun G => PowerOfFew.measurableSet_simpleGraph {G}⟩

/-- The paper's Step 1.1, before Proposition 2.2 is applied: since the update coins are
independent of the graph, `E|B| = (1 − p_up) |B₀ ∩ A| + p_up E|H|`. -/
private lemma lazyDayOneAux_exp {n m : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (B' : Set (Fin m)) (p : ℝ) {pup : ℝ} (hpup0 : 0 ≤ pup) (hpup1 : pup ≤ 1) :
    (∫ w, lazyDayOneAux_X e B' w.1 w.2 ∂((SimpleGraph.binomialRandom (Fin m) (toUnit p)).prod
        (lazyDayOneAux_coins n pup))) =
      (1 - pup) * B'.ncard + pup * gnpExp m p (fun G => ((blueAfter G B' 1).ncard : ℝ)) := by
  classical
  set ν := SimpleGraph.binomialRandom (Fin m) (toUnit p) with hν
  set π := lazyDayOneAux_coins n pup with hπ
  set U : Fin m → (Fin n → Bool) → ℝ := fun i ω => if ω (e i) then 1 else 0 with hU_def
  have hU : IsBernoulliFamily π pup U := (isBernoulliFamily_coins hpup0 hpup1).comp he
  set b : Fin m → ℝ := fun i => lazyDayOneAux_ind B' i with hb_def
  set x : Fin m → SimpleGraph (Fin m) → ℝ := fun i G => lazyDayOneAux_ind (majorityStep G B') i
    with hx_def
  have hf : ∀ G, ((blueAfter G B' 1).ncard : ℝ) = ∑ i, x i G := fun G =>
    (lazyDayOneAux_sum_ind (majorityStep G B')).symm
  have hsumb : ∑ i, b i = B'.ncard := lazyDayOneAux_sum_ind B'
  have hX : ∀ w : SimpleGraph (Fin m) × (Fin n → Bool),
      lazyDayOneAux_X e B' w.1 w.2 = ∑ i, (b i + (x i w.1 - b i) * U i w.2) := by
    intro w
    simp only [lazyDayOneAux_X]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : w.2 (e i) = true <;> simp [h, U, x, b]
  simp_rw [hX]
  rw [integral_finsetSum _ (fun i _ => Integrable.of_finite)]
  have h1 : ∀ i, ∫ w, (b i + (x i w.1 - b i) * U i w.2) ∂(ν.prod π) =
      b i + (∫ G, x i G ∂ν - b i) * pup := by
    intro i
    rw [integral_add (integrable_const _) Integrable.of_finite, integral_const,
      integral_prod_mul (fun G => x i G - b i) (U i), hU.integral_eq i,
      integral_sub Integrable.of_finite (integrable_const _), integral_const]
    simp
  simp_rw [h1]
  unfold gnpExp
  simp_rw [hf]
  rw [integral_finsetSum _ (fun i _ => Integrable.of_finite)]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, hsumb]
  ring

/-- The paper's Step 1.2, before Proposition 2.2 is applied: `Var|B| ≤ m/4 + p_up² Var|H|`.
The paper sums `Var 𝟙_B(v) ≤ 1/4` and `Cov(𝟙_B(u), 𝟙_B(v)) = p_up² Cov(𝟙_H(u), 𝟙_H(v))`
(`u ≠ v`); here the same computation is done by expanding the square of
`|B| − E|B| = ∑ᵢ (𝟙_H(i) − 𝟙_{B₀}(i))(Uᵢ − p_up) + p_up (|H| − E|H|)` on the product space. -/
private lemma lazyDayOneAux_var {n m : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (B' : Set (Fin m)) (p : ℝ) {pup : ℝ} (hpup0 : 0 ≤ pup) (hpup1 : pup ≤ 1) :
    variance (fun w => lazyDayOneAux_X e B' w.1 w.2)
        ((SimpleGraph.binomialRandom (Fin m) (toUnit p)).prod (lazyDayOneAux_coins n pup)) ≤
      m / 4 + pup ^ 2 * gnpVar m p (fun G => ((blueAfter G B' 1).ncard : ℝ)) := by
  classical
  have hE := lazyDayOneAux_exp e he B' p hpup0 hpup1
  set ν := SimpleGraph.binomialRandom (Fin m) (toUnit p) with hν
  set π := lazyDayOneAux_coins n pup with hπ
  set U : Fin m → (Fin n → Bool) → ℝ := fun i ω => if ω (e i) then 1 else 0 with hU_def
  have hU : IsBernoulliFamily π pup U := (isBernoulliFamily_coins hpup0 hpup1).comp he
  set b : Fin m → ℝ := fun i => lazyDayOneAux_ind B' i with hb_def
  set x : Fin m → SimpleGraph (Fin m) → ℝ := fun i G => lazyDayOneAux_ind (majorityStep G B') i
    with hx_def
  set f : SimpleGraph (Fin m) → ℝ := fun G => ((blueAfter G B' 1).ncard : ℝ) with hf_def
  have hf : ∀ G, f G = ∑ i, x i G := fun G => (lazyDayOneAux_sum_ind (majorityStep G B')).symm
  have hsumb : ∑ i, b i = B'.ncard := lazyDayOneAux_sum_ind B'
  set Ef := ∫ G, f G ∂ν with hEf
  have hX : ∀ w : SimpleGraph (Fin m) × (Fin n → Bool),
      lazyDayOneAux_X e B' w.1 w.2 = ∑ i, (b i + (x i w.1 - b i) * U i w.2) := by
    intro w
    simp only [lazyDayOneAux_X]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : w.2 (e i) = true <;> simp [h, U, x, b]
  have hgE : gnpExp m p f = Ef := rfl
  rw [hgE] at hE
  rw [variance_eq_integral Measurable.of_discrete.aemeasurable, hE]
  -- the centred variable: `X − E X = ∑ᵢ (xᵢ − bᵢ)(Uᵢ − p_up) + p_up (f − E f)`
  have hlin : ∀ w : SimpleGraph (Fin m) × (Fin n → Bool),
      lazyDayOneAux_X e B' w.1 w.2 - ((1 - pup) * B'.ncard + pup * Ef) =
        ∑ i, (x i w.1 - b i) * (U i w.2 - pup) + pup * (f w.1 - Ef) := by
    intro w
    have e1 : ∑ i, (b i + (x i w.1 - b i) * U i w.2) =
        ∑ i, b i + ∑ i, (x i w.1 - b i) * U i w.2 := Finset.sum_add_distrib
    have e2 : ∑ i, (x i w.1 - b i) * (U i w.2 - pup) =
        ∑ i, (x i w.1 - b i) * U i w.2 - pup * (∑ i, x i w.1 - ∑ i, b i) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hX, hf, ← hsumb, e1, e2]
    ring
  have hsq : ∀ (a : Fin m → ℝ) (c : ℝ),
      (∑ i, a i + c) ^ 2 = ∑ i, ∑ j, a i * a j + ∑ i, 2 * c * a i + c ^ 2 := by
    intro a c
    rw [← Finset.mul_sum, ← Finset.sum_mul_sum]
    ring
  have hpt : ∀ w : SimpleGraph (Fin m) × (Fin n → Bool),
      (lazyDayOneAux_X e B' w.1 w.2 - ((1 - pup) * B'.ncard + pup * Ef)) ^ 2 =
        ∑ i, ∑ j, ((x i w.1 - b i) * (x j w.1 - b j)) * ((U i w.2 - pup) * (U j w.2 - pup)) +
        ∑ i, (2 * (pup * (f w.1 - Ef)) * (x i w.1 - b i)) * (U i w.2 - pup) +
        pup ^ 2 * (f w.1 - Ef) ^ 2 := by
    intro w
    rw [hlin, hsq]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        ring
    · ring
  simp_rw [hpt]
  -- integrate term by term; each term is a function of the graph times one of the coins
  have hUc : ∀ i, ∫ ω, (U i ω - pup) ∂π = 0 := fun i => by
    rw [integral_sub Integrable.of_finite (integrable_const _), hU.integral_eq i, integral_const]
    simp
  have hUU : ∀ i j, ∫ ω, (U i ω - pup) * (U j ω - pup) ∂π =
      if i = j then pup * (1 - pup) else 0 := fun i j => by
    split_ifs with hij
    · subst hij
      rw [← hU.integral_sq_sub i]
      congr 1; ext ω; ring
    · have h := (hU.indep.indepFun hij).comp (measurable_id.sub_const pup)
        (measurable_id.sub_const pup)
      have h2 := h.integral_fun_mul_eq_mul_integral Measurable.of_discrete.aestronglyMeasurable
        Measurable.of_discrete.aestronglyMeasurable
      simp only [Function.comp_apply, id] at h2
      rw [h2, hUc i, zero_mul]
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_add Integrable.of_finite Integrable.of_finite,
    integral_finsetSum _ (fun i _ => Integrable.of_finite),
    integral_finsetSum _ (fun i _ => Integrable.of_finite)]
  have hT1 : ∀ i, ∫ w, ∑ j, ((x i w.1 - b i) * (x j w.1 - b j)) *
      ((U i w.2 - pup) * (U j w.2 - pup)) ∂(ν.prod π) =
        (∫ G, (x i G - b i) * (x i G - b i) ∂ν) * (pup * (1 - pup)) := by
    intro i
    rw [integral_finsetSum _ (fun j _ => Integrable.of_finite)]
    rw [Finset.sum_eq_single i]
    · rw [integral_prod_mul (fun G => (x i G - b i) * (x i G - b i))
        (fun ω => (U i ω - pup) * (U i ω - pup)), hUU, ite_eq_left rfl]
    · intro j _ hji
      rw [integral_prod_mul (fun G => (x i G - b i) * (x j G - b j))
        (fun ω => (U i ω - pup) * (U j ω - pup)), hUU, ite_eq_right (Ne.symm hji), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hT2 : ∀ i, ∫ w, (2 * (pup * (f w.1 - Ef)) * (x i w.1 - b i)) * (U i w.2 - pup)
      ∂(ν.prod π) = 0 := by
    intro i
    rw [integral_prod_mul (fun G => 2 * (pup * (f G - Ef)) * (x i G - b i))
      (fun ω => U i ω - pup), hUc i, mul_zero]
  have hT3 : ∫ w, pup ^ 2 * (f w.1 - Ef) ^ 2 ∂(ν.prod π) = pup ^ 2 * gnpVar m p f := by
    rw [lazyDayOneAux_integral_fst ν π (fun G => pup ^ 2 * (f G - Ef) ^ 2), integral_const_mul]
    unfold gnpVar
    rw [variance_eq_integral Measurable.of_discrete.aemeasurable]
  simp_rw [hT1, hT2, hT3]
  simp only [Finset.sum_const_zero, add_zero]
  have hz : ∀ i, ∫ G, (x i G - b i) * (x i G - b i) ∂ν ≤ 1 := by
    intro i
    calc ∫ G, (x i G - b i) * (x i G - b i) ∂ν ≤ ∫ G, (1 : ℝ) ∂ν := by
          refine integral_mono Integrable.of_finite (integrable_const _) fun G => ?_
          obtain ⟨h1, h2⟩ := lazyDayOneAux_ind_mem (majorityStep G B') i
          obtain ⟨h3, h4⟩ := lazyDayOneAux_ind_mem B' i
          simp only [x, b]
          nlinarith
      _ = 1 := by simp
  have hpq : pup * (1 - pup) ≤ 1 / 4 := by nlinarith [sq_nonneg (pup - 1 / 2)]
  have hpq0 : 0 ≤ pup * (1 - pup) := mul_nonneg hpup0 (by linarith)
  have hsum : ∑ i, (∫ G, (x i G - b i) * (x i G - b i) ∂ν) * (pup * (1 - pup)) ≤ m / 4 := by
    calc ∑ i, (∫ G, (x i G - b i) * (x i G - b i) ∂ν) * (pup * (1 - pup))
        ≤ ∑ _i : Fin m, (1 : ℝ) * (1 / 4) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul (hz i) hpq hpq0 zero_le_one
      _ = m / 4 := by simp; ring
  linarith

/-- Chebyshev's inequality for `|B|` on `G(m, p) ⊗ Bernoulli(p_up)^n` (the paper's
(day1-lazy-pf-bound-final)), written as an average over the update coins of probabilities under
`G(m, p)`. -/
private lemma lazyDayOneAux_cheb {n m : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (B' : Set (Fin m)) (p : ℝ) {pup : ℝ} (hpup0 : 0 ≤ pup) (hpup1 : pup ≤ 1) {t : ℝ}
    (ht : (1 - pup) * B'.ncard + pup * gnpExp m p (fun G => ((blueAfter G B' 1).ncard : ℝ)) < t) :
    ∑ u, (lazyDayOneAux_coins n pup).real {u} *
        gnpProb m p (fun G => t ≤ lazyDayOneAux_X e B' G u) ≤
      (m / 4 + pup ^ 2 * gnpVar m p (fun G => ((blueAfter G B' 1).ncard : ℝ))) /
        (t - ((1 - pup) * B'.ncard +
          pup * gnpExp m p (fun G => ((blueAfter G B' 1).ncard : ℝ)))) ^ 2 := by
  have hsum := lazyDayOneAux_prod_real_eq_sum (SimpleGraph.binomialRandom (Fin m) (toUnit p))
    (lazyDayOneAux_coins n pup) PowerOfFew.measurableSet_simpleGraph
    (fun G u => t ≤ lazyDayOneAux_X e B' G u)
  unfold gnpProb
  rw [← hsum]
  have hE := lazyDayOneAux_exp e he B' p hpup0 hpup1
  have hV := lazyDayOneAux_var e he B' p hpup0 hpup1
  rw [← hE] at ht ⊢
  calc _ ≤ _ := measureReal_ge_le_variance_div_sq MemLp.of_discrete ht
    _ ≤ _ := by gcongr

end Moments

/-! ### The paper's arithmetic -/

/-- `q = √(n/(p p_ac))`, `r = √(p p_ac n)` and `s = √(p_ac n)` satisfy `r q = n`, `r = p p_ac q`
and `s = √p p_ac q`. -/
private lemma lazyDayOneAux_sqrt_ids {n p pac : ℝ} (hn : 0 < n) (hp0 : 0 < p) (hpac0 : 0 < pac) :
    Real.sqrt (p * pac * n) * Real.sqrt (n / (p * pac)) = n ∧
    Real.sqrt (p * pac * n) = p * pac * Real.sqrt (n / (p * pac)) ∧
    Real.sqrt (pac * n) = Real.sqrt p * pac * Real.sqrt (n / (p * pac)) := by
  have hp0' : p ≠ 0 := hp0.ne'
  have hpac0' : pac ≠ 0 := hpac0.ne'
  have hq2 : Real.sqrt (n / (p * pac)) ^ 2 = n / (p * pac) := Real.sq_sqrt (by positivity)
  have hr2 : Real.sqrt (p * pac * n) ^ 2 = p * pac * n := Real.sq_sqrt (by positivity)
  have hs2 : Real.sqrt (pac * n) ^ 2 = pac * n := Real.sq_sqrt (by positivity)
  have hsp2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  refine ⟨?_, ?_, ?_⟩
  · refine (pow_left_inj₀ (by positivity) hn.le two_ne_zero).1 ?_
    rw [mul_pow, hr2, hq2]; field_simp
  · refine (pow_left_inj₀ (Real.sqrt_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [hr2, mul_pow, hq2]; field_simp
  · refine (pow_left_inj₀ (Real.sqrt_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [hs2, mul_pow, mul_pow, hsp2, hq2]; field_simp

/-- The paper's (day1-lazy-pf-m-bound) and its bound on `Δ'`: for good activations,
`m = |A ∩ B₀| + |A ∩ R₀|` satisfies `m ≥ 0.8 p_ac n` and `m ≤ p_ac n + 2 C_ε √(p_ac n)`, and
`Δ' = m/2 − |A ∩ B₀| ≥ p_ac Δ − C_ε √(p_ac n) ≥ p_ac Δ / 2` (using (day1-lazy-pf-bound-adv)). -/
private lemma lazyDayOneAux_counts {n pac C s nB kB kR Δ : ℝ} (hC : 0 ≤ C) (hs0 : 0 ≤ s)
    (hs2 : s ^ 2 = pac * n) (hpac_n : 100 * C ^ 2 ≤ pac * n) (hΔ : Δ = n / 2 - nB)
    (hΔs : 4 * C * s ≤ pac * Δ)
    (hkB_lo : pac * nB - C * s ≤ kB) (hkB_hi : kB ≤ pac * nB + C * s)
    (hkR_lo : pac * (n - nB) - C * s ≤ kR) (hkR_hi : kR ≤ pac * (n - nB) + C * s) :
    0.8 * (pac * n) ≤ kB + kR ∧ kB + kR ≤ pac * n + 2 * C * s ∧
      pac * Δ / 2 ≤ (kB + kR) / 2 - kB := by
  have hsC : 10 * C ≤ s := by nlinarith
  have h2 : 2 * C * s ≤ 0.2 * (pac * n) := by
    nlinarith [mul_le_mul_of_nonneg_right hsC hs0]
  have hpacΔ : pac * Δ = pac * n / 2 - pac * nB := by rw [hΔ]; ring
  have hCs : 0 ≤ C * s := mul_nonneg hC hs0
  refine ⟨by linarith, by linarith, by linarith⟩

/-- The hypotheses of Proposition 2.2 on the active subgraph, with `c = 2`: `2 ≤ p Δ'` (from
`p p_up p_ac² Δ ≥ M_K ≥ 2c`) and `2 ≤ √(p (1 − p) m)` (from `m ≥ 0.8 p_ac n`,
`(1 − p) p_ac n ≥ 10` and `p p_ac n ≥ 10`). -/
private lemma lazyDayOneAux_hyps22 {n p pac pup m Δ Δ' : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpac0 : 0 < pac) (hpac1 : pac ≤ 1) (hpup1 : pup ≤ 1)
    (hm08 : 0.8 * (pac * n) ≤ m) (h10 : 10 ≤ (1 - p) * pac * n) (hpn : 10 ≤ p * pac * n)
    (hΔpos : 0 < Δ) (hΔ' : pac * Δ / 2 ≤ Δ') (hM : 4 ≤ p * pup * pac ^ 2 * Δ) :
    2 ≤ p * Δ' ∧ 2 ≤ Real.sqrt (p * (1 - p) * m) := by
  have hpacn : 0 ≤ pac * n := by nlinarith
  have hm0 : 0 ≤ m := le_trans (by positivity) hm08
  constructor
  · have h1 : pup * pac ≤ 1 := by nlinarith
    have h2 : 0 ≤ p * (pac * Δ) := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    have h4 : p * (pac * Δ / 2) ≤ p * Δ' := mul_le_mul_of_nonneg_left hΔ' hp0.le
    nlinarith
  · rw [Real.le_sqrt (by norm_num) (mul_nonneg (mul_nonneg hp0.le (by linarith)) hm0)]
    rcases le_or_gt (1 / 2) p with hp2 | hp2
    · -- `p ≥ 1/2`: `p (1 − p) m ≥ (1 − p) m / 2 ≥ 0.4 (1 − p) p_ac n ≥ 4`
      have h1 : 0 ≤ (p - 1 / 2) * ((1 - p) * m) :=
        mul_nonneg (by linarith) (mul_nonneg (by linarith) hm0)
      have h2 : (1 - p) * (0.8 * (pac * n)) ≤ (1 - p) * m :=
        mul_le_mul_of_nonneg_left hm08 (by linarith)
      nlinarith
    · -- `p < 1/2`: `p (1 − p) m ≥ p m / 2 ≥ 0.4 p p_ac n ≥ 4`
      have h1 : 0 ≤ p * m * (1 / 2 - p) := mul_nonneg (mul_nonneg hp0.le hm0) (by linarith)
      have h2 : p * (0.8 * (pac * n)) ≤ p * m := mul_le_mul_of_nonneg_left hm08 hp0.le
      nlinarith

/-- `m min{m, pΔ'²} ≤ min{m, Δ' √(pm)}²`. -/
private lemma lazyDayOneAux_min_sq {m p Δ' : ℝ} (hm : 0 ≤ m) (hp : 0 ≤ p) :
    m * min m (p * Δ' ^ 2) ≤ (min m (Δ' * Real.sqrt (p * m))) ^ 2 := by
  rcases min_cases m (Δ' * Real.sqrt (p * m)) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    calc m * min m (p * Δ' ^ 2) ≤ m * m := mul_le_mul_of_nonneg_left (min_le_left _ _) hm
      _ = m ^ 2 := (sq m).symm
  · rw [h, mul_pow, Real.sq_sqrt (mul_nonneg hp hm)]
    calc m * min m (p * Δ' ^ 2) ≤ m * (p * Δ' ^ 2) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hm
      _ = Δ' ^ 2 * (p * m) := by ring

/-- `p_up² min{m, pΔ'²} ≥ 32/(ε D₂²)`: `p_up² m ≥ 0.8 p_up² p_ac n` (`n` large) and
`p_up² p Δ'² ≥ (p^(1/2) p_up p_ac Δ)² / 4 ≥ T_ε² / 4`. -/
private lemma lazyDayOneAux_min_bound {n p pac pup ε D₂ m Δ Δ' : ℝ} (hp0 : 0 < p)
    (hε0 : 0 < ε) (hD₂ : 0 < D₂) (hpac0 : 0 < pac) (hΔpos : 0 < Δ)
    (hm08 : 0.8 * (pac * n) ≤ m) (hn4 : 128 / (ε * D₂ ^ 2) ≤ pup ^ 2 * (pac * n))
    (hΔ' : pac * Δ / 2 ≤ Δ') (hT : 12 / (D₂ * Real.sqrt ε) ≤ Real.sqrt p * pup * pac * Δ) :
    32 / (ε * D₂ ^ 2) ≤ pup ^ 2 * min m (p * Δ' ^ 2) := by
  rw [mul_min_of_nonneg _ _ (sq_nonneg pup)]
  refine le_min ?_ ?_
  · have h1 : pup ^ 2 * (0.8 * (pac * n)) ≤ pup ^ 2 * m :=
      mul_le_mul_of_nonneg_left hm08 (sq_nonneg _)
    have h2 : 32 / (ε * D₂ ^ 2) = 0.25 * (128 / (ε * D₂ ^ 2)) := by ring
    have h3 : 0 ≤ 128 / (ε * D₂ ^ 2) := by positivity
    nlinarith
  · have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε0
    have hY2 : (12 / (D₂ * Real.sqrt ε)) ^ 2 ≤ (Real.sqrt p * pup * pac * Δ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hT 2
    have h144 : (12 / (D₂ * Real.sqrt ε)) ^ 2 = 144 / (ε * D₂ ^ 2) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hε0.le]; ring
    have hYsq : (Real.sqrt p * pup * pac * Δ) ^ 2 = p * (pup ^ 2 * (pac * Δ) ^ 2) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hp0.le]; ring
    have hΔ'2 : (pac * Δ / 2) ^ 2 ≤ Δ' ^ 2 := pow_le_pow_left₀ (by positivity) hΔ' 2
    have h3 : pup ^ 2 * (p * (pac * Δ / 2) ^ 2) ≤ pup ^ 2 * (p * Δ' ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΔ'2 hp0.le) (sq_nonneg _)
    have h4 : 32 / (ε * D₂ ^ 2) ≤ 144 / (ε * D₂ ^ 2) / 4 := by
      rw [show 144 / (ε * D₂ ^ 2) / 4 = 36 / (ε * D₂ ^ 2) by ring]
      gcongr; norm_num
    nlinarith

/-- The right side of the paper's (day1-lazy-pf-bound-final) is at most `ε/2`: for `m ≥ 3`,
`varConst m p ≤ 2.76`, so `m/4 + p_up² Var|H| ≤ 4m`, while
`(t − E|B|)² ≥ (p_up D μ₀)² ≥ D² m p_up² min{m, pΔ'²} ≥ 8m/ε`. -/
private lemma lazyDayOneAux_ratio {m : ℕ} {p pup ε D₂ Δ' μ₀ V den : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hpup0 : 0 < pup) (hpup1 : pup ≤ 1) (hε0 : 0 < ε)
    (hD₂ : 0 < D₂) (hm3 : (3 : ℝ) ≤ m) (hV : V ≤ varConst m p * m) (hμ₀ : 0 < μ₀)
    (hden : pup * (D₂ / 2) * μ₀ ≤ den)
    (hμ₀sq : (m : ℝ) * min (m : ℝ) (p * Δ' ^ 2) ≤ μ₀ ^ 2)
    (hmin : 32 / (ε * D₂ ^ 2) ≤ pup ^ 2 * min (m : ℝ) (p * Δ' ^ 2)) :
    ((m : ℝ) / 4 + pup ^ 2 * V) / den ^ 2 ≤ ε / 2 := by
  have hσ0 : 0 ≤ p * (1 - p) := mul_nonneg hp0.le (by linarith)
  have hσ1 : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have h1 : (1 - 2 * (p * (1 - p))) ^ 2 ≤ 1 := by nlinarith
  have h2 : ((m : ℝ) - 1) / ((m : ℝ) - 2) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have h3 : 0 ≤ ((m : ℝ) - 1) / ((m : ℝ) - 2) := div_nonneg (by linarith) (by linarith)
  have h4 : (1 - 2 * (p * (1 - p))) ^ 2 * (((m : ℝ) - 1) / ((m : ℝ) - 2)) ≤ 1 * 2 :=
    mul_le_mul h1 h2 h3 zero_le_one
  have h5 : 0 ≤ (1 - 2 * (p * (1 - p))) ^ 2 * (((m : ℝ) - 1) / ((m : ℝ) - 2)) :=
    mul_nonneg (sq_nonneg _) h3
  have hvc : varConst m p ≤ 2.76 := by
    unfold varConst; nlinarith
  have hvc0 : 0 ≤ varConst m p := by
    unfold varConst; nlinarith
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hVB : (m : ℝ) / 4 + pup ^ 2 * V ≤ 4 * m := by
    have e1 : pup ^ 2 * V ≤ pup ^ 2 * (varConst m p * m) :=
      mul_le_mul_of_nonneg_left hV (sq_nonneg _)
    have e2 : pup ^ 2 * (varConst m p * m) ≤ varConst m p * m :=
      mul_le_of_le_one_left (mul_nonneg hvc0 hm0) (by nlinarith)
    have e3 : varConst m p * m ≤ 2.76 * m := mul_le_mul_of_nonneg_right hvc hm0
    linarith
  have hpos : 0 < pup * (D₂ / 2) * μ₀ := by positivity
  have hden2 : (pup * (D₂ / 2) * μ₀) ^ 2 ≤ den ^ 2 := pow_le_pow_left₀ hpos.le hden 2
  have hkey : 4 * (m : ℝ) ≤ ε / 2 * (pup * (D₂ / 2) * μ₀) ^ 2 := by
    have e1 : (pup * (D₂ / 2) * μ₀) ^ 2 = D₂ ^ 2 / 4 * (pup ^ 2 * μ₀ ^ 2) := by ring
    have e2 : pup ^ 2 * ((m : ℝ) * min (m : ℝ) (p * Δ' ^ 2)) ≤ pup ^ 2 * μ₀ ^ 2 :=
      mul_le_mul_of_nonneg_left hμ₀sq (sq_nonneg _)
    have e3 : (m : ℝ) * (32 / (ε * D₂ ^ 2)) ≤ (m : ℝ) * (pup ^ 2 * min (m : ℝ) (p * Δ' ^ 2)) :=
      mul_le_mul_of_nonneg_left hmin hm0
    have e4 : ε / 2 * (D₂ ^ 2 / 4 * ((m : ℝ) * (32 / (ε * D₂ ^ 2)))) = 4 * m := by
      field_simp; ring
    have e5 : (m : ℝ) * (32 / (ε * D₂ ^ 2)) ≤ pup ^ 2 * μ₀ ^ 2 := by nlinarith
    rw [e1, ← e4]
    gcongr
  have hden0 : 0 < den ^ 2 := by have := lt_of_lt_of_le hpos hden; positivity
  rw [div_le_iff₀ hden0]
  nlinarith [mul_le_mul_of_nonneg_left hden2 (by positivity : (0 : ℝ) ≤ ε / 2)]

/-- The paper's final arithmetic: `|B₀| − |A ∩ B₀| + t ≤ n/2 − K √(n/(p p_ac))`, where
`t = m/2 − p_up D min{m, Δ' √(pm)}`. The key step is the paper's
`D p_up min{m, p_ac Δ √(pm)/2} ≥ (D/4) min{p_up p_ac^(3/2) √(pn), p p_up p_ac² Δ} √(n/(p p_ac))
≥ (K + 3 C_ε p_ac √p) √(n/(p p_ac))`. -/
private lemma lazyDayOneAux_final {n p pac pup K C D q r s nB kB m Δ Δ' : ℝ}
    (hp0 : 0 < p) (hpac0 : 0 < pac) (hpac1 : pac ≤ 1) (hpup0 : 0 < pup) (hD : 0 < D)
    (hC : 0 < C) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hrq : r * q = n) (hrpq : r = p * pac * q) (hspq : s = Real.sqrt p * pac * q)
    (hsp1 : Real.sqrt p ≤ 1)
    (hKr : K + 3 * C ≤ D / 4 * pup * pac * r)
    (hM : 8 * K / D ≤ p * pup * pac ^ 2 * Δ)
    (hT : 24 * C / D ≤ Real.sqrt p * pup * pac * Δ)
    (hΔ : Δ = n / 2 - nB)
    (hm_lo : pac * n / 4 ≤ m) (hm_hi : m ≤ pac * n + 2 * C * s)
    (hkB_lo : pac * nB - C * s ≤ kB)
    (hΔ' : pac * Δ / 2 ≤ Δ') (hΔpos : 0 < Δ)
    (hsqrtpm : r / 2 ≤ Real.sqrt (p * m)) :
    nB - kB + (m / 2 - pup * D * min m (Δ' * Real.sqrt (p * m))) ≤ n / 2 - K * q := by
  have hs0 : 0 ≤ s := by rw [hspq]; positivity
  -- `p_up D μ₀ ≥ (K + 3 C_ε p_ac √p) q = K q + 3 C_ε s`
  have hKq : K * q + 3 * C * s ≤ pup * D * min m (Δ' * Real.sqrt (p * m)) := by
    have hsq : s ≤ q := by
      rw [hspq]
      have : Real.sqrt p * pac ≤ 1 := by
        have := Real.sqrt_nonneg p; nlinarith
      nlinarith
    have hA1 : K * q + 3 * C * s ≤ pup * D * m := by
      have h1 : pup * D * (pac * n / 4) ≤ pup * D * m :=
        mul_le_mul_of_nonneg_left hm_lo (by positivity)
      have h2 : pup * D * (pac * n / 4) = (D / 4 * pup * pac * r) * q := by rw [← hrq]; ring
      have h3 : (K + 3 * C) * q ≤ (D / 4 * pup * pac * r) * q :=
        mul_le_mul_of_nonneg_right hKr hq0
      have h4 : 3 * C * s ≤ 3 * C * q := mul_le_mul_of_nonneg_left hsq (by positivity)
      linarith
    have hA2 : K * q + 3 * C * s ≤ pup * D * (Δ' * Real.sqrt (p * m)) := by
      have hpacΔ : 0 ≤ pac * Δ / 2 := by positivity
      have h1 : pac * Δ / 2 * (r / 2) ≤ Δ' * Real.sqrt (p * m) :=
        mul_le_mul hΔ' hsqrtpm (by positivity) (le_trans hpacΔ hΔ')
      have h2 : pup * D * (pac * Δ / 2 * (r / 2)) = (D / 4 * (p * pup * pac ^ 2 * Δ)) * q := by
        rw [hrpq]; ring
      have h3 : K + 3 * C * (Real.sqrt p * pac) ≤ D / 4 * (p * pup * pac ^ 2 * Δ) := by
        rw [div_le_iff₀ hD] at hM hT
        have e1 : Real.sqrt p * pac * (24 * C) ≤
            Real.sqrt p * pac * (Real.sqrt p * pup * pac * Δ * D) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
        have e2 : Real.sqrt p * pac * (Real.sqrt p * pup * pac * Δ * D) =
            p * pup * pac ^ 2 * Δ * D := by
          have := Real.mul_self_sqrt hp0.le
          calc Real.sqrt p * pac * (Real.sqrt p * pup * pac * Δ * D)
              = (Real.sqrt p * Real.sqrt p) * pup * pac ^ 2 * Δ * D := by ring
            _ = p * pup * pac ^ 2 * Δ * D := by rw [this]
        linarith
      have h4 : 3 * C * s = 3 * C * (Real.sqrt p * pac) * q := by rw [hspq]; ring
      have h5 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ pup * D)
      have h6 := mul_le_mul_of_nonneg_right h3 hq0
      linarith
    rcases min_cases m (Δ' * Real.sqrt (p * m)) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact hA1
    · rw [h]; exact hA2
  have h1 : (1 - pac) * nB ≤ (1 - pac) * (n / 2) :=
    mul_le_mul_of_nonneg_left (by linarith [mul_pos hpac0 hΔpos]) (by linarith)
  have hCs : 0 ≤ C * s := mul_nonneg hC.le hs0
  linarith

/-! ### Proposition 4.2 -/

/-- The paper's Steps 1.1–1.3 for fixed good activations `a` (the active set `A = {a = true}`):
with probability at least `1 − ε/2` over the graph and the update coins,
`|B₁| ≤ n/2 − K √(n/(p p_ac))`. Proposition 2.2 is applied to the active subgraph with `c = 2`. -/
private lemma lazyDayOneAux_good (hBE : ShevtsovaBerryEsseen) {n : ℕ} {p pac pup ε K C : ℝ}
    {B₀ : Set (Fin n)} (a : Fin n → Bool)
    (hp0 : 0 < p) (hp1 : p < 1) (hpac0 : 0 < pac) (hpac1 : pac ≤ 1) (hpup0 : 0 < pup)
    (hpup1 : pup ≤ 1) (hε0 : 0 < ε) (hC : 0 < C) (hnpos : (0 : ℝ) < n)
    (hpac_n : 100 * C ^ 2 ≤ pac * n) (hpacn4 : 4 ≤ pac * n) (h10 : 10 ≤ (1 - p) * pac * n)
    (hpn : 10 ≤ p * pac * n) (hn4 : 128 / (ε * Dc 2 ^ 2) ≤ pup ^ 2 * (pac * n))
    (hKr : K + 3 * C ≤ Dc 2 / 2 / 4 * pup * pac * Real.sqrt (p * pac * n))
    (hS : 4 * C * Real.sqrt (pac * n) ≤ pac * ((n : ℝ) / 2 - B₀.ncard))
    (hM : max (8 * K / (Dc 2 / 2)) 4 ≤ p * pup * pac ^ 2 * ((n : ℝ) / 2 - B₀.ncard))
    (hT : max (24 * C / (Dc 2 / 2)) (12 / (Dc 2 * Real.sqrt ε)) ≤
      Real.sqrt p * pup * pac * ((n : ℝ) / 2 - B₀.ncard))
    (hgB : |((B₀ ∩ {v | a v = true}).ncard : ℝ) - pac * B₀.ncard| ≤
      C * Real.sqrt (pac * B₀.ncard))
    (hgR : |((B₀ᶜ ∩ {v | a v = true}).ncard : ℝ) - pac * (B₀ᶜ.ncard : ℝ)| ≤
      C * Real.sqrt (pac * (B₀ᶜ.ncard : ℝ))) :
    ∑ u, (lazyDayOneAux_coins n pup).real {u} *
      gnpProb n p (fun G => ¬ ((lazyStep G {v | a v = true} {v | u v = true} B₀).ncard : ℝ) ≤
        n / 2 - K * Real.sqrt (n / (p * pac))) ≤ ε / 2 := by
  classical
  have hD₂ : 0 < Dc 2 := lazyDayOneAux_Dc_two_pos
  obtain ⟨hrq, hrpq, hspq⟩ := lazyDayOneAux_sqrt_ids hnpos hp0 hpac0
  set D₂ := Dc 2 with hD₂_def
  set D := D₂ / 2 with hD_def
  have hD : 0 < D := by positivity
  set q := Real.sqrt (n / (p * pac)) with hq_def
  set r := Real.sqrt (p * pac * n) with hr_def
  set s := Real.sqrt (pac * n) with hs_def
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = pac * n := Real.sq_sqrt (by positivity)
  have hr2 : r ^ 2 = p * pac * n := Real.sq_sqrt (by positivity)
  have hsp1 : Real.sqrt p ≤ 1 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hp1.le
  set nB : ℝ := (B₀.ncard : ℝ) with hnB_def
  set Δ : ℝ := (n : ℝ) / 2 - nB with hΔ_def
  have hΔpos : 0 < Δ := by
    have h1 : 0 < pac * Δ := lt_of_lt_of_le (by positivity) hS
    exact (mul_pos_iff_of_pos_left hpac0).1 h1
  -- the active set `A`, `m = |A|`, `|A ∩ B₀|`, `|A ∩ R₀|`
  set A : Set (Fin n) := {v | a v = true} with hA_def
  set kB : ℝ := ((B₀ ∩ A).ncard : ℝ) with hkB_def
  set kR : ℝ := ((B₀ᶜ ∩ A).ncard : ℝ) with hkR_def
  have hnR : ((B₀ᶜ).ncard : ℝ) = n - nB := by
    have h := Set.ncard_add_ncard_compl B₀
    rw [Nat.card_fin] at h
    have h' : ((B₀.ncard + B₀ᶜ.ncard : ℕ) : ℝ) = n := by exact_mod_cast h
    push_cast at h'
    linarith
  rw [hnR] at hgR
  have hm : (A.ncard : ℝ) = kB + kR := by
    have h := Set.ncard_inter_add_ncard_sdiff_eq_ncard A B₀ (Set.toFinite A)
    rw [Set.inter_comm A B₀, Set.sdiff_eq, Set.inter_comm A B₀ᶜ] at h
    rw [hkB_def, hkR_def]
    exact_mod_cast h.symm
  have hnB0 : 0 ≤ nB := Nat.cast_nonneg _
  have hnBn : nB ≤ n := by
    have := Nat.cast_nonneg (α := ℝ) (B₀ᶜ.ncard); linarith
  have hsB : Real.sqrt (pac * nB) ≤ s :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hnBn hpac0.le)
  have hsR : Real.sqrt (pac * (n - nB)) ≤ s :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith) hpac0.le)
  obtain ⟨hkB1, hkB2⟩ := abs_le.1 hgB
  obtain ⟨hkR1, hkR2⟩ := abs_le.1 hgR
  have hCsB := mul_le_mul_of_nonneg_left hsB hC.le
  have hCsR := mul_le_mul_of_nonneg_left hsR hC.le
  have hkB_lo : pac * nB - C * s ≤ kB := by linarith only [hkB1, hCsB]
  have hkB_hi : kB ≤ pac * nB + C * s := by linarith only [hkB2, hCsB]
  have hkR_lo : pac * (n - nB) - C * s ≤ kR := by linarith only [hkR1, hCsR]
  have hkR_hi : kR ≤ pac * (n - nB) + C * s := by linarith only [hkR2, hCsR]
  obtain ⟨hm08, hm_hi, hΔ'⟩ := lazyDayOneAux_counts hC.le hs0 hs2 hpac_n hΔ_def hS hkB_lo
    hkB_hi hkR_lo hkR_hi
  rw [← hm] at hm08 hm_hi hΔ'
  set Δ' : ℝ := (A.ncard : ℝ) / 2 - kB with hΔ'_def
  have hm3 : (3 : ℝ) ≤ A.ncard := by linarith only [hm08, hpacn4]
  have hmpos : (0 : ℝ) < A.ncard := by linarith only [hm3]
  have hΔ'pos : 0 < Δ' := by
    have := mul_pos hpac0 hΔpos; linarith only [hΔ', this]
  obtain ⟨hcΔ, hcn⟩ := lazyDayOneAux_hyps22 hp0 hp1 hpac0 hpac1 hpup1 hm08 h10 hpn
    hΔpos hΔ' (le_trans (le_max_right _ _) hM)
  -- Proposition 2.2 on the active subgraph `G[A] ∼ G(m, p)`, with `c = 2`
  set B' : Set (Fin A.ncard) := enumSet A ⁻¹' B₀ with hB'_def
  have hB'card : (B'.ncard : ℝ) = kB := by
    rw [hB'_def, ncard_preimage_enumSet, Set.inter_comm]
  obtain ⟨hExp, hVar⟩ := proposition2_2 hBE hp0 hp1 (by norm_num) hD₂ hcΔ hcn (B₀ := B')
    (le_of_eq (by rw [hB'card, hΔ'_def]; ring))
  -- the threshold `t = m/2 − p_up D min{m, Δ' √(pm)}` of (day1-lazy-pf-bound-final)
  set μ₀ : ℝ := min (A.ncard : ℝ) (Δ' * Real.sqrt (p * A.ncard)) with hμ₀_def
  have hsqrtpm : r / 2 ≤ Real.sqrt (p * A.ncard) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have : p * (0.8 * (pac * n)) ≤ p * A.ncard := mul_le_mul_of_nonneg_left hm08 hp0.le
    nlinarith only [this, hr2]
  have hμ₀pos : 0 < μ₀ :=
    lt_min hmpos (mul_pos hΔ'pos (Real.sqrt_pos.2 (by positivity)))
  set t : ℝ := (A.ncard : ℝ) / 2 - pup * D * μ₀ with ht_def
  set EX : ℝ := (1 - pup) * B'.ncard +
    pup * gnpExp A.ncard p (fun G => ((blueAfter G B' 1).ncard : ℝ)) with hEX_def
  -- (lazy-b1-exp): `E|B| ≤ m/2 − p_up D_c μ₀`, so `t − E|B| ≥ p_up D μ₀`
  have htEX : pup * D * μ₀ ≤ t - EX := by
    have h1 := mul_le_mul_of_nonneg_left hExp hpup0.le
    have h2 : 0 ≤ (1 - pup) * Δ' := mul_nonneg (by linarith) hΔ'pos.le
    have h3 : pup * D₂ * μ₀ = 2 * (pup * D * μ₀) := by rw [hD_def]; ring
    have h4 : (1 - pup) * kB = (1 - pup) * ((A.ncard : ℝ) / 2) - (1 - pup) * Δ' := by
      rw [hΔ'_def]; ring
    rw [ht_def, hEX_def, hB'card]
    linarith only [h1, h2, h3, h4]
  have hEXt : EX < t := by
    have : 0 < pup * D * μ₀ := by positivity
    linarith only [htEX, this]
  have hcheb := lazyDayOneAux_cheb (enumSet A) (enumSet A).injective B' p hpup0.le hpup1 hEXt
  -- the deterministic step: `|B₁| = |B₀| − |A ∩ B₀| + |B|`, and `|B| < t` gives the bound
  have hfin : nB - kB + t ≤ n / 2 - K * q :=
    lazyDayOneAux_final hp0 hpac0 hpac1 hpup0 hD hC hq0 hr0 hrq hrpq hspq hsp1 hKr
      (le_trans (le_max_left _ _) hM) (le_trans (le_max_left _ _) hT) hΔ_def
      (by linarith only [hm08, hpacn4]) hm_hi hkB_lo hΔ' hΔpos hsqrtpm
  have hdet : ∀ u, gnpProb n p (fun G =>
      ¬ ((lazyStep G A {v | u v = true} B₀).ncard : ℝ) ≤ n / 2 - K * q) ≤
      gnpProb A.ncard p (fun G' => t ≤ lazyDayOneAux_X (enumSet A) B' G' u) := by
    intro u
    rw [← gnpProb_inducedOn A p (fun G' => t ≤ lazyDayOneAux_X (enumSet A) B' G' u)]
    refine gnpProb_mono fun G hG => ?_
    show t ≤ lazyDayOneAux_X (enumSet A) B' (inducedOn G A) u
    by_contra hlt
    push Not at hlt
    apply hG
    rw [lazyDayOneAux_ncard_lazyStep G A u B₀, Set.inter_comm A B₀, ← hnB_def, ← hkB_def,
      ← hB'_def]
    linarith only [hfin, hlt]
  calc ∑ u, (lazyDayOneAux_coins n pup).real {u} *
        gnpProb n p (fun G => ¬ ((lazyStep G A {v | u v = true} B₀).ncard : ℝ) ≤ n / 2 - K * q)
      ≤ ∑ u, (lazyDayOneAux_coins n pup).real {u} *
          gnpProb A.ncard p (fun G' => t ≤ lazyDayOneAux_X (enumSet A) B' G' u) :=
        Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hdet u) measureReal_nonneg
    _ ≤ _ := hcheb
    _ ≤ ε / 2 := lazyDayOneAux_ratio hp0 hp1 hpup0 hpup1 hε0 hD₂ hm3 hVar hμ₀pos htEX
        (lazyDayOneAux_min_sq hmpos.le hp0.le)
        (lazyDayOneAux_min_bound hp0 hε0 hD₂ hpac0 hΔpos hm08 hn4 hΔ'
          (le_trans (le_max_right _ _) hT))

/-- **Proposition 4.2** (`S:prop:day1-lazy`). In the setting of Theorem 4.1, for every
`ε ∈ (0, 1)` and `K > 0` there are `M_K`, `S_ε` and `T_ε` such that, when
`p_ac^(1/2) Δ ≥ S_ε n^(1/2)`, `p^(1/2) p_up p_ac Δ ≥ T_ε` and `p p_up p_ac² Δ ≥ M_K`, with
probability at least `1 − ε`, `|B₁| ≤ n/2 − K √(n / (p p_ac))`.

Readings: the paper writes "for every `ε ∈ (0, 1)` and `T > 0`", a misprint for `K > 0`; its proof
takes `n` large (`n ≥ N`) and uses `(1 − p) p_ac n ≥ 10` (module docstring).

Proof (Appendix B), with `c = 2` and `D = D_2/2`: `C_ε = 2/√ε`, `S_ε = 4 C_ε`,
`M_K = max{8K/D, 2c}`, `T_ε = max{24 C_ε/D, 12/(D_2 √ε)}` (the paper: `11 ε^(−1/2)`). Taking
`n ≥ N` ("`n` sufficiently large") gives `p_ac n ≥ 100 C_ε²` (so `m ≥ 0.8 p_ac n`),
`log n ≥ 10`, `(D/4) p_up p_ac √(p p_ac n) ≥ K + 3 C_ε` and `p_up² p_ac n ≥ 128/(ε D_2²)` (the
paper's `p_up² p_ac n ≥ (11 ε^(−1/2))²` also needs `n` large). Proposition 2.2 is applied to the
active subgraph; its variance bound `varConst m p · m` replaces the paper's covariance bound
`1/(3m)` (the same argument, packaged; `varConst ≤ 2.76` for `m ≥ 3`).

Departure from the paper: the paper takes `c = 10` (`D = 0.21`), which needs
`c ≤ √(p (1 − p) m)` for the `m ≈ p_ac n` active vertices, i.e. `p (1 − p) p_ac n ≳ 100`. Under the
hypotheses `(1 − p) p_ac n ≥ 10` and `p p_ac n ≥ (1 + λ) log n`, `p (1 − p) m` can be as small as
about `5` when `p` is close to `1`, so `c = 10` is not admissible there; the proof takes `c = 2`
(`p (1 − p) m ≥ 4` once `m ≥ 0.8 p_ac n` and `log n ≥ 10`), with `D_2 = Φ₀(3/2) − 0.28 > 0`. -/
theorem proposition4_2 (hBE : ShevtsovaBerryEsseen) :
    ∃ M S T : ℝ → ℝ, ∀ ε K lam pac pup : ℝ, 0 < ε → ε < 1 → 0 < K → 0 < lam → 0 < pac →
      pac ≤ 1 → 0 < pup → pup ≤ 1 →
      ∃ N : ℕ, ∀ n ≥ N, ∀ (p : ℝ) (B₀ : Set (Fin n)), 0 < p →
        (1 + lam) * Real.log n ≤ p * pac * n → 10 ≤ (1 - p) * pac * n →
        S ε * Real.sqrt n ≤ Real.sqrt pac * ((n : ℝ) / 2 - B₀.ncard) →
        T ε ≤ Real.sqrt p * pup * pac * ((n : ℝ) / 2 - B₀.ncard) →
        M K ≤ p * pup * pac ^ 2 * ((n : ℝ) / 2 - B₀.ncard) →
        1 - ε ≤ lazyProb n p pac pup (fun G c =>
          ((lazyBlueAfter G c B₀ 1).ncard : ℝ) ≤ n / 2 - K * Real.sqrt (n / (p * pac))) := by
  classical
  have hD₂ : 0 < Dc 2 := lazyDayOneAux_Dc_two_pos
  -- `c = 2`, `D = D₂/2`, `C_ε = 2/√ε`: `M_K = max{8K/D, 2c}`, `S_ε = 4 C_ε`,
  -- `T_ε = max{24 C_ε/D, 12/(D₂ √ε)}` (the paper's (day1-lazy-pf-bounds), (day1-lazy-pf-bound-adv))
  refine ⟨fun K => max (8 * K / (Dc 2 / 2)) 4, fun ε => 4 * (2 / Real.sqrt ε),
    fun ε => max (24 * (2 / Real.sqrt ε) / (Dc 2 / 2)) (12 / (Dc 2 * Real.sqrt ε)), ?_⟩
  intro ε K lam pac pup hε0 hε1 hK hlam hpac0 hpac1 hpup0 hpup1
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε0
  set C := 2 / Real.sqrt ε with hC_def
  have hC : 0 < C := by positivity
  have hC2 : C ^ 2 = 4 / ε := by rw [hC_def, div_pow, Real.sq_sqrt hε0.le]; norm_num
  -- the threshold `N` ("`n` sufficiently large")
  set L : ℝ := ((K + 3 * C) / (Dc 2 / 2 / 4 * pup * pac)) ^ 2 with hL
  set N₀ : ℝ := max (max (100 * C ^ 2 / pac) (Real.exp 10))
    (max (Real.exp L) (max (128 / (ε * Dc 2 ^ 2 * pup ^ 2 * pac)) (4 / pac))) with hN₀
  refine ⟨⌈N₀⌉₊, fun n hn p B₀ hp0 hlog h10 hS hT hM => ?_⟩
  have hnN : N₀ ≤ n := (Nat.le_ceil N₀).trans (by exact_mod_cast hn)
  have hn1 : 100 * C ^ 2 / pac ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hnN
  have hn2 : Real.exp 10 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hnN
  have hn3 : Real.exp L ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnN
  have hn4 : 128 / (ε * Dc 2 ^ 2 * pup ^ 2 * pac) ≤ n :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hnN
  have hn5 : 4 / pac ≤ n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hnN
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos 10) hn2
  have hlogn : 10 ≤ Real.log n := by
    rw [← Real.log_exp 10]; exact Real.log_le_log (Real.exp_pos 10) hn2
  have hlogL : L ≤ Real.log n := by
    rw [← Real.log_exp L]; exact Real.log_le_log (Real.exp_pos L) hn3
  have hlogpn : Real.log n ≤ p * pac * n := by
    have := mul_nonneg hlam.le (by linarith : (0 : ℝ) ≤ Real.log n)
    linarith only [hlog, this]
  have hpn : 10 ≤ p * pac * n := le_trans hlogn hlogpn
  have hp1 : p < 1 := by
    by_contra h
    push Not at h
    have : (1 - p) * pac * n ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) hpac0.le) hnpos.le
    linarith
  have hpac_n : 100 * C ^ 2 ≤ pac * n := by rw [div_le_iff₀ hpac0] at hn1; linarith only [hn1]
  have hpacn4 : 4 ≤ pac * n := by rw [div_le_iff₀ hpac0] at hn5; linarith only [hn5]
  have hn4' : 128 / (ε * Dc 2 ^ 2) ≤ pup ^ 2 * (pac * n) := by
    rw [div_le_iff₀ (by positivity)] at hn4 ⊢; linarith only [hn4]
  -- `(D/4) p_up p_ac √(p p_ac n) ≥ K + 3 C_ε` (`n` large: `p p_ac n ≥ log n ≥ L`)
  have hKr : K + 3 * C ≤ Dc 2 / 2 / 4 * pup * pac * Real.sqrt (p * pac * n) := by
    have h1 : Real.sqrt L ≤ Real.sqrt (p * pac * n) :=
      (Real.sqrt_le_sqrt hlogL).trans (Real.sqrt_le_sqrt hlogpn)
    have h2 : Real.sqrt L = (K + 3 * C) / (Dc 2 / 2 / 4 * pup * pac) := by
      rw [hL]; exact Real.sqrt_sq (by positivity)
    rw [h2, div_le_iff₀ (by positivity)] at h1
    linarith only [h1]
  -- (day1-lazy-pf-bound-adv): `p_ac Δ ≥ 4 C_ε √(p_ac n)`
  have hS' : 4 * C * Real.sqrt (pac * n) ≤ pac * ((n : ℝ) / 2 - B₀.ncard) := by
    have hs' : Real.sqrt (pac * n) = Real.sqrt pac * Real.sqrt n := Real.sqrt_mul hpac0.le n
    have := mul_le_mul_of_nonneg_left hS (Real.sqrt_nonneg pac)
    calc 4 * C * Real.sqrt (pac * n) = Real.sqrt pac * (4 * C * Real.sqrt n) := by
          rw [hs']; ring
      _ ≤ Real.sqrt pac * (Real.sqrt pac * ((n : ℝ) / 2 - B₀.ncard)) := this
      _ = pac * ((n : ℝ) / 2 - B₀.ncard) := by rw [← mul_assoc, Real.mul_self_sqrt hpac0.le]
  -- the good activations: (day1-lazy-pf-bound-Vac)
  set bound : ℝ := (n : ℝ) / 2 - K * Real.sqrt (n / (p * pac)) with hbound
  let good : (Fin n → Bool) → Prop := fun a =>
    |((B₀ ∩ {v | a v = true}).ncard : ℝ) - pac * B₀.ncard| ≤ C * Real.sqrt (pac * B₀.ncard) ∧
    |((B₀ᶜ ∩ {v | a v = true}).ncard : ℝ) - pac * (B₀ᶜ.ncard : ℝ)| ≤
      C * Real.sqrt (pac * (B₀ᶜ.ncard : ℝ))
  -- bad activations have probability at most `ε/2`
  have hbad : lazyProb n p pac pup (fun _ c => ¬ good (c 0).1) ≤ ε / 2 := by
    refine lazyProb_le_of_forall_day 0 _ (fun G c c' h => by simp only [h 0 le_rfl])
      fun G c => ?_
    simp only [Function.update_self]
    calc (dayLaw n pac pup).real {d | ¬ good d.1}
        ≤ (dayLaw n pac pup).real
            ({d | C * Real.sqrt (pac * B₀.ncard) <
                |((B₀ ∩ {v | d.1 v = true}).ncard : ℝ) - pac * B₀.ncard|} ∪
             {d | C * Real.sqrt (pac * B₀ᶜ.ncard) <
                |((B₀ᶜ ∩ {v | d.1 v = true}).ncard : ℝ) - pac * B₀ᶜ.ncard|}) := by
          refine measureReal_mono (fun d hd => ?_) (measure_ne_top _ _)
          simp only [Set.mem_ofPred_eq, Set.mem_union] at hd ⊢
          by_contra h
          push Not at h
          exact hd ⟨h.1, h.2⟩
      _ ≤ 1 / C ^ 2 + 1 / C ^ 2 :=
          (measureReal_union_le _ _).trans
            (add_le_add (lazyDayOneAux_act_dev hpac0 hpac1 B₀ hC)
              (lazyDayOneAux_act_dev hpac0 hpac1 B₀ᶜ hC))
      _ = ε / 2 := by rw [hC2]; field_simp; ring
  -- good activations and a large `|B₁|` have probability at most `ε/2`
  have hgood : lazyProb n p pac pup (fun G c => good (c 0).1 ∧
      ¬ ((lazyBlueAfter G c B₀ 1).ncard : ℝ) ≤ bound) ≤ ε / 2 := by
    let Q : SimpleGraph (Fin n) → DayCoins n → Prop := fun G d => good d.1 ∧
      ¬ ((lazyStep G {v | d.1 v = true} {v | d.2 v = true} B₀).ncard : ℝ) ≤ bound
    have hQ : lazyProb n p pac pup (fun G c => good (c 0).1 ∧
        ¬ ((lazyBlueAfter G c B₀ 1).ncard : ℝ) ≤ bound) =
        lazyProb n p pac pup (fun G c => Q G (c 0)) := rfl
    rw [hQ, lazyProb_eq_of_day 0 Q, prod_dayLaw_real_eq_sum Q, Fintype.sum_prod_type]
    have hsplit : ∀ (a u : Fin n → Bool), (dayLaw n pac pup).real {(a, u)} =
        (lazyDayOneAux_coins n pac).real {a} * (lazyDayOneAux_coins n pup).real {u} :=
      fun a u => by rw [← Set.singleton_prod_singleton]; exact measureReal_prod_prod _ _
    simp_rw [hsplit, mul_assoc, ← Finset.mul_sum]
    have hinner : ∀ a, ∑ u, (lazyDayOneAux_coins n pup).real {u} *
        gnpProb n p (fun G => Q G (a, u)) ≤ ε / 2 := by
      intro a
      by_cases ha : good a
      swap
      · have h0 : ∀ u, gnpProb n p (fun G => Q G (a, u)) = 0 := fun u => by
          have : (fun G => Q G (a, u)) = fun _ => False := by
            funext G; exact propext ⟨fun h => ha h.1, False.elim⟩
          rw [this]; simp [gnpProb]
        simp only [h0, mul_zero, Finset.sum_const_zero]; positivity
      calc ∑ u, (lazyDayOneAux_coins n pup).real {u} * gnpProb n p (fun G => Q G (a, u))
          ≤ ∑ u, (lazyDayOneAux_coins n pup).real {u} * gnpProb n p (fun G =>
              ¬ ((lazyStep G {v | a v = true} {v | u v = true} B₀).ncard : ℝ) ≤
                n / 2 - K * Real.sqrt (n / (p * pac))) :=
            Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left
              (gnpProb_mono fun G h => h.2) measureReal_nonneg
        _ ≤ ε / 2 := lazyDayOneAux_good hBE a hp0 hp1 hpac0 hpac1 hpup0 hpup1 hε0 hC hnpos
            hpac_n hpacn4 h10 hpn hn4' hKr hS' hM hT ha.1 ha.2
    calc ∑ a, (lazyDayOneAux_coins n pac).real {a} * ∑ u,
          (lazyDayOneAux_coins n pup).real {u} * gnpProb n p (fun G => Q G (a, u))
        ≤ ∑ a, (lazyDayOneAux_coins n pac).real {a} * (ε / 2) :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hinner a) measureReal_nonneg
      _ = ε / 2 := by
          rw [← Finset.sum_mul, sum_measureReal_singleton, Finset.coe_univ, probReal_univ,
            one_mul]
  -- the union of the two events (the paper's last sentence)
  apply le_lazyProb_of_not_le
  calc lazyProb n p pac pup (fun G c => ¬ ((lazyBlueAfter G c B₀ 1).ncard : ℝ) ≤ bound)
      ≤ lazyProb n p pac pup (fun G c => ¬ good (c 0).1 ∨
          (good (c 0).1 ∧ ¬ ((lazyBlueAfter G c B₀ 1).ncard : ℝ) ≤ bound)) :=
        lazyProb_mono fun G c h => (em (good (c 0).1)).elim (fun hg => Or.inr ⟨hg, h⟩) Or.inl
    _ ≤ lazyProb n p pac pup (fun _ c => ¬ good (c 0).1) +
        lazyProb n p pac pup (fun G c => good (c 0).1 ∧
          ¬ ((lazyBlueAfter G c B₀ 1).ncard : ℝ) ≤ bound) := lazyProb_or_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hbad hgood
    _ = ε := by ring

end PowerOfFew.Sparse

end
