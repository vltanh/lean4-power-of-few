module

public import PowerOfFew.Sparse.DayTwo
public import PowerOfFew.Sparse.DayThree
public import PowerOfFew.Sparse.Chernoff
public import PowerOfFew.Sparse.ActivationLastDays

/-!
# Sparse paper, Section 4: Blue shrinks with random activations and updates

Proposition 4.3 of the sparse paper: from `|B₁| ≤ n/2 − K √(n / (p p_ac))`, Blue shrinks by a
factor `1 − 0.8 p_up p_ac` every day (Lemmas 2.4 and 2.5 on the subgraph induced by the active
vertices, with Lemmas A.4, A.6 and A.7) until it has at most `α_λ (log n)/2` vertices. See
`PowerOfFew/Sparse/Activation.lean` for the setting and the readings of Section 4.

## The proof (the paper's, TeX 1410–1510)

Day `t + 1` uses the coins `c t`: `A = actSet (c t)` (the paper's `ac V_t`), `U = updSet (c t)`,
and the updating vertices are `A ∩ U`. By equation (main-lazy-details-temp0) (`lazyStep_eq`),
`|B_{t+1}| ≤ |B_t| − |B_t ∩ A ∩ U| + |A ∩ hypo B_t ∩ U|`, and `A ∩ hypo B_t` is, renumbered, the
next Blue set of majority dynamics on the subgraph `G[A] ∼ G(|A|, p)` induced by the active
vertices (`ncard_inter_hypoStep`, `gnpProb_inducedOn`). Write `q = p_up p_ac`.

* Case 1 (`B₁ → B₂`, `lazyShrinkAux_case1_det`, TeX 1425–1465): with
  `D = (K/4) √(p_ac n / p)` (the paper's `M √(p_ac n)`, `M = K p^(−1/2)/4`), the activation counts
  `|A₁ ∩ B₁|` and `|A₁|` are within `D` of their means except with probability `e^(−Ω(K²/p))`.
  Then `|A₁ ∩ B₁| ≤ m/2 − 2m/√(pm)` (`m = |A₁| ≤ 1.1 p_ac n`), Lemma 2.4 (`a = 2`, `b = 0.3`) on
  `G[A₁]` gives `|A₁ ∩ hypo B₁| ≤ 0.33 p_ac n`, Lemma A.6 gives at most `0.35 q n` updates among
  them, and a Chernoff bound gives `|B₁| − |B₁ ∩ A₁ ∩ U₁| ≤ n/2 − 0.45 q n`; so
  `|B₂| ≤ (1/2 − 0.1 q) n`, except with probability `e^(−Ω(K²/p)) + e^(−Ω(q n))`.
* Case 2 (`B_t → B_{t+1}`, `t ≥ 2`, while `|B_t| > α_λ (log n)/2`, `lazyShrinkAux_case2_det`,
  TeX 1467–1500): the activation counts are within `p_ac √(|B_t| log n)` and `p_ac √(n log n)` of
  their means (`n^(−Ω(p_ac))`), so the active Blue fraction is at most `1/2 − 0.09 q`; on
  `G[A_t]`, Lemma A.7 (`‖A − 𝐄A‖ ≤ C √(pm)`, `c = a = 1`) and Lemma A.4 (minimum degree at least
  `α' p m`, `ε = λ/2`) fail with probability at most `n^(−1/2) + n^(−λ/8)`, and otherwise Lemma 2.5
  gives `|A_t ∩ hypo B_t| ≤ p_ac |B_t| / 20`; Lemma A.6 and a Chernoff bound for the updates give
  `|B_{t+1}| ≤ (1 − 0.8 q) |B_t|`. Each day fails with probability at most
  `6 n^(−(α_λ/400) q)`.
* Iteration and union bound (`lazyShrinkAux_iterate`, `lazyShrinkAux_incl`,
  `lazyShrinkAux_bound`, TeX 1501–1510): after the `⌈2 log n / q⌉` days `t ∈ [2, T)` of Case 2,
  `T = ⌈2 log n / q⌉ + 2 ≤ 3 log n / q`, fewer than one Blue vertex would be left, which the event
  of the proposition excludes; the union bound gives `e^(−K²/(200 p)) + n^(−(α_λ/800) q)` for
  `n ≥ N(K, λ, p_ac, p_up)`.

The probabilities of the events of one day are computed conditionally on the graph and the past
(`lazyProb_le_of_forall_day`), and, for the events about `G[A]`, as averages over the coins of
`G(|A|, p)` probabilities (`lazyProb_eq_of_day`, `prod_dayLaw_real_eq_sum`,
`gnpProb_inducedOn`).

## Notes on the route

* Where the paper cites Lemma 2.6 (`S:lem:step3`) in Case 2, the bound it uses is the first half
  of the proof of Lemma 2.6 (TeX 1164–1198): Lemma 2.5 with Lemmas A.7 and A.4 on the active
  subgraph. The proof uses those three directly; Lemma 2.6 itself (Blue vanishes within
  `O(log_{pn} n)` days of the dynamics without activations) does not apply to the lazy dynamics.
* Lemma A.6 (`lemmaA_6`) bounds upper tails; it is used for every upper tail, on an auxiliary
  space of infinitely many coins that carries a binomial variable with the same law
  (`lazyShrinkAux_upper_tail`). The lower tails (`|A_t|` and the updating Blue vertices) use the
  standard Chernoff bound (30) (`IsBernoulliFamily.measureReal_sum_le_le_exp`), as the paper's
  "a standard Chernoff bound (e.g. Lemma A.6)" allows.
* The paper's "`|upd hypo B₂| ≤ 1.05 |ac hypo B₂|`" is a misprint for `≤ 1.05 p_up |…|`; the proof
  bounds `|upd hypo B₂| ≤ 0.35 q n` directly.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-! ### Conditioning on the graph and on the other days -/

/-- Conditioning on the graph and the coins of the other days: an event about the graph, the Blue
set of day `t` and the coins `c t` of day `t + 1` has probability at most `ε` if, for every graph
and every Blue set, the coins of one day make it happen with probability at most `ε`. -/
private lemma lazyShrinkAux_day_le {n : ℕ} {p pac pup ε : ℝ} (B₀ : Set (Fin n)) (t : ℕ)
    (Q : SimpleGraph (Fin n) → Set (Fin n) → DayCoins n → Prop)
    (h : ∀ G B, (dayLaw n pac pup).real {d | Q G B d} ≤ ε) :
    lazyProb n p pac pup (fun G c => Q G (lazyBlueAfter G c B₀ t) (c t)) ≤ ε := by
  apply lazyProb_le_of_forall_day t
  · intro G c c' hcc'
    rw [lazyBlueAfter_congr G B₀ (fun i hi => hcc' i hi.le), hcc' t le_rfl]
  · intro G c
    have hset : {d | Q G (lazyBlueAfter G (Function.update c t d) B₀ t)
        (Function.update c t d t)} = {d | Q G (lazyBlueAfter G c B₀ t) d} := by
      ext d
      simp only [Set.mem_ofPred_eq, Function.update_self]
      rw [lazyBlueAfter_congr G B₀ (c' := c) (fun i hi => Function.update_of_ne hi.ne _ _)]
    rw [hset]
    exact h G _

/-- An event about the graph and the coins `c t` of one day has probability at most `ε` if, for
every value of the coins, the graph makes it happen with probability at most `ε` under `G(n, p)`
(the coins are independent of the graph). -/
private lemma lazyShrinkAux_graph_day_le {n : ℕ} {p pac pup ε : ℝ} (t : ℕ)
    (Q : SimpleGraph (Fin n) → DayCoins n → Prop)
    (h : ∀ d, gnpProb n p (fun G => Q G d) ≤ ε) :
    lazyProb n p pac pup (fun G c => Q G (c t)) ≤ ε := by
  rw [lazyProb_eq_of_day t Q, prod_dayLaw_real_eq_sum]
  calc ∑ d, (dayLaw n pac pup).real {d} * gnpProb n p (fun G => Q G d)
      ≤ ∑ d, (dayLaw n pac pup).real {d} * ε :=
        Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (h d) measureReal_nonneg
    _ = ε := by
        rw [← Finset.sum_mul, sum_measureReal_singleton, Finset.coe_univ, probReal_univ, one_mul]

/-! ### Lemma A.6 for sets fixed in advance -/

/-- The coordinates of an infinite sequence of independent Bernoulli(`q`) coins. -/
private lemma lazyShrinkAux_isBernoulliFamily_infinitePi {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsBernoulliFamily (Measure.infinitePi fun _ : ℕ => bernoulliMeasure true false (toUnit q)) q
      (fun i (ω : ℕ → Bool) => if ω i then (1 : ℝ) else 0) where
  measurable i := (Measurable.of_discrete (f := fun b : Bool => if b then (1 : ℝ) else 0)).comp
    (measurable_pi_apply i)
  indep := iIndepFun_infinitePi (P := fun _ : ℕ => bernoulliMeasure true false (toUnit q))
    (X := fun _ (b : Bool) => if b then (1 : ℝ) else 0) fun _ => Measurable.of_discrete
  zero_or_one i ω := by cases ω i <;> simp
  prob_one i := by
    have hset : {ω : ℕ → Bool | (if ω i then (1 : ℝ) else 0) = 1} =
        (fun ω : ℕ → Bool => ω i) ⁻¹' {true} := by
      ext ω; cases ω i <;> simp
    rw [hset, ← map_measureReal_apply (measurable_pi_apply i)
      (measurableSet_singleton true), Measure.infinitePi_map_eval,
      bernoulliMeasure_real_apply_of_mem_of_notMem _ (measurableSet_singleton true) rfl
        (by simp), toUnit_coe hq0 hq1]

/-- The upper tail of a sum of `#s` Bernoulli(`q`) variables, as a sum of binomial weights: its
law is `Bin(#s, q)` whatever the family. -/
private lemma lazyShrinkAux_measureReal_le_sum {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {q : ℝ} {X : ι → Ω → ℝ}
    (hX : IsBernoulliFamily μ q X) (s : Finset ι) (x : ℝ) :
    μ.real {ω | x ≤ ∑ i ∈ s, X i ω} =
      ∑ k ∈ (Finset.range (s.card + 1)).filter (fun k : ℕ => x ≤ (k : ℝ)),
        (s.card.choose k : ℝ) * q ^ k * (1 - q) ^ (s.card - k) := by
  classical
  have hsum : ∀ ω, ∑ i ∈ s, X i ω = ((s.filter (fun i => X i ω = 1)).card : ℝ) := by
    intro ω
    rw [← Finset.sum_boole]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hX.zero_or_one i ω with h | h <;> simp [h]
  have hset : {ω | x ≤ ∑ i ∈ s, X i ω} =
      ⋃ k ∈ (Finset.range (s.card + 1)).filter (fun k : ℕ => x ≤ (k : ℝ)),
        {ω | ∑ i ∈ s, X i ω = k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range,
      exists_prop]
    constructor
    · intro hx
      refine ⟨(s.filter (fun i => X i ω = 1)).card, ⟨?_, ?_⟩, hsum ω⟩
      · exact Nat.lt_succ_of_le (Finset.card_filter_le _ _)
      · rwa [← hsum ω]
    · rintro ⟨k, ⟨-, hk⟩, hω⟩
      rwa [hω]
  have hmeas : ∀ k : ℕ, MeasurableSet {ω | ∑ i ∈ s, X i ω = k} := fun k =>
    (Finset.measurable_sum s fun i _ => hX.measurable i) (measurableSet_singleton _)
  rw [hset, measureReal_biUnion_finset]
  · exact Finset.sum_congr rfl fun k _ => hX.measureReal_sum_eq s k
  · intro k _ k' _ hkk'
    refine Set.disjoint_left.2 fun ω hω hω' => hkk' ?_
    simp only [Set.mem_ofPred_eq] at hω hω'
    exact_mod_cast hω.symm.trans hω'
  · exact fun k _ => hmeas k

/-- **Lemma A.6 for a set fixed in advance.** A sum of at most `m` independent Bernoulli(`q`)
variables exceeds `qm + t` with probability at most
`exp(−max{t² / (2(qm + t)), t² / (2(1 − q)m)})`. The sum is a binomial variable; Lemma A.6
(`lemmaA_6`) is applied to a binomial variable with the same law, on the space of an infinite
sequence of coins. -/
private lemma lazyShrinkAux_upper_tail {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) {X : ι → Ω → ℝ}
    (hX : IsBernoulliFamily μ q X) (s : Finset ι) {m : ℝ} (hm : 0 < m)
    (hsm : (s.card : ℝ) ≤ m) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | q * m + t ≤ ∑ i ∈ s, X i ω} ≤
      Real.exp (-max (t ^ 2 / (2 * (q * m + t))) (t ^ 2 / (2 * (1 - q) * m))) := by
  rcases hq1.lt_or_eq with hq1 | rfl
  · set μ' := Measure.infinitePi fun _ : ℕ => bernoulliMeasure true false (toUnit q)
    have hξ := lazyShrinkAux_isBernoulliFamily_infinitePi hq0.le hq1.le
    have key := lemmaA_6 (μ := μ') hq0 hq1 hm (Y := fun _ => s.card) (fun _ => hsm) hξ ht
    rw [lazyShrinkAux_measureReal_le_sum hX,
      ← Finset.card_range s.card, ← lazyShrinkAux_measureReal_le_sum hξ]
    exact key
  · have hempty : {ω | 1 * m + t ≤ ∑ i ∈ s, X i ω} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have hle : ∑ i ∈ s, X i ω ≤ s.card := by
        rw [← nsmul_one, ← Finset.sum_const]
        exact Finset.sum_le_sum fun i _ => by rcases hX.zero_or_one i ω with h | h <;> simp [h]
      linarith
    rw [hempty, measureReal_empty]
    positivity

/-! ### Chernoff bounds for the coins of one day -/

/-- Lemma A.6 for the active vertices of a set `S` fixed by the past (activation coins of one
day). -/
private lemma lazyShrinkAux_act_upper {n : ℕ} {pac pup : ℝ} (hpac0 : 0 < pac) (hpac1 : pac ≤ 1)
    (S : Set (Fin n)) {m t : ℝ} (hm : 0 < m) (hSm : (S.ncard : ℝ) ≤ m) (ht : 0 < t) :
    (dayLaw n pac pup).real {d | pac * m + t ≤ ((actSet d ∩ S).ncard : ℝ)} ≤
      Real.exp (-(t ^ 2 / (2 * (pac * m + t)))) := by
  classical
  have hset : {d : DayCoins n | pac * m + t ≤ ((actSet d ∩ S).ncard : ℝ)} =
      {d | pac * m + t ≤ ∑ v ∈ S.toFinset, (if d.1 v then 1 else 0 : ℝ)} := by
    ext d
    simp only [Set.mem_ofPred_eq]
    rw [Set.inter_comm, ncard_inter_setOf_eq_sum]
  rw [hset]
  refine (lazyShrinkAux_upper_tail hpac0 hpac1 (isBernoulliFamily_act hpac0.le hpac1)
    S.toFinset hm (by rwa [← Set.ncard_eq_toFinset_card']) ht).trans ?_
  exact Real.exp_le_exp.2 (neg_le_neg (le_max_left _ _))

/-- The standard Chernoff bound (30) for the active vertices of a set `S` fixed by the past. -/
private lemma lazyShrinkAux_act_lower {n : ℕ} {pac pup : ℝ} (hpac0 : 0 ≤ pac) (hpac1 : pac ≤ 1)
    (S : Set (Fin n)) {T : ℝ} (hT : T < pac * S.ncard) :
    (dayLaw n pac pup).real {d | ((actSet d ∩ S).ncard : ℝ) ≤ T} ≤
      Real.exp (-((pac * S.ncard - T) ^ 2 / (2 * (pac * S.ncard)))) := by
  classical
  have hset : {d : DayCoins n | ((actSet d ∩ S).ncard : ℝ) ≤ T} =
      {d | ∑ v ∈ S.toFinset, (if d.1 v then 1 else 0 : ℝ) ≤ T} := by
    ext d
    simp only [Set.mem_ofPred_eq]
    rw [Set.inter_comm, ncard_inter_setOf_eq_sum]
  rw [hset, Set.ncard_eq_toFinset_card'] at *
  exact (isBernoulliFamily_act hpac0 hpac1).measureReal_sum_le_le_exp hpac0 hpac1 S.toFinset hT

/-- Lemma A.6 for the update coins of a set `S` fixed by the past and the activations. -/
private lemma lazyShrinkAux_upd_upper {n : ℕ} {pup : ℝ} (hpup0 : 0 < pup) (hpup1 : pup ≤ 1)
    (S : Set (Fin n)) {m t : ℝ} (hm : 0 < m) (hSm : (S.ncard : ℝ) ≤ m) (ht : 0 < t) :
    (Measure.pi fun _ : Fin n => bernoulliMeasure true false (toUnit pup)).real
      {u | pup * m + t ≤ ((S ∩ {v | u v = true}).ncard : ℝ)} ≤
      Real.exp (-(t ^ 2 / (2 * (pup * m + t)))) := by
  classical
  have hset : {u : Fin n → Bool | pup * m + t ≤ ((S ∩ {v | u v = true}).ncard : ℝ)} =
      {u | pup * m + t ≤ ∑ v ∈ S.toFinset, (if u v then 1 else 0 : ℝ)} := by
    ext u
    simp only [Set.mem_ofPred_eq]
    rw [ncard_inter_setOf_eq_sum]
  rw [hset]
  refine (lazyShrinkAux_upper_tail hpup0 hpup1 (isBernoulliFamily_coins hpup0.le hpup1)
    S.toFinset hm (by rwa [← Set.ncard_eq_toFinset_card']) ht).trans ?_
  exact Real.exp_le_exp.2 (neg_le_neg (le_max_left _ _))

/-- The standard Chernoff bound (30) for the updating vertices of a set `S` fixed by the past. -/
private lemma lazyShrinkAux_actUpd_lower {n : ℕ} {pac pup : ℝ} (hpac0 : 0 ≤ pac)
    (hpac1 : pac ≤ 1) (hpup0 : 0 ≤ pup) (hpup1 : pup ≤ 1) (S : Set (Fin n)) {T : ℝ}
    (hT : T < pac * pup * S.ncard) :
    (dayLaw n pac pup).real {d | ((S ∩ (actSet d ∩ updSet d)).ncard : ℝ) ≤ T} ≤
      Real.exp (-((pac * pup * S.ncard - T) ^ 2 / (2 * (pac * pup * S.ncard)))) := by
  classical
  have hset : {d : DayCoins n | ((S ∩ (actSet d ∩ updSet d)).ncard : ℝ) ≤ T} =
      {d | ∑ v ∈ S.toFinset, (if d.1 v = true ∧ d.2 v = true then 1 else 0 : ℝ) ≤ T} := by
    ext d
    simp only [Set.mem_ofPred_eq]
    have h1 : actSet d ∩ updSet d = {v | (d.1 v && d.2 v) = true} := by
      ext v; simp
    rw [h1, ncard_inter_setOf_eq_sum]
    refine Iff.of_eq (congrArg (· ≤ T) (Finset.sum_congr rfl fun v _ => ?_))
    cases d.1 v <;> cases d.2 v <;> simp
  have hpq0 : 0 ≤ pac * pup := mul_nonneg hpac0 hpup0
  have hpq1 : pac * pup ≤ 1 := by nlinarith
  rw [hset, Set.ncard_eq_toFinset_card'] at *
  exact (isBernoulliFamily_actUpd hpac0 hpac1 hpup0 hpup1).measureReal_sum_le_le_exp hpq0 hpq1
    S.toFinset hT

/-! ### One day, and the spectral form of Lemma 2.5 -/

/-- Equation (main-lazy-details-temp0) as an inequality: the next day's Blue set has at most
`|B| − |B ∩ upd| + |upd ∩ hypo B|` vertices. -/
private lemma lazyShrinkAux_ncard_lazyStep_le {n : ℕ} (G : SimpleGraph (Fin n))
    (A U B : Set (Fin n)) :
    ((lazyStep G A U B).ncard : ℝ) ≤
      (B.ncard : ℝ) - (B ∩ (A ∩ U)).ncard + ((A ∩ hypoStep G A B) ∩ U).ncard := by
  have h3 : A ∩ U ∩ hypoStep G A B = (A ∩ hypoStep G A B) ∩ U := by
    ext v; simp only [Set.mem_inter_iff]; tauto
  rw [lazyStep_eq, h3]
  have h1 := Set.ncard_union_le (B \ (A ∩ U)) ((A ∩ hypoStep G A B) ∩ U)
  have h2 := Set.ncard_inter_add_ncard_sdiff_eq_ncard B (A ∩ U) (Set.toFinite B)
  have h1' : ((B \ (A ∩ U) ∪ (A ∩ hypoStep G A B) ∩ U).ncard : ℝ) ≤
      ((B \ (A ∩ U)).ncard : ℝ) + ((A ∩ hypoStep G A B) ∩ U).ncard := by exact_mod_cast h1
  have h2' : ((B ∩ (A ∩ U)).ncard : ℝ) + ((B \ (A ∩ U)).ncard : ℝ) = B.ncard := by
    exact_mod_cast h2
  linarith

/-- The spectral norm is subadditive. -/
private lemma lazyShrinkAux_specNorm_add_le {m : ℕ} (M N : Matrix (Fin m) (Fin m) ℝ) :
    specNorm (M + N) ≤ specNorm M + specNorm N := by
  unfold specNorm
  rw [map_add]
  exact norm_add_le _ _

/-- `‖𝐄A − p𝟏𝟏ᵀ‖ = ‖−pI‖ ≤ p`. -/
private lemma lazyShrinkAux_specNorm_meanAdj_sub_le {m : ℕ} {p : ℝ} (hp : 0 ≤ p) :
    specNorm (meanAdj m p - p • onesMat m) ≤ p := by
  have hM : meanAdj m p - p • onesMat m = (-p) • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    ext u v
    by_cases huv : u = v
    · subst huv; simp [meanAdj, onesMat]
    · simp [meanAdj, onesMat, huv, Matrix.one_apply_ne huv]
  unfold specNorm
  rw [hM, map_smul, map_one]
  calc ‖(-p) • (1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖
      ≤ ‖-p‖ * ‖(1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖ := norm_smul_le _ _
    _ ≤ p * 1 := by
        rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg hp]
        exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hp
    _ = p := mul_one p

private lemma lazyShrinkAux_specNorm_nonneg {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) :
    0 ≤ specNorm M := norm_nonneg _

/-- `inf_x ‖A_G − x𝟏𝟏ᵀ‖² ≤ (‖A_G − 𝐄A_G‖ + p)²`: take `x = p`. -/
private lemma lazyShrinkAux_iInf_le {m : ℕ} (H : SimpleGraph (Fin m)) {p : ℝ} (hp : 0 ≤ p) :
    (⨅ x : ℝ, specNorm (adjMat H - x • onesMat m) ^ 2) ≤
      (specNorm (adjMat H - meanAdj m p) + p) ^ 2 := by
  have hbdd : BddBelow (Set.range fun x : ℝ => specNorm (adjMat H - x • onesMat m) ^ 2) :=
    ⟨0, by rintro _ ⟨x, rfl⟩; exact sq_nonneg _⟩
  refine (ciInf_le hbdd p).trans ?_
  have h0 := lazyShrinkAux_specNorm_nonneg (adjMat H - p • onesMat m)
  have e1 := lazyShrinkAux_specNorm_add_le (adjMat H - meanAdj m p) (meanAdj m p - p • onesMat m)
  have e2 := lazyShrinkAux_specNorm_meanAdj_sub_le (m := m) hp
  rw [sub_add_sub_cancel] at e1
  have h1 : specNorm (adjMat H - p • onesMat m) ≤ specNorm (adjMat H - meanAdj m p) + p := by
    linarith
  exact pow_le_pow_left₀ h0 h1 2

/-- **Lemma 2.5 with the spectral bound (Lemma A.7) and the minimum degree bound (Lemma A.4)**,
as in the first half of the proof of Lemma 2.6: if `‖A_H − 𝐄A_H‖ ≤ C √(pm)` and every degree is
at least `α' p m`, then `|B_{t+1}| (α' p m)² ≤ (C √(pm) + p)² (1 − b)/(1/2 − b)² |B_t|`. -/
private lemma lazyShrinkAux_lemma2_5_bound {m : ℕ} (H : SimpleGraph (Fin m)) (B : Set (Fin m))
    {b p C α' : ℝ} (hb : b < 1 / 2) (hBb : (B.ncard : ℝ) ≤ b * m) (hp : 0 ≤ p) (hα' : 0 ≤ α')
    (hspec : specNorm (adjMat H - meanAdj m p) ≤ C * Real.sqrt (p * m))
    (hdeg : ∀ v, α' * p * m ≤ degree H v) :
    ((majorityStep H B).ncard : ℝ) * (α' * p * m) ^ 2 ≤
      (C * Real.sqrt (p * m) + p) ^ 2 * ((1 - b) / (1 / 2 - b) ^ 2) * B.ncard := by
  classical
  have hR : 0 ≤ (1 - b) / (1 / 2 - b) ^ 2 := by
    apply div_nonneg <;> nlinarith
  have hRHS : 0 ≤ (C * Real.sqrt (p * m) + p) ^ 2 * ((1 - b) / (1 / 2 - b) ^ 2) * B.ncard := by
    positivity
  rcases lemma2_5 H B hb hBb with h | h
  · rw [h, Set.ncard_empty, Nat.cast_zero, zero_mul]
    exact hRHS
  set S := majorityStep H B with hS
  rcases Nat.eq_zero_or_pos S.ncard with hk | hk
  · rw [hk, Nat.cast_zero, zero_mul]
    exact hRHS
  have hk' : (0 : ℝ) < S.ncard := by exact_mod_cast hk
  have hsum : (S.ncard : ℝ) * (α' * p * m) ≤ ∑ᶠ v ∈ S, (degree H v : ℝ) := by
    rw [finsum_mem_eq_toFinset_sum, Set.ncard_eq_toFinset_card']
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ fun v _ => hdeg v
  have hαpm : 0 ≤ α' * p * m := by positivity
  have hsq : ((S.ncard : ℝ) * (α' * p * m)) ^ 2 ≤ (∑ᶠ v ∈ S, (degree H v : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsum 2
  have hlhs : (S.ncard : ℝ) * (α' * p * m) ^ 2 ≤ (∑ᶠ v ∈ S, (degree H v : ℝ)) ^ 2 / S.ncard := by
    rw [le_div_iff₀ hk']
    nlinarith
  refine hlhs.trans (h.trans ?_)
  have hinf := lazyShrinkAux_iInf_le H hp
  have hC : specNorm (adjMat H - meanAdj m p) + p ≤ C * Real.sqrt (p * m) + p := by linarith
  have h0 : 0 ≤ specNorm (adjMat H - meanAdj m p) + p := by
    have := lazyShrinkAux_specNorm_nonneg (adjMat H - meanAdj m p)
    linarith
  have hsq2 := pow_le_pow_left₀ h0 hC 2
  have hB0 : (0 : ℝ) ≤ B.ncard := by positivity
  gcongr
  exact hinf.trans hsq2

/-! ### Probabilities of the events of one day -/

private lemma lazyShrinkAux_ncard_le {n : ℕ} (B : Set (Fin n)) : (B.ncard : ℝ) ≤ n := by
  have h := Set.ncard_le_card B
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact_mod_cast h

private lemma lazyShrinkAux_ncard_univ (n : ℕ) : (Set.univ : Set (Fin n)).ncard = n := by
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- `√(xL) ≤ x (1/2 + 1/α)` when `x > αL/2` (from `√(xL) ≤ (x + L)/2`). -/
private lemma lazyShrinkAux_sqrt_le {x L α : ℝ} (hα : 0 < α) (hx : 0 ≤ x) (hL : 0 ≤ L)
    (hxL : α * L / 2 < x) : Real.sqrt (x * L) ≤ x * (1 / 2 + 1 / α) := by
  have hL' : L ≤ 2 * x / α := by
    rw [le_div_iff₀ hα]; linarith
  have h1 : Real.sqrt (x * L) ≤ (x + L) / 2 :=
    Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [sq_nonneg (x - L)]⟩
  have e1 : x * (1 / 2 + 1 / α) = x / 2 + x / α := by ring
  have e2 : 2 * x / α = 2 * (x / α) := by ring
  rw [e2] at hL'
  rw [e1]
  linarith

/-- The activations of a day: at most `p_ac n − D` active vertices with probability at most
`exp(−D²/(2 p_ac n))` (the standard Chernoff bound (30)). -/
private lemma lazyShrinkAux_act_card_lower {n : ℕ} {p pac pup D : ℝ} (hpac0 : 0 < pac)
    (hpac1 : pac ≤ 1) (hD : 0 < D) (t : ℕ) :
    lazyProb n p pac pup (fun _ c => ((actSet (c t)).ncard : ℝ) ≤ pac * n - D) ≤
      Real.exp (-(D ^ 2 / (2 * (pac * n)))) := by
  refine lazyShrinkAux_day_le (B₀ := ∅) (Q := fun _ _ d => ((actSet d).ncard : ℝ) ≤ pac * n - D)
    t fun _ _ => ?_
  have h := lazyShrinkAux_act_lower (pup := pup) hpac0.le hpac1 (Set.univ : Set (Fin n))
    (T := pac * n - D) (by rw [lazyShrinkAux_ncard_univ]; linarith)
  simp only [Set.inter_univ, lazyShrinkAux_ncard_univ] at h
  convert h using 3
  ring

/-- The activations of a day: at least `p_ac n + D` active vertices with probability at most
`exp(−D²/(2(p_ac n + D)))` (Lemma A.6). -/
private lemma lazyShrinkAux_act_card_upper {n : ℕ} {p pac pup D : ℝ} (hn : 0 < n)
    (hpac0 : 0 < pac) (hpac1 : pac ≤ 1) (hD : 0 < D) (t : ℕ) :
    lazyProb n p pac pup (fun _ c => pac * n + D ≤ ((actSet (c t)).ncard : ℝ)) ≤
      Real.exp (-(D ^ 2 / (2 * (pac * n + D)))) := by
  refine lazyShrinkAux_day_le (B₀ := ∅) (Q := fun _ _ d => pac * n + D ≤ ((actSet d).ncard : ℝ))
    t fun _ _ => ?_
  have h := lazyShrinkAux_act_upper (pup := pup) hpac0 hpac1 (Set.univ : Set (Fin n))
    (m := n) (by exact_mod_cast hn) (by rw [lazyShrinkAux_ncard_univ]) hD
  simpa only [Set.inter_univ] using h

/-- Case 1: the active Blue vertices of day 1: `|A₁ ∩ B₁| ≥ p_ac |B₁| + D` with probability at
most `exp(−D²/(2(p_ac n + D)))` (Lemma A.6). -/
private lemma lazyShrinkAux_case1_act_inter {n : ℕ} {p pac pup D : ℝ} (hpac0 : 0 < pac)
    (hpac1 : pac ≤ 1) (hD : 0 < D) (B₀ : Set (Fin n)) :
    lazyProb n p pac pup (fun G c => pac * (lazyBlueAfter G c B₀ 1).ncard + D ≤
      ((actSet (c 1) ∩ lazyBlueAfter G c B₀ 1).ncard : ℝ)) ≤
      Real.exp (-(D ^ 2 / (2 * (pac * n + D)))) := by
  refine lazyShrinkAux_day_le B₀ 1
    (fun _ B d => pac * B.ncard + D ≤ ((actSet d ∩ B).ncard : ℝ)) fun G B => ?_
  rcases Nat.eq_zero_or_pos B.ncard with hB | hB
  · have hempty : {d : DayCoins n | pac * B.ncard + D ≤ ((actSet d ∩ B).ncard : ℝ)} = ∅ := by
      ext d
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have h1 : (actSet d ∩ B).ncard ≤ B.ncard := Set.ncard_le_ncard Set.inter_subset_right
      have h2 : (actSet d ∩ B).ncard = 0 := by omega
      rw [h2, hB]
      simpa using hD
    rw [hempty, measureReal_empty]
    positivity
  · have hBpos : (0 : ℝ) < B.ncard := by exact_mod_cast hB
    refine (lazyShrinkAux_act_upper hpac0 hpac1 B hBpos le_rfl hD).trans ?_
    have hBn := lazyShrinkAux_ncard_le B
    apply Real.exp_le_exp.2
    apply neg_le_neg
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith

/-- Case 2: the active Blue vertices of day `t`: when `|B_t| > αL/2`,
`|A_t ∩ B_t| ≥ p_ac |B_t| + p_ac √(|B_t| L)` with probability at most `exp(−(α/8) p_ac L)`
(Lemma A.6, deviation `√(p_ac |B_t| · p_ac L)` as in the paper). -/
private lemma lazyShrinkAux_case2_act_inter {n : ℕ} {p pac pup α L : ℝ} (hpac0 : 0 < pac)
    (hpac1 : pac ≤ 1) (hα0 : 0 < α) (hα1 : α ≤ 1) (hL : 0 < L) (B₀ : Set (Fin n)) (t : ℕ) :
    lazyProb n p pac pup (fun G c => α * L / 2 < (lazyBlueAfter G c B₀ t).ncard ∧
      pac * (lazyBlueAfter G c B₀ t).ncard +
          pac * Real.sqrt ((lazyBlueAfter G c B₀ t).ncard * L) ≤
        ((actSet (c t) ∩ lazyBlueAfter G c B₀ t).ncard : ℝ)) ≤
      Real.exp (-(α / 8 * pac * L)) := by
  refine lazyShrinkAux_day_le B₀ t (fun _ B d => α * L / 2 < B.ncard ∧
    pac * B.ncard + pac * Real.sqrt (B.ncard * L) ≤ ((actSet d ∩ B).ncard : ℝ)) fun G B => ?_
  by_cases hθ : α * L / 2 < B.ncard
  · have hB0 : (0 : ℝ) < B.ncard := lt_of_le_of_lt (by positivity) hθ
    have hδ : 0 < pac * Real.sqrt (B.ncard * L) := by positivity
    have hsub : {d : DayCoins n | α * L / 2 < B.ncard ∧
        pac * B.ncard + pac * Real.sqrt (B.ncard * L) ≤ ((actSet d ∩ B).ncard : ℝ)} ⊆
        {d | pac * B.ncard + pac * Real.sqrt (B.ncard * L) ≤ ((actSet d ∩ B).ncard : ℝ)} :=
      fun d hd => hd.2
    refine (measureReal_mono hsub).trans
      ((lazyShrinkAux_act_upper hpac0 hpac1 B hB0 le_rfl hδ).trans ?_)
    apply Real.exp_le_exp.2
    apply neg_le_neg
    have hsq : (pac * Real.sqrt (B.ncard * L)) ^ 2 = pac ^ 2 * (B.ncard * L) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hsqrt := lazyShrinkAux_sqrt_le hα0 hB0.le hL.le hθ
    rw [hsq, le_div_iff₀ (by positivity)]
    have h1 : pac * B.ncard + pac * Real.sqrt (B.ncard * L) ≤
        pac * (B.ncard * (3 / 2 + 1 / α)) := by nlinarith
    have h2 : α * (1 / α) = 1 := by field_simp
    have h3 : α / 8 * pac * L * (2 * (pac * (B.ncard * (3 / 2 + 1 / α)))) =
        pac ^ 2 * (B.ncard * L) * (3 * α / 8 + 1 / 4) := by
      field_simp
      ring
    have h4 : α / 8 * pac * L * (2 * (pac * B.ncard + pac * Real.sqrt (B.ncard * L))) ≤
        α / 8 * pac * L * (2 * (pac * (B.ncard * (3 / 2 + 1 / α)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have h5 : pac ^ 2 * (B.ncard * L) * (3 * α / 8 + 1 / 4) ≤ pac ^ 2 * (B.ncard * L) := by
      have : 0 ≤ pac ^ 2 * (B.ncard * L) := by positivity
      nlinarith
    linarith
  · have hempty : {d : DayCoins n | α * L / 2 < B.ncard ∧
        pac * B.ncard + pac * Real.sqrt (B.ncard * L) ≤ ((actSet d ∩ B).ncard : ℝ)} = ∅ := by
      ext d
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h => absurd h hθ
    rw [hempty, measureReal_empty]
    positivity

/-- The updating vertices among the active vertices that are Blue in the hypothetical step: for a
fixed graph and past, if `|A ∩ hypo B| ≤ m`, at least `p_up m + τ` of them update with probability
at most `exp(−τ²/(2(p_up m + τ)))` (Lemma A.6, given the activations). -/
private lemma lazyShrinkAux_upd_hypo {n : ℕ} {pac pup m τ : ℝ} (hpup0 : 0 < pup)
    (hpup1 : pup ≤ 1) (hm : 0 < m) (hτ : 0 < τ) (G : SimpleGraph (Fin n)) (B : Set (Fin n)) :
    (dayLaw n pac pup).real {d | ((actSet d ∩ hypoStep G (actSet d) B).ncard : ℝ) ≤ m ∧
      pup * m + τ ≤ (((actSet d ∩ hypoStep G (actSet d) B) ∩ updSet d).ncard : ℝ)} ≤
      Real.exp (-(τ ^ 2 / (2 * (pup * m + τ)))) := by
  refine dayLaw_real_le_of_forall_act (fun a u =>
    (({v | a v = true} ∩ hypoStep G {v | a v = true} B).ncard : ℝ) ≤ m ∧
      pup * m + τ ≤
        ((({v | a v = true} ∩ hypoStep G {v | a v = true} B) ∩ {v | u v = true}).ncard : ℝ))
    fun a => ?_
  by_cases hS : (({v | a v = true} ∩ hypoStep G {v | a v = true} B).ncard : ℝ) ≤ m
  · have hsub : {u : Fin n → Bool |
        (({v | a v = true} ∩ hypoStep G {v | a v = true} B).ncard : ℝ) ≤ m ∧
        pup * m + τ ≤
          ((({v | a v = true} ∩ hypoStep G {v | a v = true} B) ∩ {v | u v = true}).ncard : ℝ)} ⊆
        {u | pup * m + τ ≤
          ((({v | a v = true} ∩ hypoStep G {v | a v = true} B) ∩ {v | u v = true}).ncard : ℝ)} :=
      fun u hu => hu.2
    exact (measureReal_mono hsub).trans (lazyShrinkAux_upd_upper hpup0 hpup1 _ hm hS hτ)
  · have hempty : {u : Fin n → Bool |
        (({v | a v = true} ∩ hypoStep G {v | a v = true} B).ncard : ℝ) ≤ m ∧
        pup * m + τ ≤
          ((({v | a v = true} ∩ hypoStep G {v | a v = true} B) ∩ {v | u v = true}).ncard : ℝ)} =
        ∅ := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h => absurd h hS
    rw [hempty, measureReal_empty]
    positivity

/-- The vertices of a set `B` fixed by the past that update: at most `0.9 p_up p_ac |B|` of them
with probability at most `exp(−p_up p_ac |B| / 200)` (the standard Chernoff bound (30)). -/
private lemma lazyShrinkAux_actUpd_le {n : ℕ} {pac pup : ℝ} (hpac0 : 0 < pac) (hpac1 : pac ≤ 1)
    (hpup0 : 0 < pup) (hpup1 : pup ≤ 1) (B : Set (Fin n)) (hB : (0 : ℝ) < B.ncard) :
    (dayLaw n pac pup).real
      {d | ((B ∩ (actSet d ∩ updSet d)).ncard : ℝ) ≤ 9 / 10 * (pup * pac) * B.ncard} ≤
      Real.exp (-(pup * pac * B.ncard / 200)) := by
  have hq : 0 < pup * pac := mul_pos hpup0 hpac0
  have h := lazyShrinkAux_actUpd_lower hpac0.le hpac1 hpup0.le hpup1 B
    (T := 9 / 10 * (pup * pac) * B.ncard) (by nlinarith)
  refine h.trans (le_of_eq ?_)
  congr 1
  field_simp
  ring

/-- `gnpProb` of the impossible event. -/
private lemma lazyShrinkAux_gnpProb_false {n : ℕ} {p : ℝ} : gnpProb n p (fun _ => False) = 0 := by
  have h := gnpProb_not (n := n) (p := p) (fun _ => True)
  rw [gnpProb_true, sub_self] at h
  simpa using h

/-- Case 1, the subgraph induced by the active vertices of day 2 (Lemma 2.4 with `a = 2`,
`b = 0.3` on `G[A₁] ∼ G(|A₁|, p)`): if `|A₁| > x`, the conclusion of Lemma 2.4 fails with
probability at most `exp(−κ x)`. -/
private lemma lazyShrinkAux_case1_graph {n : ℕ} {p pac pup x κ : ℝ} {N₂₄ : ℕ}
    (h24 : ∀ m ≥ N₂₄, ∀ p : ℝ, 0 < p → p < 1 → 2 * Real.sqrt p ≤ 2 →
      3 / 10 ≤ 1 / 2 - 2 / Real.sqrt (p * m) →
      1 - Real.exp (-(κ * m)) ≤ gnpProb m p (fun G => ∀ B : Set (Fin m),
        (B.ncard : ℝ) ≤ m / 2 - 2 * m / Real.sqrt (p * m) →
          ((majorityStep G B).ncard : ℝ) ≤ 3 / 10 * m))
    (hκ : 0 < κ) (hp0 : 0 < p) (hp1 : p < 1) (hxN : (N₂₄ : ℝ) ≤ x) (hpx : 100 ≤ p * x)
    (t : ℕ) :
    lazyProb n p pac pup (fun G c => x < (actSet (c t)).ncard ∧
      ¬ ∀ B : Set (Fin (actSet (c t)).ncard),
        (B.ncard : ℝ) ≤ ((actSet (c t)).ncard : ℝ) / 2 -
          2 * (actSet (c t)).ncard / Real.sqrt (p * (actSet (c t)).ncard) →
          ((majorityStep (inducedOn G (actSet (c t))) B).ncard : ℝ) ≤
            3 / 10 * (actSet (c t)).ncard) ≤
      Real.exp (-(κ * x)) := by
  refine lazyShrinkAux_graph_day_le t (fun G d => x < (actSet d).ncard ∧
      ¬ ∀ B : Set (Fin (actSet d).ncard),
        (B.ncard : ℝ) ≤ ((actSet d).ncard : ℝ) / 2 -
          2 * (actSet d).ncard / Real.sqrt (p * (actSet d).ncard) →
          ((majorityStep (inducedOn G (actSet d)) B).ncard : ℝ) ≤ 3 / 10 * (actSet d).ncard)
    fun d => ?_
  by_cases hx : x < (actSet d).ncard
  · set A := actSet d with hA
    set m := A.ncard with hm
    have hmN : N₂₄ ≤ m := by exact_mod_cast hxN.trans hx.le
    have hpm : 100 ≤ p * m := hpx.trans (mul_le_mul_of_nonneg_left hx.le hp0.le)
    have hsqrt : 10 ≤ Real.sqrt (p * m) := by
      rw [show (10 : ℝ) = Real.sqrt (10 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have hb : (3 : ℝ) / 10 ≤ 1 / 2 - 2 / Real.sqrt (p * m) := by
      have : 2 / Real.sqrt (p * m) ≤ 1 / 5 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    have hsp : 2 * Real.sqrt p ≤ 2 := by
      have : Real.sqrt p ≤ 1 := Real.sqrt_le_one.2 hp1.le
      linarith
    have key := h24 m hmN p hp0 hp1 hsp hb
    calc gnpProb n p (fun G => x < m ∧ ¬ ∀ B : Set (Fin m),
          (B.ncard : ℝ) ≤ (m : ℝ) / 2 - 2 * m / Real.sqrt (p * m) →
            ((majorityStep (inducedOn G A) B).ncard : ℝ) ≤ 3 / 10 * m)
        ≤ gnpProb n p (fun G => ¬ ∀ B : Set (Fin m),
          (B.ncard : ℝ) ≤ (m : ℝ) / 2 - 2 * m / Real.sqrt (p * m) →
            ((majorityStep (inducedOn G A) B).ncard : ℝ) ≤ 3 / 10 * m) :=
          gnpProb_mono fun G h => h.2
      _ = gnpProb m p (fun H => ¬ ∀ B : Set (Fin m),
          (B.ncard : ℝ) ≤ (m : ℝ) / 2 - 2 * m / Real.sqrt (p * m) →
            ((majorityStep H B).ncard : ℝ) ≤ 3 / 10 * m) :=
          gnpProb_inducedOn A p (fun H => ¬ ∀ B : Set (Fin m),
            (B.ncard : ℝ) ≤ (m : ℝ) / 2 - 2 * m / Real.sqrt (p * m) →
              ((majorityStep H B).ncard : ℝ) ≤ 3 / 10 * m)
      _ ≤ Real.exp (-(κ * m)) := by rw [gnpProb_not]; linarith
      _ ≤ Real.exp (-(κ * x)) := by
          apply Real.exp_le_exp.2
          nlinarith
  · calc gnpProb n p _ ≤ gnpProb n p (fun _ => False) := gnpProb_mono fun G h => hx h.1
      _ = 0 := lazyShrinkAux_gnpProb_false
      _ ≤ Real.exp (-(κ * x)) := by positivity

/-- Case 2, the subgraph induced by the active vertices of day `t + 1`, `G[A_t] ∼ G(|A_t|, p)`:
if `|A_t| > x`, the spectral bound of Lemma A.7 (`c = a = 1`) or the minimum degree bound of
Lemma A.4 (`ε = λ/2`) fails with probability at most `n^(−1/2) + n^(−λ/8)`. -/
private lemma lazyShrinkAux_case2_graph {n : ℕ} {p pac pup lam C x : ℝ}
    (hC : ∀ (m : ℕ) (p : ℝ), 0 < p → p ≤ 1 → 1 * Real.log m ≤ p * m →
      1 - (m : ℝ) ^ (-(1 : ℝ)) ≤
        gnpProb m p (fun G => specNorm (adjMat G - meanAdj m p) ≤ C * Real.sqrt (p * m)))
    (hlam : 0 < lam) (hp0 : 0 < p) (hp1 : p ≤ 1) (hx_size : 4 / (lam / 2) + 4 ≤ x)
    (hx_sqrt : Real.sqrt n ≤ x) (hx_dens : (1 + lam / 2) * Real.log n ≤ p * x) (t : ℕ) :
    lazyProb n p pac pup (fun G c => x < (actSet (c t)).ncard ∧
      ¬ (specNorm (adjMat (inducedOn G (actSet (c t))) - meanAdj (actSet (c t)).ncard p) ≤
          C * Real.sqrt (p * (actSet (c t)).ncard) ∧
        ∀ v, Real.exp (-(8 / (lam / 2) + 7)) * p * (actSet (c t)).ncard ≤
          degree (inducedOn G (actSet (c t))) v)) ≤
      Real.exp (-(Real.log n / 2)) + Real.exp (-(lam / 8 * Real.log n)) := by
  refine lazyShrinkAux_graph_day_le t (fun G d => x < (actSet d).ncard ∧
      ¬ (specNorm (adjMat (inducedOn G (actSet d)) - meanAdj (actSet d).ncard p) ≤
          C * Real.sqrt (p * (actSet d).ncard) ∧
        ∀ v, Real.exp (-(8 / (lam / 2) + 7)) * p * (actSet d).ncard ≤
          degree (inducedOn G (actSet d)) v)) fun d => ?_
  by_cases hx : x < (actSet d).ncard
  · set A := actSet d with hA
    set m := A.ncard with hm
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx_size
    have hm0 : (0 : ℝ) < m := hx0.trans hx
    have hmn : (m : ℝ) ≤ n := lazyShrinkAux_ncard_le A
    have hsqrt0 : 0 < Real.sqrt n := Real.sqrt_pos.2 (hm0.trans_le hmn)
    have hlogm : Real.log m ≤ Real.log n := Real.log_le_log hm0 hmn
    have hlogm' : Real.log n / 2 ≤ Real.log m := by
      rw [← Real.log_sqrt (by positivity)]
      exact Real.log_le_log hsqrt0 (hx_sqrt.trans hx.le)
    have hlogm0 : 0 ≤ Real.log m := Real.log_nonneg (by
      have : (1 : ℝ) ≤ m := by
        have h1 : 0 < m := by exact_mod_cast hm0
        exact_mod_cast h1
      exact this)
    have hdens : (1 + lam / 2) * Real.log m ≤ p * m := by
      have h1 : (1 + lam / 2) * Real.log m ≤ (1 + lam / 2) * Real.log n :=
        mul_le_mul_of_nonneg_left hlogm (by positivity)
      have h2 : p * x ≤ p * m := mul_le_mul_of_nonneg_left hx.le hp0.le
      linarith
    have hspec := hC m p hp0 hp1 (by nlinarith)
    have hdeg := lemmaA_4 (ε := lam / 2) (by positivity) (n := m) (hx_size.trans hx.le) hp0 hp1
      hdens
    calc gnpProb n p (fun G => x < m ∧
          ¬ (specNorm (adjMat (inducedOn G A) - meanAdj m p) ≤ C * Real.sqrt (p * m) ∧
            ∀ v, Real.exp (-(8 / (lam / 2) + 7)) * p * m ≤ degree (inducedOn G A) v))
        ≤ gnpProb n p (fun G =>
          ¬ (specNorm (adjMat (inducedOn G A) - meanAdj m p) ≤ C * Real.sqrt (p * m) ∧
            ∀ v, Real.exp (-(8 / (lam / 2) + 7)) * p * m ≤ degree (inducedOn G A) v)) :=
          gnpProb_mono fun G h => h.2
      _ = gnpProb m p (fun H =>
          ¬ (specNorm (adjMat H - meanAdj m p) ≤ C * Real.sqrt (p * m) ∧
            ∀ v, Real.exp (-(8 / (lam / 2) + 7)) * p * m ≤ degree H v)) :=
          gnpProb_inducedOn A p (fun H =>
            ¬ (specNorm (adjMat H - meanAdj m p) ≤ C * Real.sqrt (p * m) ∧
              ∀ v, Real.exp (-(8 / (lam / 2) + 7)) * p * m ≤ degree H v))
      _ ≤ gnpProb m p (fun H => ¬ specNorm (adjMat H - meanAdj m p) ≤ C * Real.sqrt (p * m)) +
          gnpProb m p (fun H => ¬ ∀ v, Real.exp (-(8 / (lam / 2) + 7)) * p * m ≤ degree H v) :=
          (gnpProb_mono fun H h => not_and_or.1 h).trans (gnpProb_or_le _ _)
      _ ≤ (m : ℝ) ^ (-(1 : ℝ)) + (m : ℝ) ^ (-(lam / 2 / 2)) := by
          rw [gnpProb_not, gnpProb_not]; linarith
      _ ≤ Real.exp (-(Real.log n / 2)) + Real.exp (-(lam / 8 * Real.log n)) := by
          rw [Real.rpow_def_of_pos hm0, Real.rpow_def_of_pos hm0]
          gcongr
          · linarith
          · nlinarith
  · calc gnpProb n p _ ≤ gnpProb n p (fun _ => False) := gnpProb_mono fun G h => hx h.1
      _ = 0 := lazyShrinkAux_gnpProb_false
      _ ≤ Real.exp (-(Real.log n / 2)) + Real.exp (-(lam / 8 * Real.log n)) := by positivity

/-- Case 1, the update coins of day 2: if `|A₁ ∩ hypo B₁| ≤ 0.33 p_ac n`, at least `0.35 p_up p_ac n`
of these vertices update with probability at most `exp(−p_up p_ac n / 1750)` (Lemma A.6). -/
private lemma lazyShrinkAux_case1_upd {n : ℕ} {p pac pup : ℝ} (hpac0 : 0 < pac) (hpup0 : 0 < pup)
    (hpup1 : pup ≤ 1) (hn : 0 < n) (B₀ : Set (Fin n)) :
    lazyProb n p pac pup (fun G c =>
      ((actSet (c 1) ∩ hypoStep G (actSet (c 1)) (lazyBlueAfter G c B₀ 1)).ncard : ℝ) ≤
          33 / 100 * pac * n ∧
        35 / 100 * (pup * pac) * n ≤ (((actSet (c 1) ∩
          hypoStep G (actSet (c 1)) (lazyBlueAfter G c B₀ 1)) ∩ updSet (c 1)).ncard : ℝ)) ≤
      Real.exp (-(pup * pac * n / 1750)) := by
  refine lazyShrinkAux_day_le B₀ 1 (fun G B d =>
    ((actSet d ∩ hypoStep G (actSet d) B).ncard : ℝ) ≤ 33 / 100 * pac * n ∧
      35 / 100 * (pup * pac) * n ≤ (((actSet d ∩ hypoStep G (actSet d) B) ∩ updSet d).ncard : ℝ))
    fun G B => ?_
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : 0 < 33 / 100 * pac * n := by positivity
  have hτ : 0 < 2 / 100 * (pup * pac) * n := by positivity
  have h := lazyShrinkAux_upd_hypo (pac := pac) hpup0 hpup1 hm hτ G B
  have e : pup * (33 / 100 * pac * n) + 2 / 100 * (pup * pac) * n =
      35 / 100 * (pup * pac) * n := by ring
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  field_simp
  ring

/-- Case 2, the update coins of day `t + 1`: if `|B_t| > αL/2` and
`|A_t ∩ hypo B_t| ≤ p_ac |B_t| / 20`, at least `0.1 p_up p_ac |B_t|` of these vertices update with
probability at most `exp(−(α/160) p_up p_ac L)` (Lemma A.6). -/
private lemma lazyShrinkAux_case2_upd {n : ℕ} {p pac pup α L : ℝ} (hpac0 : 0 < pac)
    (hpup0 : 0 < pup) (hpup1 : pup ≤ 1) (hα0 : 0 < α) (hL : 0 ≤ L) (B₀ : Set (Fin n)) (t : ℕ) :
    lazyProb n p pac pup (fun G c => α * L / 2 < (lazyBlueAfter G c B₀ t).ncard ∧
      ((actSet (c t) ∩ hypoStep G (actSet (c t)) (lazyBlueAfter G c B₀ t)).ncard : ℝ) ≤
          pac * (lazyBlueAfter G c B₀ t).ncard / 20 ∧
        1 / 10 * (pup * pac) * (lazyBlueAfter G c B₀ t).ncard ≤ (((actSet (c t) ∩
          hypoStep G (actSet (c t)) (lazyBlueAfter G c B₀ t)) ∩ updSet (c t)).ncard : ℝ)) ≤
      Real.exp (-(α / 160 * (pup * pac) * L)) := by
  refine lazyShrinkAux_day_le B₀ t (fun G B d => α * L / 2 < B.ncard ∧
    ((actSet d ∩ hypoStep G (actSet d) B).ncard : ℝ) ≤ pac * B.ncard / 20 ∧
      1 / 10 * (pup * pac) * B.ncard ≤
        (((actSet d ∩ hypoStep G (actSet d) B) ∩ updSet d).ncard : ℝ)) fun G B => ?_
  by_cases hθ : α * L / 2 < B.ncard
  · have hB0 : (0 : ℝ) < B.ncard := lt_of_le_of_lt (by positivity) hθ
    have hm : 0 < pac * B.ncard / 20 := by positivity
    have hτ : 0 < 1 / 20 * (pup * pac) * B.ncard := by positivity
    have h := lazyShrinkAux_upd_hypo (pac := pac) hpup0 hpup1 hm hτ G B
    have e : pup * (pac * B.ncard / 20) + 1 / 20 * (pup * pac) * B.ncard =
        1 / 10 * (pup * pac) * B.ncard := by ring
    rw [e] at h
    have hsub : {d : DayCoins n | α * L / 2 < B.ncard ∧
        ((actSet d ∩ hypoStep G (actSet d) B).ncard : ℝ) ≤ pac * B.ncard / 20 ∧
        1 / 10 * (pup * pac) * B.ncard ≤
          (((actSet d ∩ hypoStep G (actSet d) B) ∩ updSet d).ncard : ℝ)} ⊆
        {d | ((actSet d ∩ hypoStep G (actSet d) B).ncard : ℝ) ≤ pac * B.ncard / 20 ∧
        1 / 10 * (pup * pac) * B.ncard ≤
          (((actSet d ∩ hypoStep G (actSet d) B) ∩ updSet d).ncard : ℝ)} := fun d hd => hd.2
    refine (measureReal_mono hsub).trans (h.trans ?_)
    apply Real.exp_le_exp.2
    apply neg_le_neg
    have e2 : (1 / 20 * (pup * pac) * B.ncard) ^ 2 / (2 * (1 / 10 * (pup * pac) * B.ncard)) =
        pup * pac * B.ncard / 80 := by
      field_simp
      ring
    rw [e2]
    have hq : 0 < pup * pac := mul_pos hpup0 hpac0
    have := mul_lt_mul_of_pos_left hθ hq
    nlinarith
  · have hempty : {d : DayCoins n | α * L / 2 < B.ncard ∧
        ((actSet d ∩ hypoStep G (actSet d) B).ncard : ℝ) ≤ pac * B.ncard / 20 ∧
        1 / 10 * (pup * pac) * B.ncard ≤
          (((actSet d ∩ hypoStep G (actSet d) B) ∩ updSet d).ncard : ℝ)} = ∅ := by
      ext d
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h => absurd h hθ
    rw [hempty, measureReal_empty]
    positivity

/-- Case 1, the updating Blue vertices of day 2: if `|B₁| > n/2 − 0.45 p_up p_ac n`, at most
`0.9 p_up p_ac |B₁|` of them update with probability at most `exp(−p_up p_ac n / 4000)`. -/
private lemma lazyShrinkAux_case1_stay {n : ℕ} {p pac pup : ℝ} (hpac0 : 0 < pac)
    (hpac1 : pac ≤ 1) (hpup0 : 0 < pup) (hpup1 : pup ≤ 1) (B₀ : Set (Fin n)) :
    lazyProb n p pac pup (fun G c =>
      (n : ℝ) / 2 - 45 / 100 * (pup * pac) * n < (lazyBlueAfter G c B₀ 1).ncard ∧
        (((lazyBlueAfter G c B₀ 1) ∩ (actSet (c 1) ∩ updSet (c 1))).ncard : ℝ) ≤
          9 / 10 * (pup * pac) * (lazyBlueAfter G c B₀ 1).ncard) ≤
      Real.exp (-(pup * pac * n / 4000)) := by
  refine lazyShrinkAux_day_le B₀ 1 (fun _ B d =>
    (n : ℝ) / 2 - 45 / 100 * (pup * pac) * n < B.ncard ∧
      ((B ∩ (actSet d ∩ updSet d)).ncard : ℝ) ≤ 9 / 10 * (pup * pac) * B.ncard) fun G B => ?_
  have hq : 0 < pup * pac := mul_pos hpup0 hpac0
  have hq1 : pup * pac ≤ 1 := by nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hB : (n : ℝ) / 2 - 45 / 100 * (pup * pac) * n < B.ncard
  · have hB' : (n : ℝ) / 20 < B.ncard := by nlinarith
    have hB0 : (0 : ℝ) < B.ncard := lt_of_le_of_lt (by positivity) hB'
    have hsub : {d : DayCoins n | (n : ℝ) / 2 - 45 / 100 * (pup * pac) * n < B.ncard ∧
        ((B ∩ (actSet d ∩ updSet d)).ncard : ℝ) ≤ 9 / 10 * (pup * pac) * B.ncard} ⊆
        {d | ((B ∩ (actSet d ∩ updSet d)).ncard : ℝ) ≤ 9 / 10 * (pup * pac) * B.ncard} :=
      fun d hd => hd.2
    refine (measureReal_mono hsub).trans
      ((lazyShrinkAux_actUpd_le hpac0 hpac1 hpup0 hpup1 B hB0).trans ?_)
    apply Real.exp_le_exp.2
    apply neg_le_neg
    have := mul_le_mul_of_nonneg_left hB'.le hq.le
    have e : pup * pac * B.ncard / 200 = pup * pac * B.ncard * (1 / 200) := by ring
    have e2 : pup * pac * n / 4000 = pup * pac * (n / 20) * (1 / 200) := by ring
    rw [e, e2]
    exact mul_le_mul_of_nonneg_right this (by norm_num)
  · have hempty : {d : DayCoins n | (n : ℝ) / 2 - 45 / 100 * (pup * pac) * n < B.ncard ∧
        ((B ∩ (actSet d ∩ updSet d)).ncard : ℝ) ≤ 9 / 10 * (pup * pac) * B.ncard} = ∅ := by
      ext d
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h => absurd h hB
    rw [hempty, measureReal_empty]
    positivity

/-- Case 2, the updating Blue vertices of day `t + 1`: if `|B_t| > αL/2`, at most
`0.9 p_up p_ac |B_t|` of them update with probability at most `exp(−(α/400) p_up p_ac L)`. -/
private lemma lazyShrinkAux_case2_stay {n : ℕ} {p pac pup α L : ℝ} (hpac0 : 0 < pac)
    (hpac1 : pac ≤ 1) (hpup0 : 0 < pup) (hpup1 : pup ≤ 1) (hα0 : 0 < α) (hL : 0 ≤ L)
    (B₀ : Set (Fin n)) (t : ℕ) :
    lazyProb n p pac pup (fun G c => α * L / 2 < (lazyBlueAfter G c B₀ t).ncard ∧
        (((lazyBlueAfter G c B₀ t) ∩ (actSet (c t) ∩ updSet (c t))).ncard : ℝ) ≤
          9 / 10 * (pup * pac) * (lazyBlueAfter G c B₀ t).ncard) ≤
      Real.exp (-(α / 400 * (pup * pac) * L)) := by
  refine lazyShrinkAux_day_le B₀ t (fun _ B d => α * L / 2 < B.ncard ∧
      ((B ∩ (actSet d ∩ updSet d)).ncard : ℝ) ≤ 9 / 10 * (pup * pac) * B.ncard) fun G B => ?_
  have hq : 0 < pup * pac := mul_pos hpup0 hpac0
  by_cases hθ : α * L / 2 < B.ncard
  · have hB0 : (0 : ℝ) < B.ncard := lt_of_le_of_lt (by positivity) hθ
    have hsub : {d : DayCoins n | α * L / 2 < B.ncard ∧
        ((B ∩ (actSet d ∩ updSet d)).ncard : ℝ) ≤ 9 / 10 * (pup * pac) * B.ncard} ⊆
        {d | ((B ∩ (actSet d ∩ updSet d)).ncard : ℝ) ≤ 9 / 10 * (pup * pac) * B.ncard} :=
      fun d hd => hd.2
    refine (measureReal_mono hsub).trans
      ((lazyShrinkAux_actUpd_le hpac0 hpac1 hpup0 hpup1 B hB0).trans ?_)
    apply Real.exp_le_exp.2
    apply neg_le_neg
    have := mul_le_mul_of_nonneg_left hθ.le hq.le
    have e : pup * pac * B.ncard / 200 = pup * pac * B.ncard * (1 / 200) := by ring
    have e2 : α / 400 * (pup * pac) * L = pup * pac * (α * L / 2) * (1 / 200) := by ring
    rw [e, e2]
    exact mul_le_mul_of_nonneg_right this (by norm_num)
  · have hempty : {d : DayCoins n | α * L / 2 < B.ncard ∧
        ((B ∩ (actSet d ∩ updSet d)).ncard : ℝ) ≤ 9 / 10 * (pup * pac) * B.ncard} = ∅ := by
      ext d
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h => absurd h hθ
    rw [hempty, measureReal_empty]
    positivity

/-! ### The deterministic parts -/

/-- `p_ac K √(n/(p p_ac)) = 4D` for `D = (K/4) √(p_ac n / p)`. -/
private lemma lazyShrinkAux_pac_mul_sqrt {n p pac K : ℝ} (hp : 0 < p) (hpac : 0 < pac) :
    pac * (K * Real.sqrt (n / (p * pac))) = 4 * (K / 4 * Real.sqrt (pac * n / p)) := by
  have h : pac * n / p = pac ^ 2 * (n / (p * pac)) := by
    field_simp
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq hpac.le]
  ring

/-- Case 1, the numbers: with `D = (K/4) √(p_ac n / p) ≤ p_ac n / 10` and `K ≥ 8`, if
`|B₁| ≤ n/2 − K √(n/(p p_ac))`, `|A₁ ∩ B₁| < p_ac |B₁| + D` and `|A₁| = p_ac n ± D`, then
`|A₁|/2 − |A₁ ∩ B₁| ≥ 2.5 D ≥ 2 √(|A₁|/p)`, i.e. `|A₁ ∩ B₁| ≤ m/2 − 2m/√(pm)` with `m = |A₁|`
(the hypothesis of Lemma 2.4 with `a = 2`), and `m ≤ 1.1 p_ac n`. -/
private lemma lazyShrinkAux_case1_num {n p pac K m AB Bc : ℝ} (hp0 : 0 < p) (hpac0 : 0 < pac)
    (hK : 8 ≤ K) (hn0 : 0 ≤ n) (hDn : K / 4 * Real.sqrt (pac * n / p) ≤ pac * n / 10)
    (hB : Bc ≤ n / 2 - K * Real.sqrt (n / (p * pac)))
    (h1a : AB < pac * Bc + K / 4 * Real.sqrt (pac * n / p))
    (h1b : pac * n - K / 4 * Real.sqrt (pac * n / p) < m)
    (h1c : m < pac * n + K / 4 * Real.sqrt (pac * n / p)) :
    AB ≤ m / 2 - 2 * m / Real.sqrt (p * m) ∧ m ≤ 11 / 10 * (pac * n) := by
  set D := K / 4 * Real.sqrt (pac * n / p) with hD
  have hD0 : 0 ≤ D := by positivity
  have hD2 : D ^ 2 = K ^ 2 / 16 * (pac * n / p) := by
    rw [hD, mul_pow, Real.sq_sqrt (by positivity)]; ring
  have h4D : pac * (K * Real.sqrt (n / (p * pac))) = 4 * D :=
    lazyShrinkAux_pac_mul_sqrt hp0 hpac0
  have hpn0 : 0 ≤ pac * n := mul_nonneg hpac0.le hn0
  have hm0 : 0 < m := by linarith
  have hm1 : m ≤ 11 / 10 * (pac * n) := by linarith
  refine ⟨?_, hm1⟩
  have h25 : 2 * m / Real.sqrt (p * m) ≤ 5 / 2 * D := by
    have hs : 0 < Real.sqrt (p * m) := Real.sqrt_pos.2 (mul_pos hp0 hm0)
    rw [div_le_iff₀ hs]
    have hsqpm := Real.sq_sqrt (mul_pos hp0 hm0).le
    have hlhs : (2 * m) ^ 2 ≤ (5 / 2 * D * Real.sqrt (p * m)) ^ 2 := by
      have e : (5 / 2 * D * Real.sqrt (p * m)) ^ 2 = 25 / 4 * D ^ 2 * (p * m) := by
        rw [mul_pow, hsqpm]; ring
      rw [e, hD2]
      have e2 : 25 / 4 * (K ^ 2 / 16 * (pac * n / p)) * (p * m) =
          25 / 64 * K ^ 2 * (pac * n) * m := by
        field_simp
        ring
      rw [e2]
      have hK2 : 64 ≤ K ^ 2 := by nlinarith
      have hpnm : 0 ≤ pac * n * m := mul_nonneg hpn0 hm0.le
      have h1 : 25 * (pac * n) * m ≤ 25 / 64 * K ^ 2 * (pac * n) * m := by
        have := mul_le_mul_of_nonneg_right hK2 hpnm
        linarith
      have h2 : 4 * m ^ 2 ≤ 25 * (pac * n) * m := by
        have := mul_le_mul_of_nonneg_right hm1 hm0.le
        nlinarith
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hlhs
  have hpacB : pac * Bc ≤ pac * n / 2 - 4 * D := by
    have := mul_le_mul_of_nonneg_left hB hpac0.le
    rw [mul_sub, h4D] at this
    linarith
  linarith

/-- Case 1, the Blue vertices that keep their colour: `|B₁| − |B₁ ∩ upd| ≤ n/2 − 0.45 q n`,
either because `|B₁| ≤ n/2 − 0.45 q n` or because at least `0.9 q |B₁|` of them update. -/
private lemma lazyShrinkAux_case1_keep {n q Bc X : ℝ} (hq1 : q ≤ 1) (hBn : Bc ≤ n / 2)
    (hX0 : 0 ≤ X) (h1f : ¬ (n / 2 - 45 / 100 * q * n < Bc ∧ X ≤ 9 / 10 * q * Bc)) :
    Bc - X ≤ n / 2 - 45 / 100 * q * n := by
  by_cases hBbig : n / 2 - 45 / 100 * q * n < Bc
  · have h1 : 9 / 10 * q * Bc < X := by
      by_contra h
      exact h1f ⟨hBbig, not_lt.1 h⟩
    have h2 := mul_le_mul_of_nonneg_left hBn (by linarith : (0 : ℝ) ≤ 1 - 9 / 10 * q)
    have e : (1 - 9 / 10 * q) * (n / 2) = n / 2 - 45 / 100 * q * n := by ring
    have e2 : (1 - 9 / 10 * q) * Bc = Bc - 9 / 10 * q * Bc := by ring
    linarith
  · linarith

/-- **Case 1** (from `B₁` to `B₂`), on the good events: the activation counts are within `D` of
their means, the subgraph induced by the active vertices satisfies the conclusion of Lemma 2.4
(`a = 2`, `b = 0.3`), and the update coins behave; then `|B₂| ≤ (1/2 − 0.1 p_up p_ac) n`
(equation (main-lazy-details-temp3)). -/
private lemma lazyShrinkAux_case1_det {n : ℕ} (G : SimpleGraph (Fin n)) (B : Set (Fin n))
    (d : DayCoins n) {p pac pup K : ℝ} (hp0 : 0 < p) (hpac0 : 0 < pac) (hpac1 : pac ≤ 1)
    (hpup1 : pup ≤ 1) (hK : 8 ≤ K)
    (hDn : K / 4 * Real.sqrt (pac * n / p) ≤ pac * n / 10)
    (hB : (B.ncard : ℝ) ≤ n / 2 - K * Real.sqrt (n / (p * pac)))
    (h1a : ((actSet d ∩ B).ncard : ℝ) < pac * B.ncard + K / 4 * Real.sqrt (pac * n / p))
    (h1b : pac * n - K / 4 * Real.sqrt (pac * n / p) < (actSet d).ncard)
    (h1c : ((actSet d).ncard : ℝ) < pac * n + K / 4 * Real.sqrt (pac * n / p))
    (h1d : ∀ B' : Set (Fin (actSet d).ncard),
      (B'.ncard : ℝ) ≤ ((actSet d).ncard : ℝ) / 2 -
        2 * (actSet d).ncard / Real.sqrt (p * (actSet d).ncard) →
        ((majorityStep (inducedOn G (actSet d)) B').ncard : ℝ) ≤ 3 / 10 * (actSet d).ncard)
    (h1e : ¬ (((actSet d ∩ hypoStep G (actSet d) B).ncard : ℝ) ≤ 33 / 100 * pac * n ∧
      35 / 100 * (pup * pac) * n ≤
        (((actSet d ∩ hypoStep G (actSet d) B) ∩ updSet d).ncard : ℝ)))
    (h1f : ¬ ((n : ℝ) / 2 - 45 / 100 * (pup * pac) * n < B.ncard ∧
      ((B ∩ (actSet d ∩ updSet d)).ncard : ℝ) ≤ 9 / 10 * (pup * pac) * B.ncard)) :
    ((lazyStep G (actSet d) (updSet d) B).ncard : ℝ) ≤ (1 / 2 - 1 / 10 * (pup * pac)) * n := by
  have hq1 : pup * pac ≤ 1 := by nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨hAB, hm1⟩ := lazyShrinkAux_case1_num hp0 hpac0 hK hn0 hDn hB h1a h1b h1c
  -- Lemma 2.4 on the active subgraph: `|A₁ ∩ hypo B₁| ≤ 0.3 |A₁| ≤ 0.33 p_ac n`
  have hS : ((actSet d ∩ hypoStep G (actSet d) B).ncard : ℝ) ≤ 33 / 100 * pac * n := by
    rw [ncard_inter_hypoStep]
    have h := h1d (enumSet (actSet d) ⁻¹' B) (by rw [ncard_preimage_enumSet]; exact hAB)
    linarith
  have hSU : (((actSet d ∩ hypoStep G (actSet d) B) ∩ updSet d).ncard : ℝ) <
      35 / 100 * (pup * pac) * n := by
    by_contra h
    exact h1e ⟨hS, not_lt.1 h⟩
  have hsq0 : 0 ≤ K * Real.sqrt (n / (p * pac)) := by
    have : 0 ≤ K := by linarith
    positivity
  have hkeep := lazyShrinkAux_case1_keep hq1 (by linarith) (Nat.cast_nonneg _) h1f
  have hstep := lazyShrinkAux_ncard_lazyStep_le G (actSet d) (updSet d) B
  linarith

/-- `(1 − b)/(1/2 − b)² ≤ 124/q²` for `b = 1/2 − 0.09 q`. -/
private lemma lazyShrinkAux_R_le {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (1 - (1 / 2 - 9 / 100 * q)) / (1 / 2 - (1 / 2 - 9 / 100 * q)) ^ 2 ≤ 124 / q ^ 2 := by
  have e1 : (1 : ℝ) - (1 / 2 - 9 / 100 * q) = 1 / 2 + 9 / 100 * q := by ring
  have e2 : (1 / 2 : ℝ) - (1 / 2 - 9 / 100 * q) = 9 / 100 * q := by ring
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
  nlinarith

/-- Case 2, the active Blue fraction (TeX 1474–1484): if `|A_t ∩ B_t| < p_ac |B_t| +
p_ac √(|B_t| L)`, `|A_t| > p_ac n − p_ac √(n L)`, `|B_t| ≤ (1/2 − 0.1 q) n` and
`150 √(n L) ≤ q n`, then `|A_t ∩ B_t| ≤ (1/2 − 0.09 q) |A_t|`, and `|A_t| > p_ac n / 2`. -/
private lemma lazyShrinkAux_case2_frac {n L pac q Bc AB m : ℝ} (hpac0 : 0 < pac) (hq0 : 0 < q)
    (hq1 : q ≤ 1) (hn0 : 0 ≤ n) (hL : 0 < L) (hbprime : 150 * Real.sqrt (n * L) ≤ q * n)
    (hB1 : Bc ≤ (1 / 2 - 1 / 10 * q) * n) (hBn : Bc ≤ n)
    (h2a : AB < pac * Bc + pac * Real.sqrt (Bc * L))
    (h2b : pac * n - pac * Real.sqrt (n * L) < m) :
    AB ≤ (1 / 2 - 9 / 100 * q) * m ∧ pac * n / 2 < m := by
  have hsqnL0 : 0 ≤ Real.sqrt (n * L) := Real.sqrt_nonneg _
  have hqn : q * n ≤ n := mul_le_of_le_one_left hn0 hq1
  have hsqnL : Real.sqrt (n * L) ≤ n / 150 := by linarith
  have hmhalf : pac * n / 2 < m := by
    have := mul_le_mul_of_nonneg_left hsqnL hpac0.le
    have : 0 ≤ pac * n := mul_nonneg hpac0.le hn0
    linarith
  refine ⟨?_, hmhalf⟩
  have hsqBL : Real.sqrt (Bc * L) ≤ Real.sqrt (n * L) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hBn hL.le)
  have hb0 : 0 < 1 / 2 - 9 / 100 * q := by linarith
  have h1 : (1 / 2 - 9 / 100 * q) * (pac * n - pac * Real.sqrt (n * L)) ≤
      (1 / 2 - 9 / 100 * q) * m := mul_le_mul_of_nonneg_left h2b.le hb0.le
  have h2 : pac * Bc + pac * Real.sqrt (Bc * L) ≤
      pac * ((1 / 2 - 1 / 10 * q) * n) + pac * Real.sqrt (n * L) := by
    have := mul_le_mul_of_nonneg_left hB1 hpac0.le
    have := mul_le_mul_of_nonneg_left hsqBL hpac0.le
    linarith
  have h3 : pac * ((1 / 2 - 1 / 10 * q) * n) + pac * Real.sqrt (n * L) ≤
      (1 / 2 - 9 / 100 * q) * (pac * n - pac * Real.sqrt (n * L)) := by
    have : pac * (3 / 2 * Real.sqrt (n * L)) ≤ pac * (1 / 100 * q * n) :=
      mul_le_mul_of_nonneg_left (by linarith) hpac0.le
    have h0 : 0 ≤ q * pac * Real.sqrt (n * L) := by positivity
    linarith
  linarith

/-- Case 2, the active vertices that are Blue in the hypothetical step (TeX 1485–1489): from the
bound of Lemma 2.5 (`lazyShrinkAux_lemma2_5_bound`, `b = 1/2 − 0.09 q`) on the active subgraph,
`(C √(pm) + p)² ≤ (C + 1)² p m`, `(1 − b)/(1/2 − b)² ≤ 124/q²`,
`|A_t ∩ B_t| ≤ p_ac |B_t| (3/2 + 1/α)` (as `|B_t| > α L/2`) and `m > p_ac n / 2` give
`X ≤ (C'/(p n)) |B_t| ≤ p_ac |B_t| / 20` once `p p_ac n ≥ L ≥ Γ`. -/
private lemma lazyShrinkAux_case2_count {n p pac q α α' C L m Bc AB X : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) (hpac0 : 0 < pac) (hq0 : 0 < q) (hq1 : q ≤ 1) (hα0 : 0 < α) (hα'0 : 0 < α')
    (hC : 0 ≤ C) (hL : 0 < L) (hLpn : L ≤ p * pac * n)
    (hΓ : 4960 * (C + 1) ^ 2 * (3 / 2 + 1 / α) / (α' ^ 2 * q ^ 2) ≤ L)
    (hB2 : α * L / 2 < Bc) (hmhalf : pac * n / 2 < m) (hm1 : 1 ≤ m) (hX0 : 0 ≤ X)
    (hAB0 : 0 ≤ AB) (h2a : AB < pac * Bc + pac * Real.sqrt (Bc * L))
    (h25 : X * (α' * p * m) ^ 2 ≤ (C * Real.sqrt (p * m) + p) ^ 2 *
      ((1 - (1 / 2 - 9 / 100 * q)) / (1 / 2 - (1 / 2 - 9 / 100 * q)) ^ 2) * AB) :
    X ≤ pac * Bc / 20 := by
  have hBc0 : 0 < Bc := lt_of_le_of_lt (by positivity) hB2
  have hm0 : 0 < m := by linarith
  have hnpos : 0 < n := by
    by_contra h
    push Not at h
    have : L ≤ 0 := hLpn.trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) h)
    linarith
  -- `(C √(pm) + p)² ≤ (C + 1)² p m`
  have hpm0 : 0 < p * m := mul_pos hp0 hm0
  have hsqpm := Real.sq_sqrt hpm0.le
  have hp_le : p ≤ Real.sqrt (p * m) := by
    rw [Real.le_sqrt hp0.le hpm0.le, sq]
    exact mul_le_mul_of_nonneg_left (hp1.trans hm1) hp0.le
  have hCsq : (C * Real.sqrt (p * m) + p) ^ 2 ≤ (C + 1) ^ 2 * (p * m) := by
    have h1 : C * Real.sqrt (p * m) + p ≤ (C + 1) * Real.sqrt (p * m) := by linarith
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    rw [mul_pow, hsqpm] at h2
    exact h2
  -- `(1 − b)/(1/2 − b)² ≤ 124/q²`
  have hR := lazyShrinkAux_R_le hq0 hq1
  have hR0 : 0 ≤ (1 - (1 / 2 - 9 / 100 * q)) / (1 / 2 - (1 / 2 - 9 / 100 * q)) ^ 2 := by
    apply div_nonneg
    · linarith
    · exact sq_nonneg _
  -- `|A ∩ B| ≤ p_ac |B| (3/2 + 1/α)`
  have hsqrt := lazyShrinkAux_sqrt_le hα0 hBc0.le hL.le hB2
  have hABc : AB ≤ pac * Bc * (3 / 2 + 1 / α) := by
    have := mul_le_mul_of_nonneg_left hsqrt hpac0.le
    have e : pac * (Bc * (1 / 2 + 1 / α)) = pac * Bc * (1 / 2 + 1 / α) := by ring
    have e2 : pac * Bc * (3 / 2 + 1 / α) = pac * Bc + pac * Bc * (1 / 2 + 1 / α) := by ring
    rw [e] at this
    rw [e2]
    linarith
  -- combine
  have key1 : X * (α' * p * m) ^ 2 ≤
      (C + 1) ^ 2 * (p * m) * (124 / q ^ 2) * (pac * Bc * (3 / 2 + 1 / α)) := by
    refine h25.trans ?_
    gcongr
  have key2 : X * (α' ^ 2 * p * m) ≤
      (C + 1) ^ 2 * (124 / q ^ 2) * (pac * Bc * (3 / 2 + 1 / α)) := by
    have e : X * (α' * p * m) ^ 2 = (X * (α' ^ 2 * p * m)) * (p * m) := by ring
    have e2 : (C + 1) ^ 2 * (p * m) * (124 / q ^ 2) * (pac * Bc * (3 / 2 + 1 / α)) =
        ((C + 1) ^ 2 * (124 / q ^ 2) * (pac * Bc * (3 / 2 + 1 / α))) * (p * m) := by ring
    rw [e, e2] at key1
    exact le_of_mul_le_mul_right key1 hpm0
  by_contra hcon
  push Not at hcon
  have hΓ' : 4960 * (C + 1) ^ 2 * (3 / 2 + 1 / α) ≤ L * (α' ^ 2 * q ^ 2) := by
    rwa [div_le_iff₀ (by positivity)] at hΓ
  have h1 : pac * Bc / 20 * (α' ^ 2 * p * (pac * n / 2)) < X * (α' ^ 2 * p * m) := by
    have : pac * Bc / 20 * (α' ^ 2 * p * (pac * n / 2)) < X * (α' ^ 2 * p * (pac * n / 2)) :=
      mul_lt_mul_of_pos_right hcon
        (mul_pos (mul_pos (pow_pos hα'0 2) hp0) (half_pos (mul_pos hpac0 hnpos)))
    have h' : X * (α' ^ 2 * p * (pac * n / 2)) ≤ X * (α' ^ 2 * p * m) := by
      apply mul_le_mul_of_nonneg_left _ hX0
      apply mul_le_mul_of_nonneg_left hmhalf.le (by positivity)
    linarith
  have h2 : (C + 1) ^ 2 * (124 / q ^ 2) * (pac * Bc * (3 / 2 + 1 / α)) ≤
      pac * Bc / 20 * (α' ^ 2 * p * (pac * n / 2)) := by
    have e : pac * Bc / 20 * (α' ^ 2 * p * (pac * n / 2)) =
        (pac * Bc / 40) * α' ^ 2 * (p * pac * n) := by ring
    have e2 : (C + 1) ^ 2 * (124 / q ^ 2) * (pac * Bc * (3 / 2 + 1 / α)) =
        (pac * Bc / 40) * (4960 * (C + 1) ^ 2 * (3 / 2 + 1 / α)) / q ^ 2 := by
      field_simp
      ring
    rw [e, e2, div_le_iff₀ (by positivity)]
    have h3 : (pac * Bc / 40) * (4960 * (C + 1) ^ 2 * (3 / 2 + 1 / α)) ≤
        (pac * Bc / 40) * (L * (α' ^ 2 * q ^ 2)) :=
      mul_le_mul_of_nonneg_left hΓ' (by positivity)
    have h4 : (pac * Bc / 40) * (L * (α' ^ 2 * q ^ 2)) ≤
        (pac * Bc / 40) * α' ^ 2 * (p * pac * n) * q ^ 2 := by
      have : (pac * Bc / 40) * (L * (α' ^ 2 * q ^ 2)) =
          (pac * Bc / 40) * α' ^ 2 * L * q ^ 2 := by ring
      rw [this]
      gcongr
    linarith
  linarith

/-- **Case 2** (from `B_t` to `B_{t+1}`, `t ≥ 2`), on the good events: the activation counts are
within `p_ac √(|B_t| L)` and `p_ac √(n L)` of their means, the subgraph induced by the active
vertices has `‖A − 𝐄A‖ ≤ C √(pm)` and minimum degree at least `α' p m`, and the update coins
behave; then `|B_{t+1}| ≤ (1 − 0.8 p_up p_ac) |B_t|` (equation (gen-temp1)). The bound on the
active vertices that are Blue in the hypothetical step is Lemma 2.5 with Lemmas A.7 and A.4, as in
the first half of the proof of Lemma 2.6 (which the paper cites here). -/
private lemma lazyShrinkAux_case2_det {n : ℕ} (G : SimpleGraph (Fin n)) (B : Set (Fin n))
    (d : DayCoins n) {p pac pup α α' C L : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hpac0 : 0 < pac)
    (hpac1 : pac ≤ 1) (hpup0 : 0 < pup) (hpup1 : pup ≤ 1) (hα0 : 0 < α) (hα'0 : 0 < α')
    (hC : 0 ≤ C) (hL : 0 < L) (hLpn : L ≤ p * pac * n)
    (hbprime : 150 * Real.sqrt (n * L) ≤ (pup * pac) * n)
    (hΓ : 4960 * (C + 1) ^ 2 * (3 / 2 + 1 / α) / (α' ^ 2 * (pup * pac) ^ 2) ≤ L)
    (hB1 : (B.ncard : ℝ) ≤ (1 / 2 - 1 / 10 * (pup * pac)) * n)
    (hB2 : α * L / 2 < B.ncard)
    (h2a : ((actSet d ∩ B).ncard : ℝ) < pac * B.ncard + pac * Real.sqrt (B.ncard * L))
    (h2b : pac * n - pac * Real.sqrt (n * L) < (actSet d).ncard)
    (h2c_spec : specNorm (adjMat (inducedOn G (actSet d)) - meanAdj (actSet d).ncard p) ≤
      C * Real.sqrt (p * (actSet d).ncard))
    (h2c_deg : ∀ v, α' * p * (actSet d).ncard ≤ degree (inducedOn G (actSet d)) v)
    (h2d : ¬ (((actSet d ∩ hypoStep G (actSet d) B).ncard : ℝ) ≤ pac * B.ncard / 20 ∧
      1 / 10 * (pup * pac) * B.ncard ≤
        (((actSet d ∩ hypoStep G (actSet d) B) ∩ updSet d).ncard : ℝ)))
    (h2e : ¬ (((B ∩ (actSet d ∩ updSet d)).ncard : ℝ) ≤ 9 / 10 * (pup * pac) * B.ncard)) :
    ((lazyStep G (actSet d) (updSet d) B).ncard : ℝ) ≤ (1 - 8 / 10 * (pup * pac)) * B.ncard := by
  have hq0 : 0 < pup * pac := mul_pos hpup0 hpac0
  have hq1 : pup * pac ≤ 1 := by nlinarith
  obtain ⟨hAB, hmhalf⟩ := lazyShrinkAux_case2_frac hpac0 hq0 hq1 (Nat.cast_nonneg n) hL hbprime
    hB1 (lazyShrinkAux_ncard_le B) h2a h2b
  have hm1 : (1 : ℝ) ≤ (actSet d).ncard := by
    have h0 : (0 : ℝ) < (actSet d).ncard :=
      lt_of_le_of_lt (by positivity) hmhalf
    have : 0 < (actSet d).ncard := by exact_mod_cast h0
    exact_mod_cast this
  -- Lemma 2.5 on the active subgraph, with the spectral and degree bounds
  have h25 := lazyShrinkAux_lemma2_5_bound (inducedOn G (actSet d)) (enumSet (actSet d) ⁻¹' B)
    (b := 1 / 2 - 9 / 100 * (pup * pac)) (by linarith)
    (by rw [ncard_preimage_enumSet]; exact hAB) hp0.le hα'0.le h2c_spec h2c_deg
  rw [ncard_preimage_enumSet] at h25
  have hS : ((actSet d ∩ hypoStep G (actSet d) B).ncard : ℝ) ≤ pac * B.ncard / 20 := by
    rw [ncard_inter_hypoStep]
    exact lazyShrinkAux_case2_count hp0 hp1 hpac0 hq0 hq1 hα0 hα'0 hC hL hLpn hΓ hB2 hmhalf hm1
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) h2a h25
  have hSU : (((actSet d ∩ hypoStep G (actSet d) B) ∩ updSet d).ncard : ℝ) <
      1 / 10 * (pup * pac) * B.ncard := by
    by_contra h
    exact h2d ⟨hS, not_lt.1 h⟩
  have hBAU : 9 / 10 * (pup * pac) * B.ncard < ((B ∩ (actSet d ∩ updSet d)).ncard : ℝ) := by
    by_contra h
    exact h2e (not_lt.1 h)
  have hstep := lazyShrinkAux_ncard_lazyStep_le G (actSet d) (updSet d) B
  have e : (1 - 8 / 10 * (pup * pac)) * (B.ncard : ℝ) =
      B.ncard - 9 / 10 * (pup * pac) * B.ncard + 1 / 10 * (pup * pac) * B.ncard := by ring
  rw [e]
  linarith

/-! ### The bad events of one day and their probabilities -/

/-- The union bound for two events, with bounds for each. -/
private lemma lazyShrinkAux_or_le {n : ℕ} {p pac pup a b : ℝ}
    {P Q : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop}
    (hP : lazyProb n p pac pup P ≤ a) (hQ : lazyProb n p pac pup Q ≤ b) :
    lazyProb n p pac pup (fun G c => P G c ∨ Q G c) ≤ a + b :=
  (lazyProb_or_le P Q).trans (add_le_add hP hQ)

/-- The bad events of Case 1 (from `B₁` to `B₂`, with the coins `d` of day 2): an activation
count deviates from its mean by `D = (K/4) √(p_ac n / p)` or more, the subgraph induced by the
active vertices fails the conclusion of Lemma 2.4 (`a = 2`, `b = 0.3`), or an update count
deviates. -/
private def lazyShrinkAux_bad1 {n : ℕ} (p pac pup K : ℝ) (G : SimpleGraph (Fin n))
    (B : Set (Fin n)) (d : DayCoins n) : Prop :=
  pac * B.ncard + K / 4 * Real.sqrt (pac * n / p) ≤ ((actSet d ∩ B).ncard : ℝ) ∨
  ((actSet d).ncard : ℝ) ≤ pac * n - K / 4 * Real.sqrt (pac * n / p) ∨
  pac * n + K / 4 * Real.sqrt (pac * n / p) ≤ ((actSet d).ncard : ℝ) ∨
  (pac * n - K / 4 * Real.sqrt (pac * n / p) < (actSet d).ncard ∧
    ¬ ∀ B' : Set (Fin (actSet d).ncard),
      (B'.ncard : ℝ) ≤ ((actSet d).ncard : ℝ) / 2 -
        2 * (actSet d).ncard / Real.sqrt (p * (actSet d).ncard) →
        ((majorityStep (inducedOn G (actSet d)) B').ncard : ℝ) ≤ 3 / 10 * (actSet d).ncard) ∨
  (((actSet d ∩ hypoStep G (actSet d) B).ncard : ℝ) ≤ 33 / 100 * pac * n ∧
    35 / 100 * (pup * pac) * n ≤
      (((actSet d ∩ hypoStep G (actSet d) B) ∩ updSet d).ncard : ℝ)) ∨
  ((n : ℝ) / 2 - 45 / 100 * (pup * pac) * n < B.ncard ∧
    ((B ∩ (actSet d ∩ updSet d)).ncard : ℝ) ≤ 9 / 10 * (pup * pac) * B.ncard)

/-- The bad events of Case 2 (from `B_t` to `B_{t+1}`, with the coins `d` of day `t + 1`): an
activation count deviates (by `p_ac √(|B_t| L)` on `B_t`, by `p_ac √(n L)` overall), the subgraph
induced by the active vertices fails the spectral bound (Lemma A.7) or the minimum degree bound
(Lemma A.4), or an update count deviates. -/
private def lazyShrinkAux_bad2 {n : ℕ} (p pac pup α lam C L : ℝ) (G : SimpleGraph (Fin n))
    (B : Set (Fin n)) (d : DayCoins n) : Prop :=
  (α * L / 2 < B.ncard ∧
    pac * B.ncard + pac * Real.sqrt (B.ncard * L) ≤ ((actSet d ∩ B).ncard : ℝ)) ∨
  ((actSet d).ncard : ℝ) ≤ pac * n - pac * Real.sqrt (n * L) ∨
  (pac * n - pac * Real.sqrt (n * L) < (actSet d).ncard ∧
    ¬ (specNorm (adjMat (inducedOn G (actSet d)) - meanAdj (actSet d).ncard p) ≤
        C * Real.sqrt (p * (actSet d).ncard) ∧
      ∀ v, Real.exp (-(8 / (lam / 2) + 7)) * p * (actSet d).ncard ≤
        degree (inducedOn G (actSet d)) v)) ∨
  (α * L / 2 < B.ncard ∧
    ((actSet d ∩ hypoStep G (actSet d) B).ncard : ℝ) ≤ pac * B.ncard / 20 ∧
    1 / 10 * (pup * pac) * B.ncard ≤
      (((actSet d ∩ hypoStep G (actSet d) B) ∩ updSet d).ncard : ℝ)) ∨
  (α * L / 2 < B.ncard ∧
    ((B ∩ (actSet d ∩ updSet d)).ncard : ℝ) ≤ 9 / 10 * (pup * pac) * B.ncard)

/-- **Case 1, probability**: the bad events of Case 1 have probability at most the sum of the
Chernoff bounds for the activations (`e^(−Ω(K²/p))`), Lemma 2.4's `e^(−κ|A₁|)`, and the Chernoff
bounds for the updates (`e^(−Ω(p_up p_ac n))`). -/
private lemma lazyShrinkAux_case1_prob {n : ℕ} {p pac pup K κ : ℝ} {N₂₄ : ℕ}
    (h24 : ∀ m ≥ N₂₄, ∀ p : ℝ, 0 < p → p < 1 → 2 * Real.sqrt p ≤ 2 →
      3 / 10 ≤ 1 / 2 - 2 / Real.sqrt (p * m) →
      1 - Real.exp (-(κ * m)) ≤ gnpProb m p (fun G => ∀ B : Set (Fin m),
        (B.ncard : ℝ) ≤ m / 2 - 2 * m / Real.sqrt (p * m) →
          ((majorityStep G B).ncard : ℝ) ≤ 3 / 10 * m))
    (hκ : 0 < κ) (hn : 0 < n) (hp0 : 0 < p) (hp1 : p < 1) (hpac0 : 0 < pac) (hpac1 : pac ≤ 1)
    (hpup0 : 0 < pup) (hpup1 : pup ≤ 1) (hK : 0 < K)
    (hxN : (N₂₄ : ℝ) ≤ pac * n - K / 4 * Real.sqrt (pac * n / p))
    (hpx : 100 ≤ p * (pac * n - K / 4 * Real.sqrt (pac * n / p))) (B₀ : Set (Fin n)) :
    lazyProb n p pac pup (fun G c =>
      lazyShrinkAux_bad1 p pac pup K G (lazyBlueAfter G c B₀ 1) (c 1)) ≤
      Real.exp (-((K / 4 * Real.sqrt (pac * n / p)) ^ 2 /
          (2 * (pac * n + K / 4 * Real.sqrt (pac * n / p))))) +
        (Real.exp (-((K / 4 * Real.sqrt (pac * n / p)) ^ 2 / (2 * (pac * n)))) +
        (Real.exp (-((K / 4 * Real.sqrt (pac * n / p)) ^ 2 /
          (2 * (pac * n + K / 4 * Real.sqrt (pac * n / p))))) +
        (Real.exp (-(κ * (pac * n - K / 4 * Real.sqrt (pac * n / p)))) +
        (Real.exp (-(pup * pac * n / 1750)) + Real.exp (-(pup * pac * n / 4000)))))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hD : 0 < K / 4 * Real.sqrt (pac * n / p) := by positivity
  unfold lazyShrinkAux_bad1
  refine lazyShrinkAux_or_le (lazyShrinkAux_case1_act_inter hpac0 hpac1 hD B₀) ?_
  refine lazyShrinkAux_or_le (lazyShrinkAux_act_card_lower hpac0 hpac1 hD 1) ?_
  refine lazyShrinkAux_or_le (lazyShrinkAux_act_card_upper hn hpac0 hpac1 hD 1) ?_
  refine lazyShrinkAux_or_le (lazyShrinkAux_case1_graph h24 hκ hp0 hp1 hxN hpx 1) ?_
  refine lazyShrinkAux_or_le (lazyShrinkAux_case1_upd hpac0 hpup0 hpup1 hn B₀) ?_
  exact lazyShrinkAux_case1_stay hpac0 hpac1 hpup0 hpup1 B₀

/-- `α_λ ≤ 1`. -/
private lemma lazyShrinkAux_alphaDeg_le_one {lam : ℝ} (hlam : 0 < lam) : alphaDeg lam ≤ 1 := by
  unfold alphaDeg
  rw [Real.exp_le_one_iff]
  have : 0 < 8 / lam := by positivity
  linarith

/-- `α_λ ≤ λ`: `e^(−8/λ − 7) ≤ 1/(1 + 8/λ) ≤ λ`. -/
private lemma lazyShrinkAux_alphaDeg_le {lam : ℝ} (hlam : 0 < lam) : alphaDeg lam ≤ lam := by
  unfold alphaDeg
  have h1 : Real.exp (-(8 / lam + 7)) ≤ Real.exp (-(8 / lam)) := Real.exp_le_exp.2 (by linarith)
  have h2 : 8 / lam + 1 ≤ Real.exp (8 / lam) := Real.add_one_le_exp _
  have h3 : Real.exp (-(8 / lam)) * Real.exp (8 / lam) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : 0 < Real.exp (-(8 / lam)) := Real.exp_pos _
  have h5 : Real.exp (-(8 / lam)) * (8 / lam) ≤ 1 := by nlinarith
  have h6 : Real.exp (-(8 / lam)) ≤ lam / 8 := by
    rw [mul_div_assoc', div_le_iff₀ hlam] at h5
    linarith
  linarith

/-- **Case 2, probability**: the bad events of a day `t ≥ 2` have probability at most
`6 n^(−(α_λ/400) p_up p_ac)`: the Chernoff bounds for the activations are `n^(−Ω(p_ac))`, Lemmas
A.7 and A.4 fail with probability `n^(−1/2) + n^(−λ/8)`, and the Chernoff bounds for the updates
are `e^(−Ω(p_up p_ac |B_t|)) ≤ n^(−Ω(α_λ p_up p_ac))` while `|B_t| > α_λ (log n)/2`. -/
private lemma lazyShrinkAux_case2_prob {n : ℕ} {p pac pup lam C : ℝ}
    (hC : ∀ (m : ℕ) (p : ℝ), 0 < p → p ≤ 1 → 1 * Real.log m ≤ p * m →
      1 - (m : ℝ) ^ (-(1 : ℝ)) ≤
        gnpProb m p (fun G => specNorm (adjMat G - meanAdj m p) ≤ C * Real.sqrt (p * m)))
    (hn : 0 < n) (hL : 0 < Real.log n) (hp0 : 0 < p) (hp1 : p ≤ 1) (hpac0 : 0 < pac)
    (hpac1 : pac ≤ 1) (hpup0 : 0 < pup) (hpup1 : pup ≤ 1) (hlam : 0 < lam)
    (hx_size : 4 / (lam / 2) + 4 ≤ pac * n - pac * Real.sqrt (n * Real.log n))
    (hx_sqrt : Real.sqrt n ≤ pac * n - pac * Real.sqrt (n * Real.log n))
    (hx_dens : (1 + lam / 2) * Real.log n ≤ p * (pac * n - pac * Real.sqrt (n * Real.log n)))
    (B₀ : Set (Fin n)) (t : ℕ) :
    lazyProb n p pac pup (fun G c => lazyShrinkAux_bad2 p pac pup (alphaDeg lam) lam C
      (Real.log n) G (lazyBlueAfter G c B₀ t) (c t)) ≤
      6 * Real.exp (-(alphaDeg lam / 400 * (pup * pac) * Real.log n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hα0 : 0 < alphaDeg lam := Real.exp_pos _
  have hα1 := lazyShrinkAux_alphaDeg_le_one hlam
  have hαlam := lazyShrinkAux_alphaDeg_le hlam
  have hD : 0 < pac * Real.sqrt (n * Real.log n) := by positivity
  unfold lazyShrinkAux_bad2
  have h1 := lazyShrinkAux_case2_act_inter (p := p) (pup := pup) hpac0 hpac1 hα0 hα1 hL B₀ t
  have h2 := lazyShrinkAux_act_card_lower (n := n) (p := p) (pup := pup) hpac0 hpac1 hD t
  have h3 := lazyShrinkAux_case2_graph (n := n) (pac := pac) (pup := pup) hC hlam hp0 hp1 hx_size hx_sqrt
    hx_dens t
  have h4 := lazyShrinkAux_case2_upd (p := p) hpac0 hpup0 hpup1 hα0 hL.le B₀ t
  have h5 := lazyShrinkAux_case2_stay (p := p) hpac0 hpac1 hpup0 hpup1 hα0 hL.le B₀ t
  refine (lazyShrinkAux_or_le h1 (lazyShrinkAux_or_le h2 (lazyShrinkAux_or_le h3
    (lazyShrinkAux_or_le h4 h5)))).trans ?_
  set α := alphaDeg lam
  set L := Real.log n
  set q := pup * pac with hq
  have hq0 : 0 < q := mul_pos hpup0 hpac0
  have hq1 : q ≤ 1 := by nlinarith
  have hqpac : q ≤ pac := by nlinarith
  set E := Real.exp (-(α / 400 * q * L))
  have hE : ∀ x : ℝ, α / 400 * q * L ≤ x → Real.exp (-x) ≤ E := fun x hx =>
    Real.exp_le_exp.2 (neg_le_neg hx)
  have e1 : Real.exp (-(α / 8 * pac * L)) ≤ E := hE _ (by
    have : α / 400 * q * L ≤ α / 400 * pac * L := by gcongr
    have : α / 400 * pac * L ≤ α / 8 * pac * L := by gcongr; norm_num
    linarith)
  have e2 : Real.exp (-((pac * Real.sqrt (n * L)) ^ 2 / (2 * (pac * n)))) ≤ E := hE _ (by
    have e : (pac * Real.sqrt (n * L)) ^ 2 / (2 * (pac * n)) = pac * L / 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      field_simp
    rw [e]
    have : α / 400 * q * L ≤ 1 / 400 * pac * L := by gcongr
    have : 0 ≤ pac * L := mul_nonneg hpac0.le hL.le
    linarith)
  have e3 : Real.exp (-(L / 2)) ≤ E := hE _ (by
    have : α / 400 * q * L ≤ 1 / 400 * 1 * L := by gcongr
    linarith)
  have e4 : Real.exp (-(lam / 8 * L)) ≤ E := hE _ (by
    have : α / 400 * q * L ≤ lam / 400 * 1 * L := by gcongr
    have : lam / 400 * 1 * L ≤ lam / 8 * L := by
      have : 0 ≤ lam * L := by positivity
      linarith
    linarith)
  have e5 : Real.exp (-(α / 160 * q * L)) ≤ E := hE _ (by
    have : 0 ≤ α * q * L := by positivity
    linarith)
  linarith

/-! ### The iteration and the numerical estimates -/

/-- **Iteration** (TeX 1501–1510): if `|B₂| ≤ x` and, on every day `t ∈ [2, T)` with
`|B_t| ≤ x` and `|B_t| > θ`, Blue shrinks by the factor `r ∈ [0, 1]`, then `|B_{2+k}| ≤ r^k x` for
`2 + k ≤ T`, as long as Blue stays above `θ` up to day `T`. -/
private lemma lazyShrinkAux_iterate {n : ℕ} (G : SimpleGraph (Fin n)) (c : ℕ → DayCoins n)
    (B₀ : Set (Fin n)) {r x θ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {T : ℕ}
    (h2 : ((lazyBlueAfter G c B₀ 2).ncard : ℝ) ≤ x)
    (hstep : ∀ t, 2 ≤ t → t < T → ((lazyBlueAfter G c B₀ t).ncard : ℝ) ≤ x →
      θ < (lazyBlueAfter G c B₀ t).ncard →
      ((lazyBlueAfter G c B₀ (t + 1)).ncard : ℝ) ≤ r * (lazyBlueAfter G c B₀ t).ncard)
    (hθ : ∀ t, t ≤ T → θ < (lazyBlueAfter G c B₀ t).ncard) :
    ∀ k, 2 + k ≤ T → ((lazyBlueAfter G c B₀ (2 + k)).ncard : ℝ) ≤ r ^ k * x := by
  have hx : 0 ≤ x := le_trans (Nat.cast_nonneg _) h2
  intro k
  induction k with
  | zero => intro _; simpa using h2
  | succ k ih =>
    intro hk
    have hk' : 2 + k ≤ T := by omega
    have ih' := ih hk'
    have hle : ((lazyBlueAfter G c B₀ (2 + k)).ncard : ℝ) ≤ x :=
      ih'.trans (mul_le_of_le_one_left hx (pow_le_one₀ hr0 hr1))
    have hs := hstep (2 + k) (by omega) (by omega) hle (hθ (2 + k) hk')
    rw [show 2 + (k + 1) = 2 + k + 1 by omega]
    calc ((lazyBlueAfter G c B₀ (2 + k + 1)).ncard : ℝ)
        ≤ r * (lazyBlueAfter G c B₀ (2 + k)).ncard := hs
      _ ≤ r * (r ^ k * x) := mul_le_mul_of_nonneg_left ih' hr0
      _ = r ^ (k + 1) * x := by ring

/-- After `⌈2 log n / q⌉` days of shrinking by the factor `1 − 0.8 q`, fewer than one vertex of
`(1/2 − 0.1 q) n` is left. -/
private lemma lazyShrinkAux_contraction {n : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hn : 0 < n) (hL0 : 0 < Real.log n) :
    (1 - 8 / 10 * q) ^ ⌈2 * Real.log n / q⌉₊ * ((1 / 2 - 1 / 10 * q) * n) < 1 := by
  set L := Real.log n with hL
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 : 0 ≤ 1 - 8 / 10 * q := by linarith
  have hr : 1 - 8 / 10 * q ≤ Real.exp (-(8 / 10 * q)) := by
    linarith [Real.add_one_le_exp (-(8 / 10 * q))]
  set k := ⌈2 * L / q⌉₊ with hk
  have hk' : 2 * L / q ≤ k := Nat.le_ceil _
  have h1 : (1 - 8 / 10 * q) ^ k ≤ Real.exp (-(8 / 10 * q)) ^ k := pow_le_pow_left₀ hr0 hr k
  rw [← Real.exp_nat_mul] at h1
  have h2 : Real.exp (k * -(8 / 10 * q)) ≤ Real.exp (-(16 / 10 * L)) := by
    apply Real.exp_le_exp.2
    have : 2 * L ≤ k * q := by rwa [div_le_iff₀ hq0] at hk'
    nlinarith
  have hx : (1 / 2 - 1 / 10 * q) * n ≤ Real.exp L := by
    rw [hL, Real.exp_log hn']
    nlinarith
  have hx0 : 0 ≤ (1 / 2 - 1 / 10 * q) * n := by
    have : 0 ≤ 1 / 2 - 1 / 10 * q := by linarith
    positivity
  calc (1 - 8 / 10 * q) ^ k * ((1 / 2 - 1 / 10 * q) * n)
      ≤ Real.exp (-(16 / 10 * L)) * Real.exp L :=
        mul_le_mul (h1.trans h2) hx hx0 (Real.exp_pos _).le
    _ = Real.exp (-(6 / 10 * L)) := by rw [← Real.exp_add]; ring_nf
    _ < 1 := by rw [Real.exp_lt_one_iff]; linarith

/-- The activation terms of Case 1: with `D = (K/4) √(p_ac n / p) ≤ p_ac n / 10` and `K ≥ 8`,
the three Chernoff bounds sum to at most `e^(−K²/(200 p))`. -/
private lemma lazyShrinkAux_act_total {n p pac K : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hpac0 : 0 < pac) (hn : 0 < n) (hK : 8 ≤ K)
    (hDn : K / 4 * Real.sqrt (pac * n / p) ≤ pac * n / 10) :
    Real.exp (-((K / 4 * Real.sqrt (pac * n / p)) ^ 2 /
          (2 * (pac * n + K / 4 * Real.sqrt (pac * n / p))))) +
        (Real.exp (-((K / 4 * Real.sqrt (pac * n / p)) ^ 2 / (2 * (pac * n)))) +
        Real.exp (-((K / 4 * Real.sqrt (pac * n / p)) ^ 2 /
          (2 * (pac * n + K / 4 * Real.sqrt (pac * n / p)))))) ≤
      Real.exp (-(1 / 200 * K ^ 2 / p)) := by
  set D := K / 4 * Real.sqrt (pac * n / p) with hD
  have hD0 : 0 ≤ D := by positivity
  have hD2 : D ^ 2 = K ^ 2 / 16 * (pac * n / p) := by
    rw [hD, mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hpn : 0 < pac * n := mul_pos hpac0 hn
  set u := K ^ 2 / p with hu
  have hu64 : 64 ≤ u := by
    rw [hu, le_div_iff₀ hp0]; nlinarith
  have hb : 10 / 352 * u ≤ D ^ 2 / (2 * (pac * n + D)) := by
    rw [le_div_iff₀ (by positivity), hD2, hu]
    have h2D : 2 * (pac * n + D) ≤ 22 / 10 * (pac * n) := by linarith
    calc 10 / 352 * (K ^ 2 / p) * (2 * (pac * n + D))
        ≤ 10 / 352 * (K ^ 2 / p) * (22 / 10 * (pac * n)) := by gcongr
      _ = K ^ 2 / 16 * (pac * n / p) := by field_simp; ring
  have hb' : D ^ 2 / (2 * (pac * n + D)) ≤ D ^ 2 / (2 * (pac * n)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have h1 : Real.exp (-(D ^ 2 / (2 * (pac * n + D)))) ≤ Real.exp (-(10 / 352 * u)) :=
    Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (-(D ^ 2 / (2 * (pac * n)))) ≤ Real.exp (-(10 / 352 * u)) :=
    Real.exp_le_exp.2 (by linarith)
  have h6 : (3 : ℝ) ≤ Real.exp (6 / 5) := by
    have he := Real.exp_one_gt_d9
    have h7 : (1 : ℝ) / 5 + 1 ≤ Real.exp (1 / 5) := Real.add_one_le_exp (1 / 5)
    have e : Real.exp (6 / 5) = Real.exp 1 * Real.exp (1 / 5) := by
      rw [← Real.exp_add]; norm_num
    rw [e]
    nlinarith [Real.exp_pos (1 / 5 : ℝ)]
  have h3 : 3 * Real.exp (-(10 / 352 * u)) ≤ Real.exp (-(1 / 200 * K ^ 2 / p)) := by
    have e : Real.exp (-(10 / 352 * u)) =
        Real.exp (-(1 / 200 * K ^ 2 / p)) * Real.exp (-((10 / 352 - 1 / 200) * u)) := by
      rw [← Real.exp_add]; congr 1; rw [hu]; ring
    rw [e]
    have h4 : Real.exp (-((10 / 352 - 1 / 200) * u)) ≤ Real.exp (-(6 / 5)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h5 : 3 * Real.exp (-(6 / 5)) ≤ 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
      exact h6
    have hE0 : 0 < Real.exp (-(1 / 200 * K ^ 2 / p)) := Real.exp_pos _
    calc 3 * (Real.exp (-(1 / 200 * K ^ 2 / p)) * Real.exp (-((10 / 352 - 1 / 200) * u)))
        ≤ 3 * (Real.exp (-(1 / 200 * K ^ 2 / p)) * Real.exp (-(6 / 5))) := by gcongr
      _ = Real.exp (-(1 / 200 * K ^ 2 / p)) * (3 * Real.exp (-(6 / 5))) := by ring
      _ ≤ Real.exp (-(1 / 200 * K ^ 2 / p)) * 1 := by gcongr
      _ = Real.exp (-(1 / 200 * K ^ 2 / p)) := mul_one _
  linarith

/-- The union bound of the paper's last step: for `n` large,
`3 e^(−κ' q n) + (2 log n / q + 1) · 6 n^(−a q) ≤ n^(−(a/2) q)`. -/
private lemma lazyShrinkAux_final_sum {n L q a κ' : ℝ} (hq0 : 0 < q) (ha : 0 < a)
    (hκn : a * L ≤ κ' * n) (hΛ : 2 / (a * q) * (18 + 48 / (a * q ^ 2)) ≤ L) :
    3 * Real.exp (-(κ' * q * n)) + (2 * L / q + 1) * (6 * Real.exp (-(a * q * L))) ≤
      Real.exp (-(a / 2 * q * L)) := by
  have hL0 : 0 ≤ L := le_trans (by positivity) hΛ
  have h1 : Real.exp (-(κ' * q * n)) ≤ Real.exp (-(a * q * L)) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hκn hq0.le
    linarith
  have hy : 18 + 48 / (a * q ^ 2) ≤ a / 2 * q * L := by
    have h := mul_le_mul_of_nonneg_left hΛ (by positivity : (0 : ℝ) ≤ a / 2 * q)
    have e : a / 2 * q * (2 / (a * q) * (18 + 48 / (a * q ^ 2))) = 18 + 48 / (a * q ^ 2) := by
      field_simp
    linarith
  set y := a / 2 * q * L with hydef
  have hk0 : 0 ≤ 48 / (a * q ^ 2) := by positivity
  have hy1 : 1 ≤ y := by linarith
  have h12 : 12 * L / q = y * (48 / (a * q ^ 2)) / 2 := by
    rw [hydef]; field_simp; ring
  have hexp : 9 + 12 * L / q ≤ Real.exp y := by
    have hq := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ y)
    rw [h12]
    nlinarith
  have e2 : Real.exp (-(a * q * L)) = Real.exp (-y) * Real.exp (-y) := by
    rw [← Real.exp_add]; congr 1; rw [hydef]; ring
  have e3 : Real.exp (-(a / 2 * q * L)) = Real.exp (-y) := by rw [hydef]
  rw [e3]
  have hey : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (-y) := Real.exp_pos _
  calc 3 * Real.exp (-(κ' * q * n)) + (2 * L / q + 1) * (6 * Real.exp (-(a * q * L)))
      ≤ 3 * Real.exp (-(a * q * L)) + (2 * L / q + 1) * (6 * Real.exp (-(a * q * L))) := by
        gcongr
    _ = (9 + 12 * L / q) * Real.exp (-(a * q * L)) := by ring
    _ ≤ Real.exp y * Real.exp (-(a * q * L)) := by gcongr
    _ = Real.exp (-y) := by rw [e2]; nlinarith

/-! ### Assembling the proof -/

/-- The event of the proposition is contained in the union of the bad events of Case 1 and of the
bad events of Case 2 on the days `t ∈ [2, T)`: otherwise Case 1 gives
`|B₂| ≤ (1/2 − 0.1 p_up p_ac) n` (equation (main-lazy-details-temp3)), every day of Case 2 shrinks
Blue by the factor `1 − 0.8 p_up p_ac` (equation (gen-temp1)) while it has more than
`α_λ (log n)/2` vertices, and after `T − 2` such days fewer than one vertex is left. -/
private lemma lazyShrinkAux_incl {n : ℕ} (G : SimpleGraph (Fin n)) (c : ℕ → DayCoins n)
    (B₀ : Set (Fin n)) {p pac pup K lam C : ℝ} {T : ℕ}
    (hp0 : 0 < p) (hp1 : p < 1) (hpac0 : 0 < pac) (hpac1 : pac ≤ 1) (hpup0 : 0 < pup)
    (hpup1 : pup ≤ 1) (hK : 8 ≤ K) (hL : 0 < Real.log n)
    (hLpn : Real.log n ≤ p * pac * n)
    (hDn : K / 4 * Real.sqrt (pac * n / p) ≤ pac * n / 10)
    (hbprime : 150 * Real.sqrt (n * Real.log n) ≤ (pup * pac) * n)
    (hΓ : 4960 * (max C 0 + 1) ^ 2 * (3 / 2 + 1 / alphaDeg lam) /
      (Real.exp (-(8 / (lam / 2) + 7)) ^ 2 * (pup * pac) ^ 2) ≤ Real.log n)
    (hT : 2 ≤ T) (hTA : (T : ℝ) ≤ 3 * Real.log n / (pup * pac))
    (hcontr : (1 - 8 / 10 * (pup * pac)) ^ (T - 2) * ((1 / 2 - 1 / 10 * (pup * pac)) * n) < 1)
    (hE : ((lazyBlueAfter G c B₀ 1).ncard : ℝ) ≤ n / 2 - K * Real.sqrt (n / (p * pac)) ∧
      ∀ t : ℕ, (t : ℝ) ≤ 3 * Real.log n / (pup * pac) →
        alphaDeg lam * Real.log n / 2 < (lazyBlueAfter G c B₀ t).ncard) :
    lazyShrinkAux_bad1 p pac pup K G (lazyBlueAfter G c B₀ 1) (c 1) ∨
      ∃ t ∈ Finset.Ico 2 T, lazyShrinkAux_bad2 p pac pup (alphaDeg lam) lam C (Real.log n) G
        (lazyBlueAfter G c B₀ t) (c t) := by
  obtain ⟨hB1, hall⟩ := hE
  by_contra hcon
  rw [not_or, not_exists] at hcon
  obtain ⟨hb1, hb2⟩ := hcon
  have hq0 : 0 < pup * pac := mul_pos hpup0 hpac0
  have hq1 : pup * pac ≤ 1 := by nlinarith
  have hα0 : 0 < alphaDeg lam := Real.exp_pos _
  -- Case 1: `|B₂| ≤ (1/2 − 0.1 q) n`
  have h2 : ((lazyBlueAfter G c B₀ 2).ncard : ℝ) ≤ (1 / 2 - 1 / 10 * (pup * pac)) * n := by
    unfold lazyShrinkAux_bad1 at hb1
    simp only [not_or] at hb1
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hb1
    have h1b := not_le.1 n2
    have h1d : ∀ B' : Set (Fin (actSet (c 1)).ncard),
        (B'.ncard : ℝ) ≤ ((actSet (c 1)).ncard : ℝ) / 2 -
          2 * (actSet (c 1)).ncard / Real.sqrt (p * (actSet (c 1)).ncard) →
          ((majorityStep (inducedOn G (actSet (c 1))) B').ncard : ℝ) ≤
            3 / 10 * (actSet (c 1)).ncard := by
      by_contra h
      exact n4 ⟨h1b, h⟩
    rw [show (2 : ℕ) = 1 + 1 from rfl, lazyBlueAfter_succ]
    exact lazyShrinkAux_case1_det G _ (c 1) hp0 hpac0 hpac1 hpup1 hK hDn hB1
      (not_le.1 n1) h1b (not_le.1 n3) h1d n5 n6
  -- Case 2: `|B_{t+1}| ≤ (1 − 0.8 q) |B_t|`
  have hstep : ∀ t, 2 ≤ t → t < T →
      ((lazyBlueAfter G c B₀ t).ncard : ℝ) ≤ (1 / 2 - 1 / 10 * (pup * pac)) * n →
      alphaDeg lam * Real.log n / 2 < (lazyBlueAfter G c B₀ t).ncard →
      ((lazyBlueAfter G c B₀ (t + 1)).ncard : ℝ) ≤
        (1 - 8 / 10 * (pup * pac)) * (lazyBlueAfter G c B₀ t).ncard := by
    intro t ht2 htT hx hθ
    have hb := hb2 t
    rw [not_and] at hb
    have hb' := hb (Finset.mem_Ico.2 ⟨ht2, htT⟩)
    unfold lazyShrinkAux_bad2 at hb'
    simp only [not_or] at hb'
    obtain ⟨n1, n2, n3, n4, n5⟩ := hb'
    have h2a : ((actSet (c t) ∩ lazyBlueAfter G c B₀ t).ncard : ℝ) <
        pac * (lazyBlueAfter G c B₀ t).ncard +
          pac * Real.sqrt ((lazyBlueAfter G c B₀ t).ncard * Real.log n) :=
      not_le.1 fun h => n1 ⟨hθ, h⟩
    have h2b := not_le.1 n2
    have h2c : specNorm (adjMat (inducedOn G (actSet (c t))) -
          meanAdj (actSet (c t)).ncard p) ≤ C * Real.sqrt (p * (actSet (c t)).ncard) ∧
        ∀ v, Real.exp (-(8 / (lam / 2) + 7)) * p * (actSet (c t)).ncard ≤
          degree (inducedOn G (actSet (c t))) v := by
      by_contra h
      exact n3 ⟨h2b, h⟩
    rw [lazyBlueAfter_succ]
    exact lazyShrinkAux_case2_det G _ (c t) hp0 hp1.le hpac0 hpac1 hpup0 hpup1 hα0
      (Real.exp_pos _) (le_max_right C 0) hL hLpn hbprime hΓ hx hθ h2a h2b
      (h2c.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))) h2c.2
      (fun h => n4 ⟨hθ, h⟩) (fun h => n5 ⟨hθ, h⟩)
  -- iteration up to day `T`
  have hθ : ∀ t, t ≤ T → alphaDeg lam * Real.log n / 2 < (lazyBlueAfter G c B₀ t).ncard :=
    fun t ht => hall t (le_trans (by exact_mod_cast ht) hTA)
  have hit := lazyShrinkAux_iterate G c B₀ (by linarith) (by linarith) h2 hstep hθ (T - 2)
    (by omega)
  rw [show 2 + (T - 2) = T by omega] at hit
  have hlt : ((lazyBlueAfter G c B₀ T).ncard : ℝ) < 1 := hit.trans_lt hcontr
  have hzero : (lazyBlueAfter G c B₀ T).ncard = 0 := by
    have : (lazyBlueAfter G c B₀ T).ncard < 1 := by exact_mod_cast hlt
    omega
  have h0 := hθ T le_rfl
  rw [hzero, Nat.cast_zero] at h0
  have : 0 ≤ alphaDeg lam * Real.log n := mul_nonneg hα0.le hL.le
  linarith

/-- `√(x L) ≤ c x` when `L / x ≤ c²`. -/
private lemma lazyShrinkAux_sqrt_mul_le {x L c : ℝ} (hx : 0 < x) (hc : 0 ≤ c)
    (h : L / x ≤ c ^ 2) : Real.sqrt (x * L) ≤ c * x := by
  rw [div_le_iff₀ hx] at h
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith

/-- Case 1: `D = (K/4) √(p_ac n / p) ≤ p_ac n / 10` once `K² ≤ (4/25) log n ≤ (4/25) p p_ac n`. -/
private lemma lazyShrinkAux_Dn {n p pac K : ℝ} (hn : 0 < n) (hp0 : 0 < p) (hpac0 : 0 < pac)
    (hK2 : 25 / 4 * K ^ 2 ≤ p * pac * n) :
    K / 4 * Real.sqrt (pac * n / p) ≤ pac * n / 10 := by
  have hpn : 0 < pac * n := mul_pos hpac0 hn
  have hD2 : (K / 4 * Real.sqrt (pac * n / p)) ^ 2 = K ^ 2 / 16 * (pac * n / p) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  rcases le_or_gt K 0 with hK | hK
  · have : K / 4 * Real.sqrt (pac * n / p) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _)
    linarith [div_pos hpn (by norm_num : (0 : ℝ) < 10)]
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
  rw [hD2, div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 := mul_le_mul_of_nonneg_left hK2 hpn.le
  nlinarith

/-- Case 2: `p (p_ac n − p_ac √(n log n)) ≥ (1 + λ/2) log n` when
`(1 + λ) √(n log n) ≤ (λ/2) n` and `p p_ac n ≥ (1 + λ) log n`. -/
private lemma lazyShrinkAux_xdens {n L p pac lam : ℝ} (hp0 : 0 < p) (hpac0 : 0 < pac)
    (hlam : 0 < lam) (hlog : (1 + lam) * L ≤ p * pac * n)
    (hdens : (1 + lam) * Real.sqrt (n * L) ≤ lam / 2 * n) :
    (1 + lam / 2) * L ≤ p * (pac * n - pac * Real.sqrt (n * L)) := by
  have h1 : (1 + lam / 2) * n ≤ (1 + lam) * (n - Real.sqrt (n * L)) := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ p * pac)
  have h3 : (1 + lam) * ((1 + lam / 2) * L) ≤ (1 + lam) *
      (p * (pac * n - pac * Real.sqrt (n * L))) := by
    have e : (1 + lam) * (p * (pac * n - pac * Real.sqrt (n * L))) =
        p * pac * ((1 + lam) * (n - Real.sqrt (n * L))) := by ring
    rw [e]
    have e2 : (1 + lam) * ((1 + lam / 2) * L) = (1 + lam / 2) * ((1 + lam) * L) := by ring
    rw [e2]
    have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 1 + lam / 2)
    linarith
  exact le_of_mul_le_mul_left h3 (by positivity)

/-- The last day considered, `T = ⌈2 log n / q⌉ + 2`, is at most `3 log n / q`. -/
private lemma lazyShrinkAux_TA {L q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hL : 3 ≤ L) :
    ((⌈2 * L / q⌉₊ + 2 : ℕ) : ℝ) ≤ 3 * L / q := by
  have hceil : (⌈2 * L / q⌉₊ : ℝ) < 2 * L / q + 1 := Nat.ceil_lt_add_one (by positivity)
  push_cast
  have h3 : 3 ≤ L / q := by
    rw [le_div_iff₀ hq0]; nlinarith
  have e : 3 * L / q = 2 * L / q + L / q := by ring
  linarith

/-- Case 1: the bounds `e^(−κ(p_ac n − D))`, `e^(−q n/1750)`, `e^(−q n/4000)` are at most
`e^(−κ' q n)` with `κ' = min(0.9 κ, 1/4000)`. -/
private lemma lazyShrinkAux_case1_rest {n pac pup κ D : ℝ} (hn : 0 < n) (hpac0 : 0 < pac)
    (hpup0 : 0 < pup) (hpup1 : pup ≤ 1) (hκ : 0 < κ)
    (hDn : D ≤ pac * n / 10) :
    Real.exp (-(κ * (pac * n - D))) + (Real.exp (-(pup * pac * n / 1750)) +
        Real.exp (-(pup * pac * n / 4000))) ≤
      3 * Real.exp (-(min (9 / 10 * κ) (1 / 4000) * (pup * pac) * n)) := by
  set κ' := min (9 / 10 * κ) (1 / 4000) with hκ'
  have hκ'0 : 0 < κ' := lt_min (by positivity) (by norm_num)
  have hκ'1 : κ' ≤ 9 / 10 * κ := min_le_left _ _
  have hκ'2 : κ' ≤ 1 / 4000 := min_le_right _ _
  have hqpac : pup * pac ≤ pac := by nlinarith
  have hqn : 0 ≤ pup * pac * n := by positivity
  have hE1 : Real.exp (-(κ * (pac * n - D))) ≤ Real.exp (-(κ' * (pup * pac) * n)) := by
    apply Real.exp_le_exp.2
    have h1 : 9 / 10 * (pac * n) ≤ pac * n - D := by linarith
    have h2 : κ' * (pup * pac * n) ≤ 9 / 10 * κ * (pac * n) :=
      mul_le_mul hκ'1 (mul_le_mul_of_nonneg_right hqpac hn.le) hqn (by positivity)
    have h3 := mul_le_mul_of_nonneg_left h1 hκ.le
    have e : κ' * (pup * pac) * n = κ' * (pup * pac * n) := by ring
    have e2 : κ * (9 / 10 * (pac * n)) = 9 / 10 * κ * (pac * n) := by ring
    linarith
  have hE2 : Real.exp (-(pup * pac * n / 1750)) ≤ Real.exp (-(κ' * (pup * pac) * n)) := by
    apply Real.exp_le_exp.2
    have h1 := mul_le_mul_of_nonneg_right hκ'2 hqn
    have e : κ' * (pup * pac) * n = κ' * (pup * pac * n) := by ring
    linarith
  have hE3 : Real.exp (-(pup * pac * n / 4000)) ≤ Real.exp (-(κ' * (pup * pac) * n)) := by
    apply Real.exp_le_exp.2
    have h1 := mul_le_mul_of_nonneg_right hκ'2 hqn
    have e : κ' * (pup * pac) * n = κ' * (pup * pac * n) := by ring
    linarith
  linarith

/-- The union bound over the days `t ∈ [2, T)`, `T − 2 = ⌈2 log n / q⌉ ≤ 2 log n / q + 1`. -/
private lemma lazyShrinkAux_sum_days {L q E : ℝ} (hq0 : 0 < q) (hL : 0 ≤ L) (hE : 0 ≤ E) :
    ∑ _t ∈ Finset.Ico 2 (⌈2 * L / q⌉₊ + 2), E ≤ (2 * L / q + 1) * E := by
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, show ⌈2 * L / q⌉₊ + 2 - 2 = ⌈2 * L / q⌉₊
    by omega]
  exact mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (by positivity)).le hE

/-- **The bound of the proposition** for `n` large (in the form of the explicit conditions that
the proof uses). -/
private lemma lazyShrinkAux_bound {n : ℕ} {p pac pup K lam κ C : ℝ} {N₂₄ : ℕ}
    (B₀ : Set (Fin n))
    (h24 : ∀ m ≥ N₂₄, ∀ p : ℝ, 0 < p → p < 1 → 2 * Real.sqrt p ≤ 2 →
      3 / 10 ≤ 1 / 2 - 2 / Real.sqrt (p * m) →
      1 - Real.exp (-(κ * m)) ≤ gnpProb m p (fun G => ∀ B : Set (Fin m),
        (B.ncard : ℝ) ≤ m / 2 - 2 * m / Real.sqrt (p * m) →
          ((majorityStep G B).ncard : ℝ) ≤ 3 / 10 * m))
    (hC : ∀ (m : ℕ) (p : ℝ), 0 < p → p ≤ 1 → 1 * Real.log m ≤ p * m →
      1 - (m : ℝ) ^ (-(1 : ℝ)) ≤
        gnpProb m p (fun G => specNorm (adjMat G - meanAdj m p) ≤ C * Real.sqrt (p * m)))
    (hκ : 0 < κ) (hn : 0 < n) (hp0 : 0 < p) (hp1 : p < 1) (hpac0 : 0 < pac) (hpac1 : pac ≤ 1)
    (hpup0 : 0 < pup) (hpup1 : pup ≤ 1) (hK : 8 ≤ K) (hlam : 0 < lam)
    (hL112 : 112 ≤ Real.log n) (hlog : (1 + lam) * Real.log n ≤ p * pac * n)
    (hK2 : 25 / 4 * K ^ 2 ≤ Real.log n) (hN24 : (N₂₄ : ℝ) ≤ 9 / 10 * pac * n)
    (hsize : 4 / (lam / 2) + 4 ≤ pac * n / 2) (hsqrtn : Real.sqrt n ≤ pac * n / 2)
    (hΓ : 4960 * (max C 0 + 1) ^ 2 * (3 / 2 + 1 / alphaDeg lam) /
      (Real.exp (-(8 / (lam / 2) + 7)) ^ 2 * (pup * pac) ^ 2) ≤ Real.log n)
    (hΛ : 2 / (alphaDeg lam / 400 * (pup * pac)) *
      (18 + 48 / (alphaDeg lam / 400 * (pup * pac) ^ 2)) ≤ Real.log n)
    (hb' : 150 * Real.sqrt (n * Real.log n) ≤ pup * pac * n)
    (hdens : (1 + lam) * Real.sqrt (n * Real.log n) ≤ lam / 2 * n)
    (hκn : alphaDeg lam / 400 * Real.log n ≤ min (9 / 10 * κ) (1 / 4000) * n) :
    lazyProb n p pac pup (fun G c =>
          ((lazyBlueAfter G c B₀ 1).ncard : ℝ) ≤ n / 2 - K * Real.sqrt (n / (p * pac)) ∧
          ∀ t : ℕ, (t : ℝ) ≤ 3 * Real.log n / (pup * pac) →
            alphaDeg lam * Real.log n / 2 < (lazyBlueAfter G c B₀ t).ncard) ≤
      Real.exp (-(1 / 200 * K ^ 2 / p)) + (n : ℝ) ^ (-(alphaDeg lam / 800 * pup * pac)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hL0 : 0 < Real.log n := by linarith
  have hq0 : 0 < pup * pac := mul_pos hpup0 hpac0
  have hq1 : pup * pac ≤ 1 := by nlinarith
  have hLpn : Real.log n ≤ p * pac * n := by nlinarith
  have hDn := lazyShrinkAux_Dn (K := K) hn' hp0 hpac0 (by linarith)
  have hxN : (N₂₄ : ℝ) ≤ pac * n - K / 4 * Real.sqrt (pac * n / p) := by linarith
  have hpx : 100 ≤ p * (pac * n - K / 4 * Real.sqrt (pac * n / p)) := by
    have h1 : 9 / 10 * (pac * n) ≤ pac * n - K / 4 * Real.sqrt (pac * n / p) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hp0.le
    have e : p * (9 / 10 * (pac * n)) = 9 / 10 * (p * pac * n) := by ring
    linarith
  have hsqnL : Real.sqrt (n * Real.log n) ≤ n / 150 := by
    have : pup * pac * n ≤ n := mul_le_of_le_one_left hn'.le hq1
    linarith
  have hx_half : pac * n / 2 ≤ pac * n - pac * Real.sqrt (n * Real.log n) := by
    have := mul_le_mul_of_nonneg_left hsqnL hpac0.le
    linarith
  have hx_dens := lazyShrinkAux_xdens hp0 hpac0 hlam hlog hdens
  have hTA := lazyShrinkAux_TA hq0 hq1 (by linarith : (3 : ℝ) ≤ Real.log n)
  have hcontr : (1 - 8 / 10 * (pup * pac)) ^ (⌈2 * Real.log n / (pup * pac)⌉₊ + 2 - 2) *
      ((1 / 2 - 1 / 10 * (pup * pac)) * n) < 1 := by
    rw [show ⌈2 * Real.log n / (pup * pac)⌉₊ + 2 - 2 = ⌈2 * Real.log n / (pup * pac)⌉₊
      by omega]
    exact lazyShrinkAux_contraction hq0 hq1 hn hL0
  have hcase1 := lazyShrinkAux_case1_prob h24 hκ hn hp0 hp1 hpac0 hpac1 hpup0 hpup1
    (by linarith) hxN hpx B₀
  have hcase2 := fun t => lazyShrinkAux_case2_prob (C := C) (B₀ := B₀) (t := t) hC hn hL0
    hp0 hp1.le hpac0 hpac1 hpup0 hpup1 hlam (hsize.trans hx_half) (hsqrtn.trans hx_half) hx_dens
  have hact := lazyShrinkAux_act_total hp0 hp1.le hpac0 hn' hK hDn
  have hrest := lazyShrinkAux_case1_rest hn' hpac0 hpup0 hpup1 hκ hDn
  have hsum := lazyShrinkAux_sum_days hq0 hL0.le
    (by positivity : (0 : ℝ) ≤ 6 * Real.exp (-(alphaDeg lam / 400 * (pup * pac) * Real.log n)))
  have hα0 : 0 < alphaDeg lam := Real.exp_pos _
  have hfinal := lazyShrinkAux_final_sum (n := n) (κ' := min (9 / 10 * κ) (1 / 4000)) hq0
    (div_pos hα0 (by norm_num) : 0 < alphaDeg lam / 400) hκn hΛ
  have hsum2 := Finset.sum_le_sum fun t (_ : t ∈ Finset.Ico 2 (⌈2 * Real.log n / (pup * pac)⌉₊ + 2))
    => hcase2 t
  have hincl := lazyProb_mono (n := n) (p := p) (pac := pac) (pup := pup)
    (fun G c hE => lazyShrinkAux_incl G c B₀ hp0 hp1 hpac0 hpac1 hpup0 hpup1 hK
      hL0 hLpn hDn hb' hΓ (by omega) hTA hcontr hE)
  have hunion : lazyProb n p pac pup (fun G c =>
        lazyShrinkAux_bad1 p pac pup K G (lazyBlueAfter G c B₀ 1) (c 1) ∨
        ∃ t ∈ Finset.Ico 2 (⌈2 * Real.log n / (pup * pac)⌉₊ + 2),
          lazyShrinkAux_bad2 p pac pup (alphaDeg lam) lam C (Real.log n) G
            (lazyBlueAfter G c B₀ t) (c t)) ≤
      lazyProb n p pac pup (fun G c =>
        lazyShrinkAux_bad1 p pac pup K G (lazyBlueAfter G c B₀ 1) (c 1)) +
      ∑ t ∈ Finset.Ico 2 (⌈2 * Real.log n / (pup * pac)⌉₊ + 2), lazyProb n p pac pup
        (fun G c => lazyShrinkAux_bad2 p pac pup (alphaDeg lam) lam C (Real.log n) G
          (lazyBlueAfter G c B₀ t) (c t)) :=
    (lazyProb_or_le _ _).trans (add_le_add_right (lazyProb_exists_le _ _) _)
  have hrpow : (n : ℝ) ^ (-(alphaDeg lam / 800 * pup * pac)) =
      Real.exp (-(alphaDeg lam / 400 / 2 * (pup * pac) * Real.log n)) := by
    rw [Real.rpow_def_of_pos hn']
    congr 1
    ring
  rw [hrpow]
  refine hincl.trans (hunion.trans ?_)
  linarith

/-- The bound of the proposition from the thresholds that `n` exceeds (`log n ≥ M`, `n ≥ M`,
`(log n)/n ≤ ε` for the `M` and `ε` of the proof): the conditions of `lazyShrinkAux_bound`. -/
private lemma lazyShrinkAux_bound_of_large {n : ℕ} {p pac pup K lam κ C : ℝ} {N₂₄ : ℕ}
    (B₀ : Set (Fin n))
    (h24 : ∀ m ≥ N₂₄, ∀ p : ℝ, 0 < p → p < 1 → 2 * Real.sqrt p ≤ 2 →
      3 / 10 ≤ 1 / 2 - 2 / Real.sqrt (p * m) →
      1 - Real.exp (-(κ * m)) ≤ gnpProb m p (fun G => ∀ B : Set (Fin m),
        (B.ncard : ℝ) ≤ m / 2 - 2 * m / Real.sqrt (p * m) →
          ((majorityStep G B).ncard : ℝ) ≤ 3 / 10 * m))
    (hC : ∀ (m : ℕ) (p : ℝ), 0 < p → p ≤ 1 → 1 * Real.log m ≤ p * m →
      1 - (m : ℝ) ^ (-(1 : ℝ)) ≤
        gnpProb m p (fun G => specNorm (adjMat G - meanAdj m p) ≤ C * Real.sqrt (p * m)))
    (hκ : 0 < κ) (hp0 : 0 < p) (hpac0 : 0 < pac) (hpac1 : pac ≤ 1) (hpup0 : 0 < pup)
    (hpup1 : pup ≤ 1) (hK : 8 ≤ K) (hlam : 0 < lam)
    (hlog : (1 + lam) * Real.log n ≤ p * pac * n) (h10 : 10 ≤ (1 - p) * pac * n)
    (hK2 : 25 / 4 * K ^ 2 ≤ Real.log n) (hL112 : 112 ≤ Real.log n)
    (hΓ : 4960 * (max C 0 + 1) ^ 2 * (3 / 2 + 1 / alphaDeg lam) /
      (Real.exp (-(8 / (lam / 2) + 7)) ^ 2 * (pup * pac) ^ 2) ≤ Real.log n)
    (hΛ : 2 / (alphaDeg lam / 400 * (pup * pac)) *
      (18 + 48 / (alphaDeg lam / 400 * (pup * pac) ^ 2)) ≤ Real.log n)
    (hN24 : (N₂₄ : ℝ) / (9 / 10 * pac) ≤ n) (h112n : (112 : ℝ) ≤ n)
    (hsz : 2 * (4 / (lam / 2) + 4) / pac ≤ n) (hsq : 4 / pac ^ 2 ≤ n)
    (hε1 : Real.log n / n ≤ (pup * pac / 150) ^ 2)
    (hε2 : Real.log n / n ≤ (lam / (2 * (1 + lam))) ^ 2)
    (hε3 : Real.log n / n ≤ min (9 / 10 * κ) (1 / 4000) / (alphaDeg lam / 400)) :
    lazyProb n p pac pup (fun G c =>
          ((lazyBlueAfter G c B₀ 1).ncard : ℝ) ≤ n / 2 - K * Real.sqrt (n / (p * pac)) ∧
          ∀ t : ℕ, (t : ℝ) ≤ 3 * Real.log n / (pup * pac) →
            alphaDeg lam * Real.log n / 2 < (lazyBlueAfter G c B₀ t).ncard) ≤
      Real.exp (-(1 / 200 * K ^ 2 / p)) + (n : ℝ) ^ (-(alphaDeg lam / 800 * pup * pac)) := by
  have hn' : (0 : ℝ) < n := by linarith
  have hn0 : 0 < n := by exact_mod_cast hn'
  have hα0 : 0 < alphaDeg lam := Real.exp_pos _
  have ha0 : 0 < alphaDeg lam / 400 := div_pos hα0 (by norm_num)
  have hp1 : p < 1 := by
    by_contra h
    push Not at h
    have h1 : 0 ≤ (p - 1) * (pac * n) := mul_nonneg (by linarith) (by positivity)
    nlinarith
  have hsqnL := lazyShrinkAux_sqrt_mul_le hn' (by positivity) hε1
  have hsqnL2 := lazyShrinkAux_sqrt_mul_le hn' (by positivity) hε2
  refine lazyShrinkAux_bound B₀ h24 hC hκ hn0 hp0 hp1 hpac0 hpac1 hpup0 hpup1 hK hlam hL112
    hlog hK2 ?_ ?_ ?_ hΓ hΛ ?_ ?_ ?_
  · rw [div_le_iff₀ (by positivity)] at hN24
    linarith
  · rw [div_le_iff₀ hpac0] at hsz
    linarith
  · rw [div_le_iff₀ (by positivity)] at hsq
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have := mul_le_mul_of_nonneg_left hsq hn'.le
    nlinarith
  · have e : pup * pac / 150 * n * 150 = pup * pac * n := by ring
    linarith
  · have e : (1 + lam) * (lam / (2 * (1 + lam)) * n) = lam / 2 * n := by
      field_simp
    have := mul_le_mul_of_nonneg_left hsqnL2 (by positivity : (0 : ℝ) ≤ 1 + lam)
    linarith
  · rw [div_le_iff₀ hn'] at hε3
    have h := mul_le_mul_of_nonneg_left hε3 ha0.le
    have e : alphaDeg lam / 400 * (min (9 / 10 * κ) (1 / 4000) / (alphaDeg lam / 400) * n) =
        min (9 / 10 * κ) (1 / 4000) * n := by
      field_simp
    linarith

/-- For every `M` and `ε > 0`, eventually `log n ≥ M`, `n ≥ M` and `(log n)/n ≤ ε`. -/
private lemma lazyShrinkAux_eventually (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, M ≤ Real.log n ∧ M ≤ n ∧ Real.log n / n ≤ ε := by
  have h1 : Filter.Tendsto (fun n : ℕ => Real.log n) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h3 : Filter.Tendsto (fun n : ℕ => Real.log n / n) Filter.atTop (nhds 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    refine this.congr fun n => ?_
    simp
  exact (h1.eventually_ge_atTop M).and
    (((tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop M).and
      (h3.eventually (ge_mem_nhds hε)))

/-- **Proposition 4.3** (`S:prop:main-lazy-details-prop2`). Under the assumptions of Theorem 4.1
and `|B₁| ≤ n/2 − K √(n / (p p_ac))`, for every `K ≥ 8` there is `t*₁ = O(p_up⁻¹ p_ac⁻¹ log n)`
such that, with probability at least `1 − e^(−Ω(K² p⁻¹)) − n^(−Ω(p_up p_ac))`,
`|B_{t*₁}| ≤ α_λ (log n) / 2`.

Readings: the probability that `|B₁|` satisfies the assumption and every `B_t`,
`t ≤ A log n / (p_up p_ac)`, has more than `α_λ (log n)/2` vertices is at most
`e^(−c₁ K² / p) + n^(−c₂ p_up p_ac)`; the statement's "for every `ε > 0`" is unused.

Proof: the paper's (see the module docstring), with `A = 3`, `c₁ = 1/200` and `c₂ = α_λ/800`.
In Case 2 the paper cites Lemma 2.6 (`S:lem:step3`) for the bound on the active vertices that are
Blue in the hypothetical step; that bound is the first half of Lemma 2.6's proof, Lemma 2.5 with
Lemmas A.7 and A.4 on the subgraph induced by the active vertices, which the proof uses directly.
-/
theorem proposition4_3 :
    ∃ A c₁ : ℝ, 0 < c₁ ∧ ∀ K lam : ℝ, 8 ≤ K → 0 < lam →
      ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ pac pup : ℝ, 0 < pac → pac ≤ 1 → 0 < pup → pup ≤ 1 →
      ∃ N : ℕ, ∀ n ≥ N, ∀ (p : ℝ) (B₀ : Set (Fin n)), 0 < p →
        (1 + lam) * Real.log n ≤ p * pac * n → 10 ≤ (1 - p) * pac * n →
        lazyProb n p pac pup (fun G c =>
          ((lazyBlueAfter G c B₀ 1).ncard : ℝ) ≤ n / 2 - K * Real.sqrt (n / (p * pac)) ∧
          ∀ t : ℕ, (t : ℝ) ≤ A * Real.log n / (pup * pac) →
            alphaDeg lam * Real.log n / 2 < (lazyBlueAfter G c B₀ t).ncard) ≤
          Real.exp (-(c₁ * K ^ 2 / p)) + (n : ℝ) ^ (-(c₂ * pup * pac)) := by
  -- Lemma 2.4 with `a = 2`, `b = 0.3` (Case 1)
  obtain ⟨κ, hκ, N₂₄, h24⟩ := lemma2_4 (a := 2) (b := 3 / 10) (by norm_num) (by norm_num)
    (by norm_num) (by have := Real.log_two_lt_d9; norm_num at this ⊢; linarith)
  -- Lemma A.7 with `c = a = 1` (Case 2)
  obtain ⟨C, hC⟩ := lemmaA_7 (c := 1) (a := 1) one_pos one_pos
  refine ⟨3, 1 / 200, by norm_num, fun K lam hK hlam => ?_⟩
  have hα0 : 0 < alphaDeg lam := Real.exp_pos _
  refine ⟨alphaDeg lam / 800, div_pos hα0 (by norm_num),
    fun pac pup hpac0 hpac1 hpup0 hpup1 => ?_⟩
  have hq0 : 0 < pup * pac := mul_pos hpup0 hpac0
  have hκ'0 : 0 < min (9 / 10 * κ) (1 / 4000) := lt_min (by positivity) (by norm_num)
  have ha0 : 0 < alphaDeg lam / 400 := div_pos hα0 (by norm_num)
  have hε : 0 < min (min ((pup * pac / 150) ^ 2) ((lam / (2 * (1 + lam))) ^ 2))
      (min (9 / 10 * κ) (1 / 4000) / (alphaDeg lam / 400)) :=
    lt_min (lt_min (by positivity) (by positivity)) (div_pos hκ'0 ha0)
  -- `n` large: the thresholds of the proof
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (lazyShrinkAux_eventually
    (max (max (max (25 / 4 * K ^ 2) ((N₂₄ : ℝ) / (9 / 10 * pac)))
      (max 112 (2 * (4 / (lam / 2) + 4) / pac)))
      (max (max (4 / pac ^ 2) (4960 * (max C 0 + 1) ^ 2 * (3 / 2 + 1 / alphaDeg lam) /
        (Real.exp (-(8 / (lam / 2) + 7)) ^ 2 * (pup * pac) ^ 2)))
        (2 / (alphaDeg lam / 400 * (pup * pac)) *
          (18 + 48 / (alphaDeg lam / 400 * (pup * pac) ^ 2))))) hε)
  refine ⟨N, fun n hn p B₀ hp0 hlog h10 => ?_⟩
  obtain ⟨hML, hMn, hεn⟩ := hN n hn
  simp only [max_le_iff] at hML hMn
  simp only [le_min_iff] at hεn
  obtain ⟨⟨⟨hK2, -⟩, ⟨hL112, -⟩⟩, ⟨⟨-, hΓ⟩, hΛ⟩⟩ := hML
  obtain ⟨⟨⟨-, hN24⟩, ⟨h112n, hsz⟩⟩, ⟨⟨hsq, -⟩, -⟩⟩ := hMn
  obtain ⟨⟨hε1, hε2⟩, hε3⟩ := hεn
  exact lazyShrinkAux_bound_of_large B₀ h24 hC hκ hp0 hpac0 hpac1 hpup0 hpup1 hK hlam hlog h10
    hK2 hL112 hΓ hΛ hN24 h112n hsz hsq hε1 hε2 hε3

end PowerOfFew.Sparse

end
