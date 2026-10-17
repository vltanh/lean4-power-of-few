module

public import PowerOfFew.Defs
public import PowerOfFew.Model.Lazy
public import Basic.Probability.BernoulliFamily
public import Basic.Probability.Chernoff
public import Basic.Combinatorics.Choose

/-!
# Sparse paper, Section 4: Theorems 1.7 and 4.1 are false as printed

Counterexample (unconditional; it uses none of the assumed cited results): `p = 1` (the complete
graph), `p_ac = 1/2`, `p_up = 1`, and `|B₀| = n/2 − Δ` with `Δ = ⌊n^(1/4)⌋`. The difference between
the active Red and Blue vertices on day 1 is `Δ ± Θ(√n)`, so it is at most `−1` with probability
tending to `1/2`; then every active vertex turns Blue, and afterwards Blue has a linear majority
among the active vertices of every day except with probability `e^(−Ω(n))`, so Blue only grows.
Red wins with probability at most `1/2 + o(1)`, whereas the printed theorems claim `1 − o(1)`.

Two readings of the printed statements are refuted:

* uniform (`theorem1_7_printed_false`, `theorem4_1_printed_false`): the constants may depend on
  `λ`, `p_ac` and `p_up` (the weakest uniform reading), and the bound is claimed for every `n`,
  `p`, `B₀` satisfying the hypotheses;
* per sequence (`theorem1_7_printed_false_seq`, `theorem4_1_printed_false_seq`): "assume `p = p(n)`
  satisfies …" read for one sequence `(p, B₀)` at a time, with constants that may depend on the
  sequence and the bound claimed only for `n` large. Along the counterexample sequence, the
  hypotheses hold for all large `n` (whatever the threshold for `pΔ` or `p p_up p_ac² Δ`) and no
  constants make the bound hold for all large `n`.

Theorem 1.7's hypothesis `p p_ac n ≥ (1 + λ) n⁻¹ log n` is read with its misprint corrected
(`≥ (1 + λ) log n`); the counterexample satisfies both.

## Proof outline

All four statements come from one estimate along the sequence `B n` of the first
`⌊n/2⌋ − ⌊n^(1/4)⌋` vertices, with `p = 1`, `p_ac = 1/2`, `p_up = 1`:

1. At `p = 1` the graph is complete (`lazyProb_one`), and with `p_up = 1` every update coin is
   `true` almost surely.
2. On the complete graph, if every update coin is `true` and the active Blue vertices outnumber the
   active Red ones (a *good* day), every active vertex turns Blue.
3. On day 1 the number of active Red vertices minus the number of active Blue ones is
   `∑ᵥ Yᵥ − |B₀|` for a Bernoulli(`1/2`) family `Y`, so `∑ᵥ Yᵥ ∼ Bin(n, 1/2)`. By the symmetry
   `C(n, j) = C(n, n − j)` and `C(n, j) ≤ 2ⁿ/√n`, day 1 is not good with probability at most
   `1/2 + (n + 1 − 2|B₀|)/(2√n) ≤ 1/2 + (Δ + 1)/√n`.
4. After a good day 1, Blue is `B₀ ∪ A₁`, with at least `5n/8` vertices except with probability
   at most `e^(−n/256)` (Chernoff's lower tail for `|A₁ ∖ B₀| ∼ Bin(n − |B₀|, 1/2)`).
5. Whatever the past, a day on which Blue has at least `5n/8` vertices is not good with
   probability at most `e^(−n/256)` (Chernoff's upper tail), and after a good day Blue only grows.
6. Union bound over the days up to `⌊τ⌋₊ + 1`: Red wins by time `τ` with probability at most
   `1/2 + (Δ + 1)/√n + (⌊τ⌋₊ + 2) e^(−n/256)`, which is less than `3/5` for large `n` when
   `τ = O(n)`; the printed lower bounds tend to `1`.
7. The uniform readings follow by instantiating them at `p_ac = 1/2`, `p_up = 1`, `λ = 1/2`,
   `p = 1`, `B₀ = B n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace PowerOfFew.Sparse

section Deterministic

variable {n : ℕ}

/-- On the complete graph, the neighbours of `v` in `S` are the vertices of `S` other than `v`. -/
private lemma lazyCexAux_nbrCount_top (S : Set (Fin n)) (v : Fin n) :
    nbrCount (⊤ : SimpleGraph (Fin n)) S v = (S \ {v}).ncard := by
  unfold nbrCount
  congr 1
  ext u
  simp only [SimpleGraph.top_adj, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
  exact ⟨fun h => ⟨h.2, fun h' => h.1 h'.symm⟩, fun h => ⟨fun h' => h.2 h'.symm, h.1⟩⟩

/-- Step 2 of the proof outline: one day on the complete graph in which every active vertex
updates. If the active Blue vertices outnumber the active Red ones, every active vertex turns Blue:
an active Blue vertex sees `|A ∩ B| − 1` Blue and `|A ∩ Bᶜ|` Red active neighbours, an active Red
one sees `|A ∩ B|` Blue and `|A ∩ Bᶜ| − 1` Red ones. -/
private lemma lazyCexAux_lazyStep_top (A B : Set (Fin n))
    (h : (A ∩ Bᶜ).ncard < (A ∩ B).ncard) :
    lazyStep (⊤ : SimpleGraph (Fin n)) A Set.univ B = B ∪ A := by
  ext v
  simp only [lazyStep, Set.inter_univ, lazyCexAux_nbrCount_top, Set.mem_ofPred_eq, Set.mem_union]
  by_cases hvA : v ∈ A
  · have key : ((A ∩ Bᶜ) \ {v}).ncard < ((A ∩ B) \ {v}).ncard ∨
        (((A ∩ Bᶜ) \ {v}).ncard = ((A ∩ B) \ {v}).ncard ∧ v ∈ B) := by
      by_cases hvB : v ∈ B
      · have h1 : (A ∩ Bᶜ) \ {v} = A ∩ Bᶜ :=
          Set.sdiff_singleton_eq_self (fun hv => hv.2 hvB)
        have h2 : ((A ∩ B) \ {v}).ncard = (A ∩ B).ncard - 1 :=
          Set.ncard_sdiff_singleton_of_mem ⟨hvA, hvB⟩
        rw [h1, h2]
        rcases Nat.lt_or_ge (A ∩ Bᶜ).ncard ((A ∩ B).ncard - 1) with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨by omega, hvB⟩
      · have h1 : ((A ∩ Bᶜ) \ {v}).ncard = (A ∩ Bᶜ).ncard - 1 :=
          Set.ncard_sdiff_singleton_of_mem ⟨hvA, hvB⟩
        have h2 : (A ∩ B) \ {v} = A ∩ B := Set.sdiff_singleton_eq_self (fun hv => hvB hv.2)
        rw [h1, h2]
        exact Or.inl (by omega)
    simp only [hvA, true_and, not_true_eq_false, false_and, or_false, or_true, iff_true]
    exact key
  · simp [hvA]

/-- A good day for Blue: every update coin is `true`, and the active Blue vertices outnumber the
active Red ones. -/
private def lazyCexAux_good (d : DayCoins n) (B : Set (Fin n)) : Prop :=
  (∀ v, d.2 v = true) ∧ (actSet d ∩ Bᶜ).ncard < (actSet d ∩ B).ncard

/-- After a good day on the complete graph, every active vertex is Blue. -/
private lemma lazyCexAux_succ_of_good (c : ℕ → DayCoins n) (B₀ : Set (Fin n)) (t : ℕ)
    (h : lazyCexAux_good (c t) (lazyBlueAfter ⊤ c B₀ t)) :
    lazyBlueAfter ⊤ c B₀ (t + 1) = lazyBlueAfter ⊤ c B₀ t ∪ actSet (c t) := by
  rw [lazyBlueAfter_succ]
  have hU : updSet (c t) = Set.univ := Set.eq_univ_of_forall h.1
  rw [hU]
  exact lazyCexAux_lazyStep_top _ _ h.2

/-- Steps 4 and 5 of the proof outline, deterministically: if day 1 is good, Blue has at least
`θ` vertices after it, and every later day on which Blue has at least `θ` vertices is good, then
Blue keeps at least `θ` vertices. -/
private lemma lazyCexAux_le_ncard (c : ℕ → DayCoins n) (B₀ : Set (Fin n)) (θ : ℝ) (T : ℕ)
    (h0 : lazyCexAux_good (c 0) B₀) (h1 : θ ≤ ((B₀ ∪ actSet (c 0)).ncard : ℝ))
    (hs : ∀ s ∈ Finset.range (T + 1), θ ≤ ((lazyBlueAfter ⊤ c B₀ s).ncard : ℝ) →
      lazyCexAux_good (c s) (lazyBlueAfter ⊤ c B₀ s)) :
    ∀ t, t ≤ T → θ ≤ ((lazyBlueAfter ⊤ c B₀ (t + 1)).ncard : ℝ) := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [lazyCexAux_succ_of_good c B₀ 0 h0]
    exact h1
  | succ t ih =>
    intro ht
    have hB := ih (by omega)
    have hg := hs (t + 1) (Finset.mem_range.2 (by omega)) hB
    rw [lazyCexAux_succ_of_good c B₀ (t + 1) hg]
    refine hB.trans ?_
    exact_mod_cast Set.ncard_le_ncard Set.subset_union_left

end Deterministic

section OneDay

variable {n : ℕ}

/-- With `p_up = 1`, almost surely every update coin of a day is `true`. -/
private lemma lazyCexAux_dayLaw_upd (pac : ℝ) :
    (dayLaw n pac 1).real {d | ¬ ∀ v, d.2 v = true} = 0 := by
  have hU := isBernoulliFamily_upd (n := n) (pac := pac) (pup := 1) zero_le_one le_rfl
  have hv : ∀ v : Fin n, (dayLaw n pac 1).real {d | d.2 v = false} = 0 := by
    intro v
    have h1 := hU.prob_one v
    have hset : {d : DayCoins n | d.2 v = false} =
        {d : DayCoins n | (if d.2 v then (1 : ℝ) else 0) = 1}ᶜ := by
      ext d
      cases d.2 v <;> simp
    rw [hset, probReal_compl_eq_one_sub MeasurableSet.of_discrete, h1, sub_self]
  have hset : {d : DayCoins n | ¬ ∀ v, d.2 v = true} = ⋃ v, {d | d.2 v = false} := by
    ext d
    simp
  rw [hset]
  refine le_antisymm ?_ measureReal_nonneg
  calc _ ≤ ∑ v, (dayLaw n pac 1).real {d : DayCoins n | d.2 v = false} :=
        measureReal_iUnion_fintype_le _
    _ = 0 := by simp [hv]

open Classical in
/-- `x ↦ 1 − x` on the vertices of `B`, the identity elsewhere. -/
private def lazyCexAux_flip (B : Set (Fin n)) (v : Fin n) (x : ℝ) : ℝ :=
  if v ∈ B then 1 - x else x

/-- The indicator that `v` is active and Red, or inactive and Blue (for the Blue set `B`). -/
private def lazyCexAux_Y (B : Set (Fin n)) (v : Fin n) (d : DayCoins n) : ℝ :=
  lazyCexAux_flip B v (if d.1 v then 1 else 0)

/-- The indicators `Y` form a Bernoulli(`1/2`) family: flipping some of the activation indicators
of a Bernoulli(`1/2`) family gives a Bernoulli(`1/2`) family. -/
private lemma lazyCexAux_isBernoulliFamily_Y (pup : ℝ) (B : Set (Fin n)) :
    IsBernoulliFamily (dayLaw n (1 / 2) pup) (1 / 2) (lazyCexAux_Y B) := by
  have hX := isBernoulliFamily_act (n := n) (pac := 1 / 2) (pup := pup) (by norm_num) (by norm_num)
  refine ⟨fun v => Measurable.of_discrete, ?_, ?_, ?_⟩
  · have hg : ∀ v, Measurable (lazyCexAux_flip B v) := by
      intro v
      by_cases hv : v ∈ B
      · have e : lazyCexAux_flip B v = fun x => 1 - x := by
          funext x
          simp [lazyCexAux_flip, hv]
        rw [e]
        exact measurable_const.sub measurable_id
      · have e : lazyCexAux_flip B v = fun x => x := by
          funext x
          simp [lazyCexAux_flip, hv]
        rw [e]
        exact measurable_id
    exact hX.indep.comp (lazyCexAux_flip B) hg
  · intro v d
    by_cases hv : v ∈ B <;> by_cases h : d.1 v = true <;>
      simp [lazyCexAux_Y, lazyCexAux_flip, hv, h]
  · intro v
    by_cases hv : v ∈ B
    · have h1 := hX.prob_one v
      have hset : {d : DayCoins n | lazyCexAux_Y B v d = 1} =
          {d : DayCoins n | (if d.1 v then (1 : ℝ) else 0) = 1}ᶜ := by
        ext d
        by_cases h : d.1 v = true <;> simp [lazyCexAux_Y, lazyCexAux_flip, hv, h]
      rw [hset, probReal_compl_eq_one_sub MeasurableSet.of_discrete, h1]
      norm_num
    · have h1 := hX.prob_one v
      have hset : {d : DayCoins n | lazyCexAux_Y B v d = 1} =
          {d : DayCoins n | (if d.1 v then (1 : ℝ) else 0) = 1} := by
        ext d
        simp [lazyCexAux_Y, lazyCexAux_flip, hv]
      rw [hset, h1]

/-- The cardinality of a set of vertices as a sum of indicators. -/
private lemma lazyCexAux_ncard_eq_sum (S : Set (Fin n)) [DecidablePred (· ∈ S)] :
    (S.ncard : ℝ) = ∑ v, if v ∈ S then 1 else 0 := by
  rw [Finset.sum_boole]
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext v
  simp

/-- The sum of the indicators `Y`: `∑ Y = |A ∩ Bᶜ| + |B| − |A ∩ B|`, the difference between the
active Red and Blue vertices shifted by `|B|`. -/
private lemma lazyCexAux_sum_Y (B : Set (Fin n)) (d : DayCoins n) :
    ∑ v, lazyCexAux_Y B v d =
      ((actSet d ∩ Bᶜ).ncard : ℝ) + B.ncard - (actSet d ∩ B).ncard := by
  classical
  rw [lazyCexAux_ncard_eq_sum (actSet d ∩ Bᶜ), lazyCexAux_ncard_eq_sum B,
    lazyCexAux_ncard_eq_sum (actSet d ∩ B), ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : v ∈ B <;> by_cases h : d.1 v = true <;>
    simp [lazyCexAux_Y, lazyCexAux_flip, hv, h]

/-- A day that is not good for Blue has a `false` update coin, or `|B| ≤ ∑ Y`. -/
private lemma lazyCexAux_not_good_subset (B : Set (Fin n)) :
    {d : DayCoins n | ¬ lazyCexAux_good d B} ⊆
      {d | ¬ ∀ v, d.2 v = true} ∪ {d | (B.ncard : ℝ) ≤ ∑ v, lazyCexAux_Y B v d} := by
  intro d hd
  simp only [lazyCexAux_good, Set.mem_ofPred_eq, not_and_or, not_lt] at hd
  rcases hd with hd | hd
  · exact Or.inl hd
  · right
    simp only [Set.mem_ofPred_eq, lazyCexAux_sum_Y]
    have : ((actSet d ∩ B).ncard : ℝ) ≤ (actSet d ∩ Bᶜ).ncard := by exact_mod_cast hd
    linarith

end OneDay

section Binomial

/-- The sum of a Bernoulli family over `s` counts the variables equal to `1`. -/
private lemma lazyCexAux_sum_eq_card {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : ℝ}
    {X : ι → Ω → ℝ} (hX : IsBernoulliFamily μ p X) (s : Finset ι) (ω : Ω)
    [DecidablePred (fun i => X i ω = 1)] :
    ∑ i ∈ s, X i ω = ((s.filter (fun i => X i ω = 1)).card : ℝ) := by
  rw [← Finset.sum_boole]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hX.zero_or_one i ω with h | h <;> simp [h]

/-- The upper tail of a binomial variable as a sum of point probabilities. -/
private lemma lazyCexAux_measureReal_ge_eq_sum {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ℝ} {X : ι → Ω → ℝ}
    (hX : IsBernoulliFamily μ p X) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Finset ι) (k : ℕ) :
    μ.real {ω | (k : ℝ) ≤ ∑ i ∈ s, X i ω} =
      ∑ j ∈ Finset.Icc k s.card, (s.card.choose j : ℝ) * p ^ j * (1 - p) ^ (s.card - j) := by
  classical
  have hset : {ω | (k : ℝ) ≤ ∑ i ∈ s, X i ω} =
      ⋃ j ∈ Finset.Icc k s.card, {ω | ∑ i ∈ s, X i ω = j} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_Icc, exists_prop]
    rw [lazyCexAux_sum_eq_card hX s ω]
    constructor
    · intro h
      exact ⟨_, ⟨by exact_mod_cast h, Finset.card_filter_le _ _⟩, rfl⟩
    · rintro ⟨j, ⟨hkj, _⟩, hj⟩
      rw [hj]
      exact_mod_cast hkj
  rw [hset, measureReal_biUnion_finset]
  · exact Finset.sum_congr rfl fun j _ => hX.measureReal_sum_eq hp0 hp1 s j
  · intro j _ j' _ hjj'
    rw [Function.onFun, Set.disjoint_left]
    intro ω h h'
    simp only [Set.mem_ofPred_eq] at h h'
    exact hjj' (by exact_mod_cast h.symm.trans h')
  · intro j _
    exact measurableSet_eq_fun (Finset.measurable_sum s fun i _ => hX.measurable i)
      measurable_const

/-- The symmetry `C(m, j) = C(m, m − j)`: for `2k ≤ m + 1`,
`2 ∑_{j=k}^{m} C(m, j) = 2^m + ∑_{j=k}^{m−k} C(m, j)`. -/
private lemma lazyCexAux_two_mul_sum_choose (m k : ℕ) (hk : 2 * k ≤ m + 1) :
    2 * ∑ j ∈ Finset.Icc k m, (m.choose j : ℝ) =
      2 ^ m + ∑ j ∈ Finset.Icc k (m - k), (m.choose j : ℝ) := by
  have hrefl : ∑ j ∈ Finset.Icc k m, (m.choose j : ℝ) =
      ∑ j ∈ Finset.Icc 0 (m - k), (m.choose j : ℝ) := by
    refine Finset.sum_nbij' (fun j => m - j) (fun j => m - j) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      rw [Nat.choose_symm ha.2]
  have hunion : Finset.Icc k m ∪ Finset.Icc 0 (m - k) = Finset.range (m + 1) := by
    ext j
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_range]
    omega
  have hinter : Finset.Icc k m ∩ Finset.Icc 0 (m - k) = Finset.Icc k (m - k) := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_Icc]
    omega
  have hsum : ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) = 2 ^ m := by
    exact_mod_cast Nat.sum_range_choose m
  have h := Finset.sum_union_inter (s₁ := Finset.Icc k m) (s₂ := Finset.Icc 0 (m - k))
    (f := fun j => (m.choose j : ℝ))
  rw [hunion, hinter, hsum, ← hrefl] at h
  linarith

/-- Every binomial coefficient `C(m, j)` is at most `2^m / √m` (`m ≥ 1`), by
`Nat.centralBinom_lt_four_pow_div_sqrt` (for odd `m`, compare with `m + 1`). -/
private lemma lazyCexAux_choose_le (m j : ℕ) (hm : 1 ≤ m) :
    (m.choose j : ℝ) ≤ 2 ^ m / Real.sqrt m := by
  have h1 : (m.choose j : ℝ) ≤ m.choose (m / 2) := by exact_mod_cast Nat.choose_le_middle j m
  refine h1.trans ?_
  obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' m
  · have ha : 1 ≤ a := by omega
    have h2 := Nat.centralBinom_lt_four_pow_div_sqrt ha
    rw [Nat.centralBinom_eq_two_mul_choose] at h2
    rw [show 2 * a / 2 = a by omega, pow_mul]
    push_cast
    rw [show ((2 : ℝ) ^ 2) = 4 by norm_num]
    exact h2.le
  · have h2 := Nat.centralBinom_lt_four_pow_div_sqrt (m := a + 1) (by omega)
    rw [Nat.centralBinom_eq_two_mul_choose] at h2
    have h3 : (2 * (a + 1)).choose (a + 1) = 2 * (2 * a + 1).choose a := by
      rw [show 2 * (a + 1) = (2 * a + 1) + 1 by ring, Nat.choose_succ_succ, Nat.choose_symm_half]
      ring
    rw [h3] at h2
    rw [show (2 * a + 1) / 2 = a by omega]
    push_cast at h2 ⊢
    have hC : (0 : ℝ) ≤ ((2 * a + 1).choose a : ℝ) := Nat.cast_nonneg _
    have hs1 : 0 < Real.sqrt (2 * (a : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have hs2 : Real.sqrt (2 * (a : ℝ) + 1) ≤ Real.sqrt (2 * ((a : ℝ) + 1)) :=
      Real.sqrt_le_sqrt (by linarith)
    have hs3 : 0 < Real.sqrt (2 * ((a : ℝ) + 1)) := lt_of_lt_of_le hs1 hs2
    have h4 : (4 : ℝ) ^ (a + 1) = 2 * 2 ^ (2 * a + 1) := by
      rw [pow_succ, pow_succ, pow_mul]
      norm_num
      ring
    rw [h4, lt_div_iff₀ hs3] at h2
    rw [le_div_iff₀ hs1]
    have h5 := mul_le_mul_of_nonneg_left hs2 hC
    linarith

/-- **Anti-concentration** (step 3 of the proof outline): for a Bernoulli(`1/2`) family of `m ≥ 1`
variables and `2k ≤ m + 1`, `P(∑ ≥ k) ≤ 1/2 + (m + 1 − 2k) / (2√m)`. -/
private lemma lazyCexAux_measureReal_ge_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ} {Y : Fin m → Ω → ℝ} (hY : IsBernoulliFamily μ (1 / 2) Y)
    (hm : 1 ≤ m) (k : ℕ) (hk : 2 * k ≤ m + 1) :
    μ.real {ω | (k : ℝ) ≤ ∑ i, Y i ω} ≤ 1 / 2 + ((m : ℝ) + 1 - 2 * k) / (2 * Real.sqrt m) := by
  rw [lazyCexAux_measureReal_ge_eq_sum hY (by norm_num) (by norm_num) Finset.univ k]
  simp only [Finset.card_univ, Fintype.card_fin]
  have h1 : ∀ j ∈ Finset.Icc k m, (m.choose j : ℝ) * (1 / 2) ^ j * (1 - 1 / 2) ^ (m - j) =
      (m.choose j : ℝ) / 2 ^ m := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, mul_assoc, ← pow_add,
      Nat.add_sub_cancel' hj.2, one_div, inv_pow, div_eq_mul_inv]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_div]
  have h2 := lazyCexAux_two_mul_sum_choose m k hk
  have hc : ((m - k + 1 - k : ℕ) : ℝ) = (m : ℝ) + 1 - 2 * k := by
    have e : m - k + 1 - k + 2 * k = m + 1 := by omega
    have e' : ((m - k + 1 - k : ℕ) : ℝ) + 2 * k = m + 1 := by exact_mod_cast e
    linarith
  have h3 : ∑ j ∈ Finset.Icc k (m - k), (m.choose j : ℝ) ≤
      ((m : ℝ) + 1 - 2 * k) * (2 ^ m / Real.sqrt m) := by
    calc ∑ j ∈ Finset.Icc k (m - k), (m.choose j : ℝ)
        ≤ (Finset.Icc k (m - k)).card • (2 ^ m / Real.sqrt m) :=
          Finset.sum_le_card_nsmul _ _ _ fun j _ => lazyCexAux_choose_le m j hm
      _ = ((m : ℝ) + 1 - 2 * k) * (2 ^ m / Real.sqrt m) := by
          rw [Nat.card_Icc, nsmul_eq_mul, hc]
  have hpow : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_le_iff₀ hpow]
  have e : (1 / 2 + ((m : ℝ) + 1 - 2 * k) / (2 * Real.sqrt m)) * 2 ^ m =
      2 ^ m / 2 + ((m : ℝ) + 1 - 2 * k) * (2 ^ m / Real.sqrt m) / 2 := by
    ring
  rw [e]
  linarith

end Binomial

section DayBounds

variable {n : ℕ}

/-- Step 3 of the proof outline: the first day is not good for Blue with probability at most
`1/2 + (n + 1 − 2|B₀|) / (2√n)`. -/
private lemma lazyCexAux_first_day_not_good (hn : 1 ≤ n) (B₀ : Set (Fin n))
    (hB₀ : 2 * B₀.ncard ≤ n) :
    (dayLaw n (1 / 2) 1).real {d | ¬ lazyCexAux_good d B₀} ≤
      1 / 2 + ((n : ℝ) + 1 - 2 * B₀.ncard) / (2 * Real.sqrt n) := by
  calc (dayLaw n (1 / 2) 1).real {d | ¬ lazyCexAux_good d B₀}
      ≤ (dayLaw n (1 / 2) 1).real ({d | ¬ ∀ v, d.2 v = true} ∪
          {d | (B₀.ncard : ℝ) ≤ ∑ v, lazyCexAux_Y B₀ v d}) :=
        measureReal_mono (lazyCexAux_not_good_subset B₀)
    _ ≤ (dayLaw n (1 / 2) 1).real {d | ¬ ∀ v, d.2 v = true} +
          (dayLaw n (1 / 2) 1).real {d | (B₀.ncard : ℝ) ≤ ∑ v, lazyCexAux_Y B₀ v d} :=
        measureReal_union_le _ _
    _ ≤ 0 + (1 / 2 + ((n : ℝ) + 1 - 2 * B₀.ncard) / (2 * Real.sqrt n)) := by
        rw [lazyCexAux_dayLaw_upd]
        exact add_le_add le_rfl
          (lazyCexAux_measureReal_ge_le (lazyCexAux_isBernoulliFamily_Y 1 B₀) hn _ (by omega))
    _ = 1 / 2 + ((n : ℝ) + 1 - 2 * B₀.ncard) / (2 * Real.sqrt n) := zero_add _

/-- Step 5 of the proof outline (days `t + 1 ≥ 2`): when Blue has at least `5n/8` vertices, the
day is not good for Blue with probability at most `e^(−n/256)` (Chernoff's bound, upper tail, for
`∑ Y ∼ Bin(n, 1/2)`). -/
private lemma lazyCexAux_later_day_not_good (hn : 1 ≤ n) (B : Set (Fin n))
    (hB : 5 * (n : ℝ) / 8 ≤ B.ncard) :
    (dayLaw n (1 / 2) 1).real {d | ¬ lazyCexAux_good d B} ≤ Real.exp (-((n : ℝ) / 256)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hBn : (B.ncard : ℝ) ≤ n := by
    have h := Set.ncard_le_card B
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h
    exact_mod_cast h
  have hT : 1 / 2 * ((Finset.univ : Finset (Fin n)).card : ℝ) < B.ncard := by
    rw [Finset.card_univ, Fintype.card_fin]
    linarith
  have hC := (lazyCexAux_isBernoulliFamily_Y 1 B).measureReal_sum_ge_le_exp (by norm_num)
    (by norm_num) Finset.univ hT
  rw [Finset.card_univ, Fintype.card_fin] at hC
  calc (dayLaw n (1 / 2) 1).real {d | ¬ lazyCexAux_good d B}
      ≤ (dayLaw n (1 / 2) 1).real ({d | ¬ ∀ v, d.2 v = true} ∪
          {d | (B.ncard : ℝ) ≤ ∑ v, lazyCexAux_Y B v d}) :=
        measureReal_mono (lazyCexAux_not_good_subset B)
    _ ≤ (dayLaw n (1 / 2) 1).real {d | ¬ ∀ v, d.2 v = true} +
          (dayLaw n (1 / 2) 1).real {d | (B.ncard : ℝ) ≤ ∑ v, lazyCexAux_Y B v d} :=
        measureReal_union_le _ _
    _ ≤ 0 + Real.exp (-(((B.ncard : ℝ) - 1 / 2 * n) ^ 2 / (2 * B.ncard))) := by
        rw [lazyCexAux_dayLaw_upd]
        exact add_le_add le_rfl hC
    _ ≤ Real.exp (-((n : ℝ) / 256)) := by
        rw [zero_add, Real.exp_le_exp, neg_le_neg_iff, le_div_iff₀ (by linarith)]
        have h1 : (n : ℝ) / 8 ≤ B.ncard - 1 / 2 * n := by linarith
        have h2 : ((n : ℝ) / 8) ^ 2 ≤ ((B.ncard : ℝ) - 1 / 2 * n) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
        nlinarith

/-- Step 4 of the proof outline: after a good first day Blue is `B₀ ∪ A₁`, which has fewer than
`5n/8` vertices with probability at most `e^(−n/256)` when `3n/8 ≤ |B₀| ≤ n/2` (Chernoff's bound,
lower tail, for `|A₁ ∩ R₀| ∼ Bin(|R₀|, 1/2)`). -/
private lemma lazyCexAux_first_day_small (hn : 1 ≤ n) (B₀ : Set (Fin n))
    (hb1 : 3 * (n : ℝ) / 8 ≤ B₀.ncard) (hb2 : 2 * B₀.ncard ≤ n) :
    (dayLaw n (1 / 2) 1).real {d | ((B₀ ∪ actSet d).ncard : ℝ) < 5 * n / 8} ≤
      Real.exp (-((n : ℝ) / 256)) := by
  classical
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb2' : 2 * (B₀.ncard : ℝ) ≤ n := by exact_mod_cast hb2
  have hX := isBernoulliFamily_act (n := n) (pac := 1 / 2) (pup := 1) (by norm_num) (by norm_num)
  set s : Finset (Fin n) := Finset.univ.filter (fun v => v ∉ B₀) with hs
  have hsum : ∀ d : DayCoins n, ((B₀ ∪ actSet d).ncard : ℝ) =
      B₀.ncard + ∑ v ∈ s, (if d.1 v then (1 : ℝ) else 0) := by
    intro d
    rw [lazyCexAux_ncard_eq_sum (B₀ ∪ actSet d), lazyCexAux_ncard_eq_sum B₀, hs,
      Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v ∈ B₀ <;> by_cases h : d.1 v = true <;> simp [hv, h]
  have hcard : (s.card : ℝ) = n - B₀.ncard := by
    rw [hs, Finset.card_filter, lazyCexAux_ncard_eq_sum B₀, eq_sub_iff_add_eq]
    push_cast
    rw [← Finset.sum_add_distrib]
    have e : ∀ v : Fin n, ((if v ∉ B₀ then (1 : ℝ) else 0) + if v ∈ B₀ then 1 else 0) = 1 := by
      intro v
      by_cases hv : v ∈ B₀ <;> simp [hv]
    simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hT : 5 * (n : ℝ) / 8 - B₀.ncard < 1 / 2 * s.card := by
    rw [hcard]
    linarith
  have hC := hX.measureReal_sum_le_le_exp (by norm_num) (by norm_num) s hT
  calc (dayLaw n (1 / 2) 1).real {d | ((B₀ ∪ actSet d).ncard : ℝ) < 5 * n / 8}
      ≤ (dayLaw n (1 / 2) 1).real
          {d | ∑ v ∈ s, (if d.1 v then (1 : ℝ) else 0) ≤ 5 * n / 8 - B₀.ncard} := by
        refine measureReal_mono fun d hd => ?_
        simp only [Set.mem_ofPred_eq, hsum] at hd ⊢
        linarith
    _ ≤ Real.exp (-((1 / 2 * s.card - (5 * n / 8 - B₀.ncard)) ^ 2 /
          (2 * (1 / 2 * s.card)))) := hC
    _ ≤ Real.exp (-((n : ℝ) / 256)) := by
        rw [Real.exp_le_exp, neg_le_neg_iff, hcard, le_div_iff₀ (by linarith)]
        have h1 : (n : ℝ) / 16 ≤ 1 / 2 * (n - B₀.ncard) - (5 * n / 8 - B₀.ncard) := by linarith
        have h2 : ((n : ℝ) / 16) ^ 2 ≤ (1 / 2 * (n - B₀.ncard) - (5 * n / 8 - B₀.ncard)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
        nlinarith

end DayBounds

section FixedN

variable {n : ℕ}

/-- Step 6 of the proof outline, for one `n`: on `G(n, 1)` (the complete graph) with `p_ac = 1/2`,
`p_up = 1` and `3n/8 ≤ |B₀| ≤ n/2`, Red wins by time `τ` with probability at most
`1/2 + (n + 1 − 2|B₀|) / (2√n) + (⌊τ⌋₊ + 2) e^(−n/256)`. Union bound over the first day failing
(step 3), Blue being small after it (step 4), and a later day failing while Blue has at least
`5n/8` vertices (step 5); otherwise Blue keeps at least `5n/8` vertices
(`lazyCexAux_le_ncard`). -/
private lemma lazyCexAux_prob_le (hn : 1 ≤ n) (B₀ : Set (Fin n))
    (hb1 : 3 * (n : ℝ) / 8 ≤ B₀.ncard) (hb2 : 2 * B₀.ncard ≤ n) (τ : ℝ) :
    lazyProb n 1 (1 / 2) 1 (fun G c => ∃ t : ℕ, (t : ℝ) ≤ τ ∧ lazyBlueAfter G c B₀ t = ∅) ≤
      1 / 2 + ((n : ℝ) + 1 - 2 * B₀.ncard) / (2 * Real.sqrt n) +
        ((⌊τ⌋₊ : ℝ) + 2) * Real.exp (-((n : ℝ) / 256)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set T := ⌊τ⌋₊ with hT
  set θ : ℝ := 5 * n / 8 with hθ
  have hθ0 : 0 < θ := by
    rw [hθ]
    positivity
  set ε := Real.exp (-((n : ℝ) / 256)) with hε
  have hε0 : 0 ≤ ε := (Real.exp_pos _).le
  -- The bad events: the first day fails, Blue is small after it, or a later day fails while
  -- Blue is large.
  let E₀ : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop := fun _ c => ¬ lazyCexAux_good (c 0) B₀
  let E₁ : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop :=
    fun _ c => ((B₀ ∪ actSet (c 0)).ncard : ℝ) < θ
  let F : ℕ → SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop := fun s _ c =>
    θ ≤ ((lazyBlueAfter ⊤ c B₀ s).ncard : ℝ) ∧ ¬ lazyCexAux_good (c s) (lazyBlueAfter ⊤ c B₀ s)
  have hsub : ∀ (G : SimpleGraph (Fin n)) (c : ℕ → DayCoins n),
      (∃ t : ℕ, (t : ℝ) ≤ τ ∧ lazyBlueAfter ⊤ c B₀ t = ∅) →
        E₀ G c ∨ (E₁ G c ∨ ∃ s ∈ Finset.range (T + 1), F s G c) := by
    rintro G c ⟨t, ht, hBt⟩
    by_contra hcon
    simp only [E₀, E₁, F, not_or, not_not, not_lt, not_exists, not_and] at hcon
    obtain ⟨h0, h1, hs⟩ := hcon
    have hle := lazyCexAux_le_ncard c B₀ θ T h0 h1 (fun s hs' hθs => hs s hs' hθs) T le_rfl
    have htT : t ≤ T + 1 := by
      have : t ≤ T := Nat.le_floor ht
      omega
    have hT1 : lazyBlueAfter ⊤ c B₀ (T + 1) = ∅ := lazyBlueAfter_eq_empty_of_le ⊤ c B₀ hBt htT
    rw [hT1, Set.ncard_empty, Nat.cast_zero] at hle
    linarith
  have hE₀ : lazyProb n 1 (1 / 2) 1 E₀ ≤
      1 / 2 + ((n : ℝ) + 1 - 2 * B₀.ncard) / (2 * Real.sqrt n) := by
    refine lazyProb_le_of_forall_day 0 E₀ ?_ ?_
    · intro G c c' h
      simp only [E₀, h 0 le_rfl]
    · intro G c
      simp only [E₀, Function.update_self]
      exact lazyCexAux_first_day_not_good hn B₀ hb2
  have hE₁ : lazyProb n 1 (1 / 2) 1 E₁ ≤ ε := by
    refine lazyProb_le_of_forall_day 0 E₁ ?_ ?_
    · intro G c c' h
      simp only [E₁, h 0 le_rfl]
    · intro G c
      simp only [E₁, Function.update_self]
      exact lazyCexAux_first_day_small hn B₀ hb1 hb2
  have hF : ∀ s, lazyProb n 1 (1 / 2) 1 (F s) ≤ ε := by
    intro s
    refine lazyProb_le_of_forall_day s (F s) ?_ ?_
    · intro G c c' h
      have hB : lazyBlueAfter ⊤ c B₀ s = lazyBlueAfter ⊤ c' B₀ s :=
        lazyBlueAfter_congr ⊤ B₀ fun i hi => h i hi.le
      simp only [F, hB, h s le_rfl]
    · intro G c
      set B := lazyBlueAfter ⊤ c B₀ s with hBdef
      have hB : ∀ d, lazyBlueAfter ⊤ (Function.update c s d) B₀ s = B := fun d =>
        lazyBlueAfter_congr ⊤ B₀ fun i hi => Function.update_of_ne (ne_of_lt hi) d c
      have hset : {d | F s G (Function.update c s d)} =
          {d | θ ≤ (B.ncard : ℝ) ∧ ¬ lazyCexAux_good d B} := by
        ext d
        simp only [F, Set.mem_ofPred_eq, hB d, Function.update_self]
      rw [hset]
      by_cases hθB : θ ≤ (B.ncard : ℝ)
      · simp only [hθB, true_and]
        exact lazyCexAux_later_day_not_good hn B hθB
      · simp only [hθB, false_and, Set.ofPred_false, measureReal_empty]
        exact hε0
  rw [lazyProb_one]
  calc lazyProb n 1 (1 / 2) 1
        (fun _ c => ∃ t : ℕ, (t : ℝ) ≤ τ ∧ lazyBlueAfter ⊤ c B₀ t = ∅)
      ≤ lazyProb n 1 (1 / 2) 1
          (fun G c => E₀ G c ∨ (E₁ G c ∨ ∃ s ∈ Finset.range (T + 1), F s G c)) :=
        lazyProb_mono fun G c h => hsub G c h
    _ ≤ lazyProb n 1 (1 / 2) 1 E₀ + (lazyProb n 1 (1 / 2) 1 E₁ +
          ∑ s ∈ Finset.range (T + 1), lazyProb n 1 (1 / 2) 1 (F s)) := by
        refine (lazyProb_or_le E₀ _).trans (add_le_add le_rfl ?_)
        exact (lazyProb_or_le E₁ _).trans (add_le_add le_rfl (lazyProb_exists_le _ F))
    _ ≤ (1 / 2 + ((n : ℝ) + 1 - 2 * B₀.ncard) / (2 * Real.sqrt n)) +
          (ε + ∑ s ∈ Finset.range (T + 1), ε) :=
        add_le_add hE₀ (add_le_add hE₁ (Finset.sum_le_sum fun s _ => hF s))
    _ = 1 / 2 + ((n : ℝ) + 1 - 2 * B₀.ncard) / (2 * Real.sqrt n) + ((T : ℝ) + 2) * ε := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

end FixedN

section Sequence

/-- `Δ n = ⌊n^(1/4)⌋`. -/
private def lazyCexAux_Δ (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊

/-- The counterexample's initial Blue sets: the first `⌊n/2⌋ − Δ n` vertices. -/
private def lazyCexAux_B (n : ℕ) : Set (Fin n) := {v | v.val < n / 2 - lazyCexAux_Δ n}

private lemma lazyCexAux_ncard_B (n : ℕ) :
    (lazyCexAux_B n).ncard = n / 2 - lazyCexAux_Δ n := by
  classical
  have h : lazyCexAux_B n =
      ↑(Finset.univ.filter (fun v : Fin n => v.val < n / 2 - lazyCexAux_Δ n)) := by
    ext v
    simp [lazyCexAux_B]
  rw [h, Set.ncard_coe_finset, Fin.card_filter_val_lt]
  exact Nat.min_eq_right (by omega)

/-- `n^(1/4) → ∞`. -/
private lemma lazyCexAux_tendsto_rpow :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop

/-- `Δ n → ∞`. -/
private lemma lazyCexAux_tendsto_Δ :
    Tendsto (fun n : ℕ => (lazyCexAux_Δ n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp lazyCexAux_tendsto_rpow)

/-- The facts on `n^(1/4)` used below: `(n^(1/4))⁴ = n`, `Δ n ≤ n^(1/4)`, `√n = (n^(1/4))²`. -/
private lemma lazyCexAux_rpow_facts (n : ℕ) :
    0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) ∧ ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = n ∧
      (lazyCexAux_Δ n : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) ∧
      Real.sqrt n = ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
  have hr0 : 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hr4 : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = n := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    norm_num
  refine ⟨hr0, hr4, Nat.floor_le hr0, ?_⟩
  have e : (((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2) ^ 2 = n := by
    rw [← pow_mul]
    exact hr4
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2), e]

/-- For `n` large (`n^(1/4) ≥ 3`): `8(Δ + 1) ≤ n`. -/
private lemma lazyCexAux_eight_mul_le {n : ℕ} (hr : 3 ≤ (n : ℝ) ^ (1 / 4 : ℝ)) :
    8 * (lazyCexAux_Δ n + 1) ≤ n := by
  obtain ⟨hr0, hr4, hΔ, -⟩ := lazyCexAux_rpow_facts n
  set r := (n : ℝ) ^ (1 / 4 : ℝ)
  have h1 : 9 ≤ r ^ 2 := by nlinarith
  have h2 : 27 ≤ r ^ 3 := by nlinarith
  have h3 : 27 * r ≤ r ^ 4 := by nlinarith
  have h : (8 : ℝ) * ((lazyCexAux_Δ n : ℝ) + 1) ≤ n := by linarith
  exact_mod_cast h

/-- `n/2 − |B n| ≥ Δ n` for `n` large. -/
private lemma lazyCexAux_Δ_le {n : ℕ} (hr : 3 ≤ (n : ℝ) ^ (1 / 4 : ℝ)) :
    (lazyCexAux_Δ n : ℝ) ≤ (n : ℝ) / 2 - (lazyCexAux_B n).ncard := by
  have h8 := lazyCexAux_eight_mul_le hr
  have h : 2 * (lazyCexAux_B n).ncard + 2 * lazyCexAux_Δ n ≤ n := by
    rw [lazyCexAux_ncard_B]
    omega
  have h' : 2 * ((lazyCexAux_B n).ncard : ℝ) + 2 * lazyCexAux_Δ n ≤ n := by exact_mod_cast h
  linarith

/-- `n/2 − |B n| → ∞`. -/
private lemma lazyCexAux_tendsto_gap :
    Tendsto (fun n : ℕ => (n : ℝ) / 2 - (lazyCexAux_B n).ncard) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ lazyCexAux_tendsto_Δ
  filter_upwards [lazyCexAux_tendsto_rpow.eventually_ge_atTop 3] with n hn
  exact lazyCexAux_Δ_le hn

/-- `min{n, κ (n/2 − |B n|)²} → ∞` for `κ > 0`. -/
private lemma lazyCexAux_tendsto_min {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => min (n : ℝ) (κ * ((n : ℝ) / 2 - (lazyCexAux_B n).ncard) ^ 2))
      atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => κ * ((n : ℝ) / 2 - (lazyCexAux_B n).ncard) ^ 2) atTop atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp lazyCexAux_tendsto_gap).const_mul_atTop hκ
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop b, h1.eventually_ge_atTop b]
    with n hn1 hn2
  exact le_min hn1 hn2

/-- The hypothesis `(1 + λ) log n ≤ p p_ac n` (`λ = 1/2`, `p = 1`, `p_ac = 1/2`) holds for `n`
large. -/
private lemma lazyCexAux_eventually_log :
    ∀ᶠ n : ℕ in atTop, (1 + 1 / 2) * Real.log n ≤ 1 * (1 / 2) * (n : ℝ) := by
  have h := Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 3)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h] with n hn
  simp only [id, Real.norm_eq_abs] at hn
  rw [abs_of_nonneg (Real.log_natCast_nonneg n), abs_of_nonneg (Nat.cast_nonneg _)] at hn
  linarith

/-- Step 6 of the proof outline, along the sequence `B n`: if the time bound `τ n` is at most
`K n`, Red wins by time `τ n` with probability less than `3/5` for all large `n`. -/
private lemma lazyCexAux_eventually_lt (τ : ℕ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hτ : ∀ n, τ n ≤ K * n) :
    ∀ᶠ n : ℕ in atTop, lazyProb n 1 (1 / 2) 1 (fun G c => ∃ t : ℕ, (t : ℝ) ≤ τ n ∧
      lazyBlueAfter G c (lazyCexAux_B n) t = ∅) < 3 / 5 := by
  have h256 : Tendsto (fun n : ℕ => (n : ℝ) / 256) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
  have hexp : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) / 256))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h256
  have hmulexp : Tendsto (fun n : ℕ => ((n : ℝ) / 256) ^ 1 * Real.exp (-((n : ℝ) / 256)))
      atTop (nhds 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h256
  have hw : Tendsto (fun n : ℕ => 2 / (n : ℝ) ^ (1 / 4 : ℝ) +
      (K * n + 2) * Real.exp (-((n : ℝ) / 256))) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => 2 / (n : ℝ) ^ (1 / 4 : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop lazyCexAux_tendsto_rpow
    have h2 := (hmulexp.const_mul (256 * K)).add (hexp.const_mul 2)
    rw [mul_zero, mul_zero, add_zero] at h2
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr fun n => ?_
    ring
  filter_upwards [hw.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 10),
    lazyCexAux_tendsto_rpow.eventually_ge_atTop 3] with n hw hr
  obtain ⟨hr0, hr4, hΔ, hsq⟩ := lazyCexAux_rpow_facts n
  have h8 := lazyCexAux_eight_mul_le hr
  have hn : 1 ≤ n := by omega
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb2 : 2 * (lazyCexAux_B n).ncard ≤ n := by
    rw [lazyCexAux_ncard_B]
    omega
  have hb1 : 3 * (n : ℝ) / 8 ≤ (lazyCexAux_B n).ncard := by
    have h : 3 * n ≤ 8 * (lazyCexAux_B n).ncard := by
      rw [lazyCexAux_ncard_B]
      omega
    have h' : 3 * (n : ℝ) ≤ 8 * (lazyCexAux_B n).ncard := by exact_mod_cast h
    linarith
  have hgap : (n : ℝ) + 1 - 2 * (lazyCexAux_B n).ncard ≤ 2 * lazyCexAux_Δ n + 2 := by
    have h : n + 1 ≤ 2 * (lazyCexAux_B n).ncard + 2 * lazyCexAux_Δ n + 2 := by
      rw [lazyCexAux_ncard_B]
      omega
    have h' : (n : ℝ) + 1 ≤ 2 * (lazyCexAux_B n).ncard + 2 * lazyCexAux_Δ n + 2 := by
      exact_mod_cast h
    linarith
  -- The anti-concentration error is at most `2 / n^(1/4)`.
  have hanti : ((n : ℝ) + 1 - 2 * (lazyCexAux_B n).ncard) / (2 * Real.sqrt n) ≤
      2 / (n : ℝ) ^ (1 / 4 : ℝ) := by
    set r := (n : ℝ) ^ (1 / 4 : ℝ)
    have hr1 : 0 < r := by linarith
    rw [hsq, div_le_div_iff₀ (by positivity) hr1]
    have h1 : ((n : ℝ) + 1 - 2 * (lazyCexAux_B n).ncard) * r ≤ (2 * r + 2) * r :=
      mul_le_mul_of_nonneg_right (by linarith) hr1.le
    nlinarith
  -- The union bound's number of days is at most `K n + 1`.
  have hfl : (⌊τ n⌋₊ : ℝ) ≤ K * n := by
    rcases le_or_gt (τ n) 0 with h | h
    · rw [Nat.floor_of_nonpos h, Nat.cast_zero]
      positivity
    · exact (Nat.floor_le h.le).trans (hτ n)
  have hP := lazyCexAux_prob_le hn (lazyCexAux_B n) hb1 hb2 (τ n)
  have hexp0 : 0 ≤ Real.exp (-((n : ℝ) / 256)) := (Real.exp_pos _).le
  have h2 : ((⌊τ n⌋₊ : ℝ) + 2) * Real.exp (-((n : ℝ) / 256)) ≤
      (K * n + 2) * Real.exp (-((n : ℝ) / 256)) :=
    mul_le_mul_of_nonneg_right (by linarith) hexp0
  linarith

end Sequence

section Refutations

/-- Along `B n`, the hypotheses of Theorem 1.7 (`p = 1`, `p_ac = 1/2`, `λ = 1/2`) hold for all
large `n`, whatever the threshold `C₀` for `pΔ`. -/
private lemma lazyCexAux_hyp_1_7 (C₀ : ℝ) :
    ∀ᶠ n : ℕ in atTop, (1 + 1 / 2) * Real.log n ≤ 1 * (1 / 2) * n ∧
      C₀ ≤ 1 * ((n : ℝ) / 2 - (lazyCexAux_B n).ncard) := by
  filter_upwards [lazyCexAux_eventually_log,
    (lazyCexAux_tendsto_gap.const_mul_atTop one_pos).eventually_ge_atTop C₀] with n h1 h2
  exact ⟨h1, h2⟩

/-- Along `B n`, the hypotheses of Theorem 4.1 (`p = 1`, `p_ac = 1/2`, `p_up = 1`, `λ = 1/2`) hold
for all large `n`, whatever `M`. -/
private lemma lazyCexAux_hyp_4_1 (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, (1 + 1 / 2) * Real.log n ≤ 1 * (1 / 2) * n ∧
      M ≤ 1 * 1 * (1 / 2) ^ 2 * ((n : ℝ) / 2 - (lazyCexAux_B n).ncard) := by
  filter_upwards [lazyCexAux_eventually_log,
    (lazyCexAux_tendsto_gap.const_mul_atTop
      (by norm_num : (0 : ℝ) < 1 * 1 * (1 / 2) ^ 2)).eventually_ge_atTop M] with n h1 h2
  exact ⟨h1, h2⟩

/-- `A log n ≤ |A| n`. -/
private lemma lazyCexAux_mul_log_le (A : ℝ) (n : ℕ) : A * Real.log n ≤ |A| * n :=
  (mul_le_mul_of_nonneg_right (le_abs_self A) (Real.log_natCast_nonneg n)).trans
    (mul_le_mul_of_nonneg_left (Real.log_le_self (Nat.cast_nonneg n)) (abs_nonneg A))

/-- Step 6 of the proof outline, for Theorem 1.7: along `B n`, the printed lower bound tends to
`1`, while Red wins by time `A log n` with probability less than `3/5` for all large `n`. -/
private lemma lazyCexAux_not_1_7 :
    ¬ ∃ A C₁ C₂ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
        1 - C₁ / min (n : ℝ) (1 * ((n : ℝ) / 2 - (lazyCexAux_B n).ncard) ^ 2) -
            C₂ * (n : ℝ) ^ (-((1 / 2 : ℝ) / 4)) - (n : ℝ) ^ (-c) ≤
          lazyProb n 1 (1 / 2) 1 (fun G c' => ∃ t : ℕ,
            (t : ℝ) ≤ A * Real.log n ∧ lazyBlueAfter G c' (lazyCexAux_B n) t = ∅) := by
  rintro ⟨A, C₁, C₂, c, hc, hev⟩
  have hP := lazyCexAux_eventually_lt (fun n => A * Real.log n) (abs_nonneg A)
    (lazyCexAux_mul_log_le A)
  have h1 : Tendsto (fun n : ℕ => C₁ / min (n : ℝ) (1 * ((n : ℝ) / 2 -
      (lazyCexAux_B n).ncard) ^ 2)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (lazyCexAux_tendsto_min one_pos)
  have h2 : Tendsto (fun n : ℕ => C₂ * (n : ℝ) ^ (-((1 / 2 : ℝ) / 4))) atTop (nhds 0) := by
    have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (1 / 2 : ℝ) / 4)).comp
      tendsto_natCast_atTop_atTop).const_mul C₂
    rwa [mul_zero] at this
  have h3 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-c)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun n : ℕ => 1 - C₁ / min (n : ℝ) (1 * ((n : ℝ) / 2 -
      (lazyCexAux_B n).ncard) ^ 2) - C₂ * (n : ℝ) ^ (-((1 / 2 : ℝ) / 4)) - (n : ℝ) ^ (-c))
      atTop (nhds 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub h1).sub h2 |>.sub h3
    rwa [sub_zero, sub_zero, sub_zero] at this
  obtain ⟨n, hn1, hn2, hn3⟩ :=
    (hev.and (hP.and (hL.eventually_const_lt (by norm_num : (3 : ℝ) / 5 < 1)))).exists
  exact lt_irrefl _ ((hn3.trans_le hn1).trans hn2)

/-- Step 6 of the proof outline, for Theorem 4.1: along `B n`, the printed lower bound tends to
`1`, while Red wins by time `A log n / (p_up p_ac) = 2A log n` with probability less than `3/5` for
all large `n`. -/
private lemma lazyCexAux_not_4_1 :
    ¬ ∃ A C₁ c₁ C₂ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ n : ℕ in atTop,
        1 - C₁ / (1 ^ 2 * (1 / 2) ^ 2 *
              min (n : ℝ) (1 * (1 / 2) * ((n : ℝ) / 2 - (lazyCexAux_B n).ncard) ^ 2)) -
            Real.exp (-(c₁ * 1 ^ 2 * (1 / 2) ^ 4 * 1 *
              ((n : ℝ) / 2 - (lazyCexAux_B n).ncard) ^ 2)) -
            C₂ * (n : ℝ) ^ (-((1 / 2 : ℝ) / 4)) - (n : ℝ) ^ (-(c₂ * 1 * (1 / 2))) ≤
          lazyProb n 1 (1 / 2) 1 (fun G c => ∃ t : ℕ,
            (t : ℝ) ≤ A * Real.log n / (1 * (1 / 2)) ∧
              lazyBlueAfter G c (lazyCexAux_B n) t = ∅) := by
  rintro ⟨A, C₁, c₁, C₂, c₂, hc₁, hc₂, hev⟩
  have hc : (0 : ℝ) < c₁ * 1 ^ 2 * (1 / 2) ^ 4 * 1 := by positivity
  have hc' : (0 : ℝ) < c₂ * 1 * (1 / 2) := by positivity
  have hk : (0 : ℝ) < 1 ^ 2 * (1 / 2) ^ 2 := by norm_num
  have hP := lazyCexAux_eventually_lt (fun n => A * Real.log n / (1 * (1 / 2)))
    (K := 2 * |A|) (by positivity) fun n => by
      have h := lazyCexAux_mul_log_le A n
      have e : A * Real.log n / (1 * (1 / 2)) = 2 * (A * Real.log n) := by ring
      rw [e]
      linarith
  have h1 : Tendsto (fun n : ℕ => C₁ / (1 ^ 2 * (1 / 2) ^ 2 *
      min (n : ℝ) (1 * (1 / 2) * ((n : ℝ) / 2 - (lazyCexAux_B n).ncard) ^ 2))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      ((lazyCexAux_tendsto_min (by norm_num : (0 : ℝ) < 1 * (1 / 2))).const_mul_atTop hk)
  have h2 : Tendsto (fun n : ℕ => Real.exp (-(c₁ * 1 ^ 2 * (1 / 2) ^ 4 * 1 *
      ((n : ℝ) / 2 - (lazyCexAux_B n).ncard) ^ 2))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (((tendsto_pow_atTop two_ne_zero).comp lazyCexAux_tendsto_gap).const_mul_atTop hc)
  have h3 : Tendsto (fun n : ℕ => C₂ * (n : ℝ) ^ (-((1 / 2 : ℝ) / 4))) atTop (nhds 0) := by
    have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (1 / 2 : ℝ) / 4)).comp
      tendsto_natCast_atTop_atTop).const_mul C₂
    rwa [mul_zero] at this
  have h4 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(c₂ * 1 * (1 / 2)))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hc').comp tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun n : ℕ => 1 - C₁ / (1 ^ 2 * (1 / 2) ^ 2 *
        min (n : ℝ) (1 * (1 / 2) * ((n : ℝ) / 2 - (lazyCexAux_B n).ncard) ^ 2)) -
      Real.exp (-(c₁ * 1 ^ 2 * (1 / 2) ^ 4 * 1 *
        ((n : ℝ) / 2 - (lazyCexAux_B n).ncard) ^ 2)) -
      C₂ * (n : ℝ) ^ (-((1 / 2 : ℝ) / 4)) - (n : ℝ) ^ (-(c₂ * 1 * (1 / 2)))) atTop (nhds 1) := by
    have := (((tendsto_const_nhds (x := (1 : ℝ))).sub h1).sub h2).sub h3 |>.sub h4
    rwa [sub_zero, sub_zero, sub_zero, sub_zero] at this
  obtain ⟨n, hn1, hn2, hn3⟩ :=
    (hev.and (hP.and (hL.eventually_const_lt (by norm_num : (3 : ℝ) / 5 < 1)))).exists
  exact lt_irrefl _ ((hn3.trans_le hn1).trans hn2)

end Refutations

/-- Theorem 1.7 as printed (with `p p_ac n ≥ (1 + λ) log n`) is false, even if its constants may
depend on `p_ac`, `p_up` and `λ`: there are `p_ac`, `p_up`, `λ` such that, whatever the threshold
`C₀` for `pΔ`, the time constant `A` and the constants of the error terms, some `n`, `p`, `B₀`
violate the bound. -/
theorem theorem1_7_printed_false :
    ¬ ∀ pac pup lam : ℝ, 0 < pac → pac ≤ 1 → 0 < pup → pup ≤ 1 → 0 < lam →
      ∃ C₀ A C₁ C₂ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (p : ℝ) (B₀ : Set (Fin n)), 0 < p → p ≤ 1 →
        (1 + lam) * Real.log n ≤ p * pac * n → C₀ ≤ p * ((n : ℝ) / 2 - B₀.ncard) →
        1 - C₁ / min (n : ℝ) (p * ((n : ℝ) / 2 - B₀.ncard) ^ 2) - C₂ * (n : ℝ) ^ (-(lam / 4)) -
            (n : ℝ) ^ (-c) ≤
          lazyProb n p pac pup (fun G c' => ∃ t : ℕ,
            (t : ℝ) ≤ A * Real.log n ∧ lazyBlueAfter G c' B₀ t = ∅) := by
  intro H
  obtain ⟨C₀, A, C₁, C₂, c, hc, hH⟩ :=
    H (1 / 2) 1 (1 / 2) (by norm_num) (by norm_num) one_pos le_rfl (by norm_num)
  exact lazyCexAux_not_1_7 ⟨A, C₁, C₂, c, hc, (lazyCexAux_hyp_1_7 C₀).mono fun n hn =>
    hH n 1 (lazyCexAux_B n) one_pos le_rfl hn.1 hn.2⟩

/-- Theorem 4.1 as printed is false, even if its constants may depend on `λ`, `p_ac` and
`p_up`. -/
theorem theorem4_1_printed_false :
    ¬ ∀ lam pac pup : ℝ, 0 < lam → 0 < pac → pac ≤ 1 → 0 < pup → pup ≤ 1 →
      ∃ M A C₁ c₁ C₂ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (n : ℕ) (p : ℝ) (B₀ : Set (Fin n)), 0 < p →
        p ≤ 1 → (1 + lam) * Real.log n ≤ p * pac * n →
        M ≤ p * pup * pac ^ 2 * ((n : ℝ) / 2 - B₀.ncard) →
        1 - C₁ / (pup ^ 2 * pac ^ 2 * min (n : ℝ) (p * pac * ((n : ℝ) / 2 - B₀.ncard) ^ 2)) -
            Real.exp (-(c₁ * pup ^ 2 * pac ^ 4 * p * ((n : ℝ) / 2 - B₀.ncard) ^ 2)) -
            C₂ * (n : ℝ) ^ (-(lam / 4)) - (n : ℝ) ^ (-(c₂ * pup * pac)) ≤
          lazyProb n p pac pup (fun G c => ∃ t : ℕ,
            (t : ℝ) ≤ A * Real.log n / (pup * pac) ∧ lazyBlueAfter G c B₀ t = ∅) := by
  intro H
  obtain ⟨M, A, C₁, c₁, C₂, c₂, hc₁, hc₂, hH⟩ :=
    H (1 / 2) (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num) one_pos le_rfl
  exact lazyCexAux_not_4_1 ⟨A, C₁, c₁, C₂, c₂, hc₁, hc₂, (lazyCexAux_hyp_4_1 M).mono fun n hn =>
    hH n 1 (lazyCexAux_B n) one_pos le_rfl hn.1 hn.2⟩

/-- Theorem 1.7 as printed fails along one sequence: with `p = 1`, `p_ac = 1/2`, `p_up = 1`,
`λ = 1/2` and a sequence of initial Blue sets `B n`, the hypotheses hold for all large `n`
(whatever the threshold `C₀` for `pΔ`), and no constants `A`, `C₁`, `C₂`, `c` make the printed bound
hold for all large `n`. -/
theorem theorem1_7_printed_false_seq :
    ∃ B : (n : ℕ) → Set (Fin n),
      (∀ C₀ : ℝ, ∀ᶠ n : ℕ in atTop, (1 + 1 / 2) * Real.log n ≤ 1 * (1 / 2) * n ∧
        C₀ ≤ 1 * ((n : ℝ) / 2 - (B n).ncard)) ∧
      ¬ ∃ A C₁ C₂ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
          1 - C₁ / min (n : ℝ) (1 * ((n : ℝ) / 2 - (B n).ncard) ^ 2) -
              C₂ * (n : ℝ) ^ (-((1 / 2 : ℝ) / 4)) - (n : ℝ) ^ (-c) ≤
            lazyProb n 1 (1 / 2) 1 (fun G c' => ∃ t : ℕ,
              (t : ℝ) ≤ A * Real.log n ∧ lazyBlueAfter G c' (B n) t = ∅) := by
  exact ⟨lazyCexAux_B, lazyCexAux_hyp_1_7, lazyCexAux_not_1_7⟩

/-- Theorem 4.1 as printed fails along one sequence (`p = 1`, `p_ac = 1/2`, `p_up = 1`,
`λ = 1/2`): the hypotheses hold for all large `n` (whatever `M`), and no constants make the
printed bound hold for all large `n`. -/
theorem theorem4_1_printed_false_seq :
    ∃ B : (n : ℕ) → Set (Fin n),
      (∀ M : ℝ, ∀ᶠ n : ℕ in atTop, (1 + 1 / 2) * Real.log n ≤ 1 * (1 / 2) * n ∧
        M ≤ 1 * 1 * (1 / 2) ^ 2 * ((n : ℝ) / 2 - (B n).ncard)) ∧
      ¬ ∃ A C₁ c₁ C₂ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ n : ℕ in atTop,
          1 - C₁ / (1 ^ 2 * (1 / 2) ^ 2 *
                min (n : ℝ) (1 * (1 / 2) * ((n : ℝ) / 2 - (B n).ncard) ^ 2)) -
              Real.exp (-(c₁ * 1 ^ 2 * (1 / 2) ^ 4 * 1 * ((n : ℝ) / 2 - (B n).ncard) ^ 2)) -
              C₂ * (n : ℝ) ^ (-((1 / 2 : ℝ) / 4)) - (n : ℝ) ^ (-(c₂ * 1 * (1 / 2))) ≤
            lazyProb n 1 (1 / 2) 1 (fun G c => ∃ t : ℕ,
              (t : ℝ) ≤ A * Real.log n / (1 * (1 / 2)) ∧ lazyBlueAfter G c (B n) t = ∅) := by
  exact ⟨lazyCexAux_B, lazyCexAux_hyp_4_1, lazyCexAux_not_4_1⟩

end PowerOfFew.Sparse

end
