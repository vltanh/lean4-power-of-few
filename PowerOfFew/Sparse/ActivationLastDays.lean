module

public import PowerOfFew.Sparse.Degrees
public import PowerOfFew.Model.Lazy

/-!
# Sparse paper, Section 4: the last days with random activations and updates

The constant `α_λ` of Lemma A.4 and Proposition 4.4 of the sparse paper (unlabelled there): once
Blue has at most `α_λ (log n)/2` vertices, every Blue vertex that updates turns Red, and within
`O(log n)` more days every one of them has updated. See `PowerOfFew/Sparse/Activation.lean` for
the setting and the readings of Section 4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- `α_λ = exp(−(8/λ + 7))`, the constant of Lemma A.4. -/
def alphaDeg (lam : ℝ) : ℝ := Real.exp (-(8 / lam + 7))

/-- The active neighbours of `v` split into the Blue and the Red ones. -/
private lemma lazyFinalAux_nbrCount_add {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Set (Fin n))
    (v : Fin n) : nbrCount G (A ∩ B) v + nbrCount G (A ∩ Bᶜ) v = nbrCount G A v := by
  unfold nbrCount
  rw [← Set.ncard_union_eq]
  · congr 1
    ext u
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    tauto
  · rw [Set.disjoint_left]
    rintro u ⟨_, _, hB⟩ ⟨_, _, hB'⟩
    exact hB' hB

/-- Step 1 of the proof of Proposition 4.4 (deterministic). If `|B_{t₀}| ≤ b / 2` and on each of
the days `t₀, …, t₀ + k − 1` every active vertex has more than `b` active neighbours, then an
updating vertex sees fewer active Blue neighbours (at most `|B_t| ≤ b / 2`) than active Red ones
(more than `b − b / 2`), so it is Red the next day: `B_{t+1} = B_t \ (A_t ∩ U_t)`. Hence every
vertex that is Blue on day `t₀ + k` is Blue on day `t₀` and does not update on any of these
days. -/
private lemma lazyFinalAux_mem_of_degree {n : ℕ} (G : SimpleGraph (Fin n)) (c : ℕ → DayCoins n)
    (B₀ : Set (Fin n)) (t₀ : ℕ) {b : ℝ}
    (hB : ((lazyBlueAfter G c B₀ t₀).ncard : ℝ) ≤ b / 2) :
    ∀ k : ℕ, (∀ s, t₀ ≤ s → s < t₀ + k → ∀ v ∈ actSet (c s), b < nbrCount G (actSet (c s)) v) →
      ∀ v ∈ lazyBlueAfter G c B₀ (t₀ + k), v ∈ lazyBlueAfter G c B₀ t₀ ∧
        ∀ s, t₀ ≤ s → s < t₀ + k → ¬ ((c s).1 v = true ∧ (c s).2 v = true) := by
  intro k
  induction k with
  | zero =>
    intro _ v hv
    exact ⟨hv, fun s hs1 hs2 => absurd hs2 (by omega)⟩
  | succ k ih =>
    intro hdeg v hv
    have ih' := ih (fun s hs1 hs2 => hdeg s hs1 (by omega))
    rw [show t₀ + (k + 1) = (t₀ + k) + 1 by omega, lazyBlueAfter_succ, lazyStep_eq] at hv
    set B := lazyBlueAfter G c B₀ (t₀ + k) with hBdef
    set A := actSet (c (t₀ + k)) with hA
    set U := updSet (c (t₀ + k)) with hU
    -- `B ⊆ B_{t₀}`, so `|B| ≤ b / 2`
    have hsub : B ⊆ lazyBlueAfter G c B₀ t₀ := fun u hu => (ih' u hu).1
    have hcard : (B.ncard : ℝ) ≤ b / 2 :=
      le_trans (by exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)) hB
    rcases hv with hv | hv
    · -- `v` did not update
      obtain ⟨hvB, hvAU⟩ := hv
      refine ⟨(ih' v hvB).1, fun s hs1 hs2 => ?_⟩
      rcases Nat.lt_or_ge s (t₀ + k) with hs | hs
      · exact (ih' v hvB).2 s hs1 hs
      · have hs' : s = t₀ + k := by omega
        subst hs'
        exact fun h => hvAU ⟨h.1, h.2⟩
    · -- an updating vertex is Red the next day
      exfalso
      obtain ⟨⟨hvA, _⟩, hvhyp⟩ := hv
      have hdegv := hdeg (t₀ + k) (by omega) (by omega) v hvA
      have hblue : (nbrCount G (A ∩ B) v : ℝ) ≤ b / 2 := by
        refine le_trans ?_ hcard
        have hsubB : {u | G.Adj v u ∧ u ∈ A ∩ B} ⊆ B := fun u hu => hu.2.2
        exact_mod_cast Set.ncard_le_ncard hsubB (Set.toFinite _)
      have hsplit := lazyFinalAux_nbrCount_add G A B v
      have hred : (nbrCount G (A ∩ B) v : ℝ) < nbrCount G (A ∩ Bᶜ) v := by
        have : (nbrCount G (A ∩ B) v : ℝ) + nbrCount G (A ∩ Bᶜ) v = nbrCount G A v := by
          exact_mod_cast hsplit
        linarith
      have hred' : nbrCount G (A ∩ B) v < nbrCount G (A ∩ Bᶜ) v := by exact_mod_cast hred
      rcases hvhyp with h | ⟨h, _⟩
      · exact absurd h (by omega)
      · omega

/-- Steps 1 and 3 of the proof of Proposition 4.4, deterministically: if some day
`t₀ ≤ x ≤ T₁` has `|B_{t₀}| ≤ b / 2` and Blue is not empty on day `T₁ + T₂`, then either some
active vertex has at most `b` active neighbours on some day before `T₁ + T₂`, or some vertex of
`B_{t₀}` does not update on any of the days `t₀, …, T₁ + T₂ − 1` (`lazyFinalAux_mem_of_degree`). -/
private lemma lazyFinalAux_contain {n : ℕ} (G : SimpleGraph (Fin n)) (c : ℕ → DayCoins n)
    (B₀ : Set (Fin n)) {x b : ℝ} (T₁ T₂ : ℕ) (hx : x ≤ T₁)
    (h : (∃ t₀ : ℕ, (t₀ : ℝ) ≤ x ∧ ((lazyBlueAfter G c B₀ t₀).ncard : ℝ) ≤ b / 2) ∧
      lazyBlueAfter G c B₀ (T₁ + T₂) ≠ ∅) :
    (∃ t ∈ Finset.range (T₁ + T₂), ∃ v ∈ actSet (c t), (nbrCount G (actSet (c t)) v : ℝ) ≤ b) ∨
    (∃ t₀ ∈ Finset.range (T₁ + 1), ((lazyBlueAfter G c B₀ t₀).ncard : ℝ) ≤ b / 2 ∧
      ∃ v ∈ lazyBlueAfter G c B₀ t₀, ∀ s, t₀ ≤ s → s < t₀ + (T₁ + T₂ - t₀) →
        ¬ ((c s).1 v = true ∧ (c s).2 v = true)) := by
  obtain ⟨⟨t₀, ht₀, hB⟩, hne⟩ := h
  by_cases hdeg : ∃ t ∈ Finset.range (T₁ + T₂), ∃ v ∈ actSet (c t),
      (nbrCount G (actSet (c t)) v : ℝ) ≤ b
  · exact Or.inl hdeg
  · right
    push Not at hdeg
    have ht₀T₁ : t₀ ≤ T₁ := by
      have : (t₀ : ℝ) ≤ T₁ := le_trans ht₀ hx
      exact_mod_cast this
    refine ⟨t₀, Finset.mem_range.mpr (by omega), hB, ?_⟩
    have hk : t₀ + (T₁ + T₂ - t₀) = T₁ + T₂ := by omega
    obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.mpr hne
    rw [← hk] at hv
    have := lazyFinalAux_mem_of_degree G c B₀ t₀ hB (T₁ + T₂ - t₀)
      (fun s _ hs2 u hu => hdeg s (Finset.mem_range.mpr (by omega)) u hu) v hv
    exact ⟨v, this.1, this.2⟩

/-- The probability that a vertex does not update on a day is `1 − p_ac p_up`. -/
private lemma lazyFinalAux_dayLaw_not_upd {n : ℕ} {pac pup : ℝ} (hpac0 : 0 ≤ pac) (hpac1 : pac ≤ 1)
    (hpup0 : 0 ≤ pup) (hpup1 : pup ≤ 1) (v : Fin n) :
    (dayLaw n pac pup).real {d | ¬ (d.1 v = true ∧ d.2 v = true)} = 1 - pac * pup := by
  classical
  have h := (isBernoulliFamily_actUpd (n := n) hpac0 hpac1 hpup0 hpup1).prob_one v
  have e : {d : DayCoins n | (if d.1 v = true ∧ d.2 v = true then (1 : ℝ) else 0) = 1} =
      {d | d.1 v = true ∧ d.2 v = true} := by
    ext d
    by_cases hd : d.1 v = true ∧ d.2 v = true <;> simp [hd]
  rw [e] at h
  rw [show {d : DayCoins n | ¬ (d.1 v = true ∧ d.2 v = true)} =
    {d | d.1 v = true ∧ d.2 v = true}ᶜ from rfl,
    probReal_compl_eq_one_sub MeasurableSet.of_discrete, h]

/-- Step 2 of the proof of Proposition 4.4. Conditioning on the graph and on the first `t₀` days:
whatever they are, the probability that one of at most `b` vertices of `B_{t₀}` does not update on
any of the `k` days `t₀, …, t₀ + k − 1` is at most `b (1 − p_ac p_up)^k`. -/
private lemma lazyFinalAux_never_update {n : ℕ} {p pac pup b : ℝ} (hpac0 : 0 ≤ pac)
    (hpac1 : pac ≤ 1) (hpup0 : 0 ≤ pup) (hpup1 : pup ≤ 1) (hb : 0 ≤ b) (B₀ : Set (Fin n))
    (t₀ k : ℕ) :
    lazyProb n p pac pup (fun G c => ((lazyBlueAfter G c B₀ t₀).ncard : ℝ) ≤ b ∧
      ∃ v ∈ lazyBlueAfter G c B₀ t₀, ∀ s, t₀ ≤ s → s < t₀ + k →
        ¬ ((c s).1 v = true ∧ (c s).2 v = true)) ≤
      b * (1 - pac * pup) ^ k := by
  classical
  have hq : 0 ≤ 1 - pac * pup := by nlinarith
  apply lazyProb_le_of_forall_days t₀ k
  · intro G c c' hcc'
    have hB : lazyBlueAfter G c B₀ t₀ = lazyBlueAfter G c' B₀ t₀ :=
      lazyBlueAfter_congr G B₀ (fun i hi => hcc' i (by omega))
    rw [hB]
    constructor
    · rintro ⟨h1, v, hv, hs⟩
      exact ⟨h1, v, hv, fun s hs1 hs2 => by rw [← hcc' s hs2]; exact hs s hs1 hs2⟩
    · rintro ⟨h1, v, hv, hs⟩
      exact ⟨h1, v, hv, fun s hs1 hs2 => by rw [hcc' s hs2]; exact hs s hs1 hs2⟩
  · intro G c
    -- the Blue set of day `t₀` does not depend on the days `t₀, …, t₀ + k − 1`
    have hBw : ∀ w : Fin k → DayCoins n,
        lazyBlueAfter G (fun i => if hi : t₀ ≤ i ∧ i < t₀ + k then w ⟨i - t₀, by omega⟩ else c i)
          B₀ t₀ = lazyBlueAfter G c B₀ t₀ := fun w =>
      lazyBlueAfter_congr G B₀ (fun i hi => by
        simp only [show ¬ (t₀ ≤ i ∧ i < t₀ + k) by omega, dite_false])
    set B := lazyBlueAfter G c B₀ t₀ with hBdef
    by_cases hBb : (B.ncard : ℝ) ≤ b
    · set S : Fin n → Set (DayCoins n) := fun v => {d | ¬ (d.1 v = true ∧ d.2 v = true)}
        with hS
      have hsub : {w : Fin k → DayCoins n | ((lazyBlueAfter G
            (fun i => if hi : t₀ ≤ i ∧ i < t₀ + k then w ⟨i - t₀, by omega⟩ else c i)
            B₀ t₀).ncard : ℝ) ≤ b ∧
          ∃ v ∈ lazyBlueAfter G
            (fun i => if hi : t₀ ≤ i ∧ i < t₀ + k then w ⟨i - t₀, by omega⟩ else c i) B₀ t₀,
            ∀ s, t₀ ≤ s → s < t₀ + k →
              ¬ (((fun i => if hi : t₀ ≤ i ∧ i < t₀ + k then w ⟨i - t₀, by omega⟩ else c i)
                s).1 v = true ∧
              ((fun i => if hi : t₀ ≤ i ∧ i < t₀ + k then w ⟨i - t₀, by omega⟩ else c i)
                s).2 v = true)} ⊆
          ⋃ v ∈ B.toFinset, Set.pi Set.univ (fun _ : Fin k => S v) := by
        rintro w ⟨_, v, hv, hs⟩
        rw [hBw w] at hv
        simp only [Set.mem_iUnion, Set.mem_toFinset, Set.mem_pi, Set.mem_univ, true_implies]
        refine ⟨v, hv, fun j => ?_⟩
        have := hs (t₀ + j) (by omega) (by omega)
        simp only [show t₀ ≤ t₀ + j ∧ t₀ + j < t₀ + k by omega,
          show t₀ + j - t₀ = (j : ℕ) by omega, Fin.eta] at this
        exact this
      refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
      refine le_trans (measureReal_biUnion_finset_le _ _) ?_
      have hpi : ∀ v, (Measure.pi fun _ : Fin k => dayLaw n pac pup).real
          (Set.pi Set.univ (fun _ : Fin k => S v)) = (1 - pac * pup) ^ k := fun v => by
        rw [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
        simp only [← measureReal_def, hS, lazyFinalAux_dayLaw_not_upd hpac0 hpac1 hpup0 hpup1,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      simp only [hpi, Finset.sum_const, nsmul_eq_mul]
      rw [← Set.ncard_eq_toFinset_card']
      exact mul_le_mul_of_nonneg_right hBb (pow_nonneg hq _)
    · have hempty : {w : Fin k → DayCoins n | ((lazyBlueAfter G
            (fun i => if hi : t₀ ≤ i ∧ i < t₀ + k then w ⟨i - t₀, by omega⟩ else c i)
            B₀ t₀).ncard : ℝ) ≤ b ∧
          ∃ v ∈ lazyBlueAfter G
            (fun i => if hi : t₀ ≤ i ∧ i < t₀ + k then w ⟨i - t₀, by omega⟩ else c i) B₀ t₀,
            ∀ s, t₀ ≤ s → s < t₀ + k →
              ¬ (((fun i => if hi : t₀ ≤ i ∧ i < t₀ + k then w ⟨i - t₀, by omega⟩ else c i)
                s).1 v = true ∧
              ((fun i => if hi : t₀ ≤ i ∧ i < t₀ + k then w ⟨i - t₀, by omega⟩ else c i)
                s).2 v = true)} = ∅ := by
        ext w
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro h
        rw [hBw w] at h
        exact absurd h hBb
      rw [hempty, measureReal_empty]
      exact mul_nonneg hb (pow_nonneg hq _)

/-- Step 2 of the proof of Proposition 4.4, over the possible days `t₀ ≤ T₁`: by the union bound
and `lazyFinalAux_never_update` with `k = T₁ + T₂ − t₀ ≥ T₂ ≥ log n` days and
`(1 − p_ac p_up)^k ≤ e^(−p_ac p_up k)`, the probability that some `B_{t₀}` has at most `b`
vertices, one of which never updates until day `T₁ + T₂`, is at most `(T₁ + 1) b n^(−p_up p_ac)`. -/
private lemma lazyFinalAux_update_event {n : ℕ} {p pac pup b : ℝ} (hpac0 : 0 ≤ pac)
    (hpac1 : pac ≤ 1) (hpup0 : 0 ≤ pup) (hpup1 : pup ≤ 1) (hb : 0 ≤ b) (hn : (0 : ℝ) < n)
    (B₀ : Set (Fin n)) (T₁ T₂ : ℕ) (hT₂ : Real.log n ≤ T₂) :
    lazyProb n p pac pup (fun G c => ∃ t₀ ∈ Finset.range (T₁ + 1),
      ((lazyBlueAfter G c B₀ t₀).ncard : ℝ) ≤ b ∧
        ∃ v ∈ lazyBlueAfter G c B₀ t₀, ∀ s, t₀ ≤ s → s < t₀ + (T₁ + T₂ - t₀) →
          ¬ ((c s).1 v = true ∧ (c s).2 v = true)) ≤
      ((T₁ + 1 : ℕ) : ℝ) * (b * (n : ℝ) ^ (-(pup * pac))) := by
  refine le_trans (lazyProb_exists_le _ _) ?_
  have hx0 : 0 ≤ 1 - pac * pup := by nlinarith
  have hx1 : 1 - pac * pup ≤ 1 := by nlinarith
  have hone : ∀ t₀ ∈ Finset.range (T₁ + 1), lazyProb n p pac pup (fun G c =>
      ((lazyBlueAfter G c B₀ t₀).ncard : ℝ) ≤ b ∧
        ∃ v ∈ lazyBlueAfter G c B₀ t₀, ∀ s, t₀ ≤ s → s < t₀ + (T₁ + T₂ - t₀) →
          ¬ ((c s).1 v = true ∧ (c s).2 v = true)) ≤ b * (n : ℝ) ^ (-(pup * pac)) := by
    intro t₀ ht₀
    have ht₀' : t₀ ≤ T₁ := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht₀)
    refine le_trans (lazyFinalAux_never_update hpac0 hpac1 hpup0 hpup1 hb B₀ t₀
      (T₁ + T₂ - t₀)) ?_
    apply mul_le_mul_of_nonneg_left _ hb
    have hq : 0 ≤ pac * pup := mul_nonneg hpac0 hpup0
    calc (1 - pac * pup) ^ (T₁ + T₂ - t₀) ≤ (1 - pac * pup) ^ T₂ :=
          pow_le_pow_of_le_one hx0 hx1 (by omega)
      _ ≤ Real.exp (-(pac * pup)) ^ T₂ :=
          pow_le_pow_left₀ hx0 (Real.one_sub_le_exp_neg _) T₂
      _ = Real.exp (T₂ * -(pac * pup)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (Real.log n * -(pup * pac)) := by
          apply Real.exp_le_exp.mpr
          rw [mul_comm pac pup] at hq ⊢
          have := mul_le_mul_of_nonneg_right hT₂ hq
          linarith
      _ = (n : ℝ) ^ (-(pup * pac)) := (Real.rpow_def_of_pos hn _).symm
  refine le_trans (Finset.sum_le_sum hone) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- A sum of Bernoulli variables with parameter `1` is below its number of terms with
probability `0`. -/
private lemma lazyFinalAux_measureReal_sum_le_of_one {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ} (hX : IsBernoulliFamily μ 1 X)
    (s : Finset ι) {b : ℝ} (hb : b < s.card) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ b} = 0 := by
  have hsub : {ω | ∑ i ∈ s, X i ω ≤ b} ⊆ ⋃ i ∈ s, {ω | X i ω = 1}ᶜ := by
    intro ω hω
    by_contra h
    simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_not] at h
    have : ∑ i ∈ s, X i ω = s.card := by
      rw [Finset.sum_congr rfl (fun i hi => h i hi)]
      simp
    simp only [Set.mem_ofPred_eq] at hω
    linarith
  have h0 : ∀ i ∈ s, μ.real {ω | X i ω = 1}ᶜ = 0 := fun i _ => by
    have hm : MeasurableSet {ω | X i ω = 1} := hX.measurable i (measurableSet_singleton 1)
    rw [probReal_compl_eq_one_sub hm, hX.prob_one]
    simp
  refine le_antisymm ?_ measureReal_nonneg
  calc μ.real {ω | ∑ i ∈ s, X i ω ≤ b} ≤ μ.real (⋃ i ∈ s, {ω | X i ω = 1}ᶜ) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i ∈ s, μ.real {ω | X i ω = 1}ᶜ := measureReal_biUnion_finset_le _ _
    _ = 0 := Finset.sum_eq_zero h0

/-- If `(1 + λ) log y ≤ p y` and `1 + λ ≤ p y`, then `(1 + λ) log x ≤ p x` for every `x ≥ y`: the
function `x ↦ p x − (1 + λ) log x` is nondecreasing where `p x ≥ 1 + λ`. -/
private lemma lazyFinalAux_log_le_of_le {p a x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) (ha : 0 ≤ a)
    (hlog : a * Real.log y ≤ p * y) (hay : a ≤ p * y) : a * Real.log x ≤ p * x := by
  have hx : 0 < x := lt_of_lt_of_le hy hyx
  have h1 : Real.log x - Real.log y ≤ x / y - 1 := by
    rw [← Real.log_div hx.ne' hy.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hx hy)
  have h2 : a * (x / y - 1) ≤ p * (x - y) := by
    have e : a * (x / y - 1) = a / y * (x - y) := by
      field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    rw [div_le_iff₀ hy]
    linarith
  have := mul_le_mul_of_nonneg_left h1 ha
  linarith

/-- Step 3 of the proof of Proposition 4.4, for one day with a given active set `A` of at least
`m₀` vertices. The subgraph `G[A]` induced on `A` is `G(|A|, p)` (`gnpProb_inducedOn`), and
`p |A| ≥ (1 + λ) log |A|` (it holds at `m₀`), so Lemma A.4 with `ε = λ` gives `G[A]` minimum
degree at least `α_λ p |A| > α_λ log n` except with probability `|A|^(−λ/2) ≤ m₀^(−λ/2)`: then
every active vertex has more than `α_λ log n` active neighbours (`degree_inducedOn`). -/
private lemma lazyFinalAux_good {n : ℕ} {lam p m₀ : ℝ} (hlam : 0 < lam) (hp0 : 0 < p)
    (hp1 : p ≤ 1) (hm₀ : 4 / lam + 4 ≤ m₀) (hlog : (1 + lam) * Real.log m₀ ≤ p * m₀)
    (hpm₀ : 1 + lam ≤ p * m₀) (hL : Real.log n < p * m₀) (A : Set (Fin n))
    (hA : m₀ ≤ A.ncard) :
    gnpProb n p (fun G => ∃ v ∈ A, (nbrCount G A v : ℝ) ≤ alphaDeg lam * Real.log n) ≤
      m₀ ^ (-(lam / 2)) := by
  have hm₀pos : 0 < m₀ := by
    have : 0 < 4 / lam := by positivity
    linarith
  have hlogm : (1 + lam) * Real.log A.ncard ≤ p * A.ncard :=
    lazyFinalAux_log_le_of_le hm₀pos hA (by linarith) hlog hpm₀
  -- Lemma A.4 with `ε = λ`, for `G(|A|, p)`
  have hA4 := lemmaA_4 hlam (le_trans hm₀ hA) hp0 hp1 hlogm
  have hα0 : 0 < alphaDeg lam := Real.exp_pos _
  have hsub : ∀ G : SimpleGraph (Fin n),
      (∃ v ∈ A, (nbrCount G A v : ℝ) ≤ alphaDeg lam * Real.log n) →
        ¬ ∀ i, Real.exp (-(8 / lam + 7)) * p * A.ncard ≤ degree (inducedOn G A) i := by
    rintro G ⟨v, hvA, hv⟩ hall
    rw [← range_enumSet A] at hvA
    obtain ⟨i, rfl⟩ := hvA
    have h1 := hall i
    rw [degree_inducedOn] at h1
    have h2 : alphaDeg lam * Real.log n < alphaDeg lam * (p * A.ncard) :=
      mul_lt_mul_of_pos_left (lt_of_lt_of_le hL (mul_le_mul_of_nonneg_left hA hp0.le)) hα0
    have h3 : Real.exp (-(8 / lam + 7)) * p * A.ncard = alphaDeg lam * (p * A.ncard) := by
      unfold alphaDeg
      ring
    linarith
  calc gnpProb n p (fun G => ∃ v ∈ A, (nbrCount G A v : ℝ) ≤ alphaDeg lam * Real.log n)
      ≤ gnpProb n p (fun G => ¬ ∀ i, Real.exp (-(8 / lam + 7)) * p * A.ncard ≤
          degree (inducedOn G A) i) := gnpProb_mono hsub
    _ = gnpProb A.ncard p (fun H => ¬ ∀ i, Real.exp (-(8 / lam + 7)) * p * A.ncard ≤
          degree H i) :=
        gnpProb_inducedOn A p (fun H => ¬ ∀ i, Real.exp (-(8 / lam + 7)) * p * A.ncard ≤
          degree H i)
    _ = 1 - gnpProb A.ncard p (fun H => ∀ i, Real.exp (-(8 / lam + 7)) * p * A.ncard ≤
          degree H i) := gnpProb_not _
    _ ≤ (A.ncard : ℝ) ^ (-(lam / 2)) := by linarith
    _ ≤ m₀ ^ (-(lam / 2)) := Real.rpow_le_rpow_of_nonpos hm₀pos hA (by linarith)

/-- Step 3 of the proof of Proposition 4.4, for one day: conditioning on the day's coins
(`prod_dayLaw_real_eq_sum`), some active vertex has at most `α_λ log n` active neighbours with
probability at most `m₀^(−λ/2)` (`lazyFinalAux_good`) plus the probability that fewer than `m₀`
vertices are active. -/
private lemma lazyFinalAux_day {n : ℕ} {lam p pac pup m₀ : ℝ} (hlam : 0 < lam) (hp0 : 0 < p)
    (hp1 : p ≤ 1) (hm₀ : 4 / lam + 4 ≤ m₀) (hlog : (1 + lam) * Real.log m₀ ≤ p * m₀)
    (hpm₀ : 1 + lam ≤ p * m₀) (hL : Real.log n < p * m₀) :
    ((SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod (dayLaw n pac pup)).real
      {x | ∃ v ∈ actSet x.2, (nbrCount x.1 (actSet x.2) v : ℝ) ≤ alphaDeg lam * Real.log n} ≤
      m₀ ^ (-(lam / 2)) + (dayLaw n pac pup).real {d | ((actSet d).ncard : ℝ) < m₀} := by
  classical
  have hm₀pos : 0 < m₀ := by
    have : 0 < 4 / lam := by positivity
    linarith
  have hB0 : 0 ≤ m₀ ^ (-(lam / 2)) := Real.rpow_nonneg hm₀pos.le _
  rw [prod_dayLaw_real_eq_sum (fun G d => ∃ v ∈ actSet d,
    (nbrCount G (actSet d) v : ℝ) ≤ alphaDeg lam * Real.log n)]
  have hpt : ∀ d : DayCoins n, gnpProb n p (fun G => ∃ v ∈ actSet d,
      (nbrCount G (actSet d) v : ℝ) ≤ alphaDeg lam * Real.log n) ≤
      m₀ ^ (-(lam / 2)) + (if ((actSet d).ncard : ℝ) < m₀ then 1 else 0) := by
    intro d
    split_ifs with hd
    · linarith [gnpProb_le_one (n := n) (p := p) (fun G => ∃ v ∈ actSet d,
        (nbrCount G (actSet d) v : ℝ) ≤ alphaDeg lam * Real.log n)]
    · rw [add_zero]
      exact lazyFinalAux_good hlam hp0 hp1 hm₀ hlog hpm₀ hL (actSet d) (not_lt.mp hd)
  calc ∑ d : DayCoins n, (dayLaw n pac pup).real {d} * gnpProb n p (fun G => ∃ v ∈ actSet d,
        (nbrCount G (actSet d) v : ℝ) ≤ alphaDeg lam * Real.log n)
      ≤ ∑ d : DayCoins n, (dayLaw n pac pup).real {d} *
          (m₀ ^ (-(lam / 2)) + (if ((actSet d).ncard : ℝ) < m₀ then 1 else 0)) :=
        Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (hpt d) measureReal_nonneg
    _ = m₀ ^ (-(lam / 2)) * ∑ d : DayCoins n, (dayLaw n pac pup).real {d} +
          ∑ d ∈ Finset.univ.filter (fun d : DayCoins n => ((actSet d).ncard : ℝ) < m₀),
            (dayLaw n pac pup).real {d} := by
        rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d _ => ?_
        split_ifs <;> ring
    _ = m₀ ^ (-(lam / 2)) + (dayLaw n pac pup).real {d | ((actSet d).ncard : ℝ) < m₀} := by
        rw [sum_measureReal_singleton, sum_measureReal_singleton, Finset.coe_univ,
          probReal_univ, mul_one, Finset.coe_filter]
        simp

/-- Step 3 of the proof of Proposition 4.4 over `T` days: by the union bound and
`lazyFinalAux_day` (the event of one day depends on the graph and that day's coins only,
`lazyProb_eq_of_day`). -/
private lemma lazyFinalAux_degree_event {n : ℕ} {lam p pac pup m₀ : ℝ} (hlam : 0 < lam)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hm₀ : 4 / lam + 4 ≤ m₀)
    (hlog : (1 + lam) * Real.log m₀ ≤ p * m₀) (hpm₀ : 1 + lam ≤ p * m₀)
    (hL : Real.log n < p * m₀) (T : ℕ) :
    lazyProb n p pac pup (fun G c => ∃ t ∈ Finset.range T, ∃ v ∈ actSet (c t),
      (nbrCount G (actSet (c t)) v : ℝ) ≤ alphaDeg lam * Real.log n) ≤
      (T : ℝ) * (m₀ ^ (-(lam / 2)) +
        (dayLaw n pac pup).real {d | ((actSet d).ncard : ℝ) < m₀}) := by
  refine le_trans (lazyProb_exists_le _ _) ?_
  have hday : ∀ t ∈ Finset.range T, lazyProb n p pac pup (fun G c => ∃ v ∈ actSet (c t),
      (nbrCount G (actSet (c t)) v : ℝ) ≤ alphaDeg lam * Real.log n) ≤
      m₀ ^ (-(lam / 2)) + (dayLaw n pac pup).real {d | ((actSet d).ncard : ℝ) < m₀} := by
    intro t _
    rw [lazyProb_eq_of_day t (fun G d => ∃ v ∈ actSet d,
      (nbrCount G (actSet d) v : ℝ) ≤ alphaDeg lam * Real.log n)]
    exact lazyFinalAux_day hlam hp0 hp1 hm₀ hlog hpm₀ hL
  refine le_trans (Finset.sum_le_sum hday) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The number of active vertices as a sum of indicators. -/
private lemma lazyFinalAux_ncard_act {n : ℕ} (d : DayCoins n) :
    ((actSet d).ncard : ℝ) = ∑ v, (if d.1 v then (1 : ℝ) else 0) := by
  classical
  rw [Finset.sum_boole, Set.ncard_eq_toFinset_card']
  congr 2
  ext v
  simp

/-- The concentration step that the paper leaves out: by Chernoff's lower tail (the sparse
paper's `(30)`), fewer than `(1 − η) p_ac n` vertices are active with probability at most
`exp(−η² p_ac n / 2)`. -/
private lemma lazyFinalAux_bad {n : ℕ} {pac pup η : ℝ} (hpac0 : 0 < pac) (hpac1 : pac ≤ 1)
    (hη : 0 < η) (hn : (0 : ℝ) < n) :
    (dayLaw n pac pup).real {d | ((actSet d).ncard : ℝ) < (1 - η) * pac * n} ≤
      Real.exp (-(η ^ 2 * pac * n / 2)) := by
  classical
  have hX := isBernoulliFamily_act (n := n) (pup := pup) hpac0.le hpac1
  have hcard : ((Finset.univ : Finset (Fin n)).card : ℝ) = n := by simp
  have hT : (1 - η) * pac * n < pac * (Finset.univ : Finset (Fin n)).card := by
    rw [hcard]
    have : 0 < η * pac * n := by positivity
    linarith
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
    (le_trans (hX.measureReal_sum_le_le_exp hpac0.le hpac1 Finset.univ hT) (le_of_eq ?_))
  · intro d hd
    simp only [Set.mem_ofPred_eq] at hd ⊢
    rw [lazyFinalAux_ncard_act] at hd
    exact hd.le
  · rw [hcard]
    congr 1
    field_simp
    ring

/-- With `p_ac = 1`, all `n` vertices are active almost surely. -/
private lemma lazyFinalAux_bad_one {n : ℕ} {pup : ℝ} :
    (dayLaw n 1 pup).real {d | ((actSet d).ncard : ℝ) < n} = 0 := by
  classical
  have hX := isBernoulliFamily_act (n := n) (pup := pup) zero_le_one le_rfl
  have hb : (n : ℝ) - 1 / 2 < (Finset.univ : Finset (Fin n)).card := by simp
  refine le_antisymm ?_ measureReal_nonneg
  calc (dayLaw n 1 pup).real {d | ((actSet d).ncard : ℝ) < n}
      ≤ (dayLaw n 1 pup).real
          {d | ∑ v ∈ Finset.univ, (if d.1 v then (1 : ℝ) else 0) ≤ n - 1 / 2} := by
        refine measureReal_mono (fun d hd => ?_) (measure_ne_top _ _)
        simp only [Set.mem_ofPred_eq] at hd ⊢
        rw [← lazyFinalAux_ncard_act]
        have h1 : (actSet d).ncard < n := by exact_mod_cast hd
        have h2 : ((actSet d).ncard : ℝ) + 1 ≤ n := by exact_mod_cast h1
        linarith
    _ = 0 := lazyFinalAux_measureReal_sum_le_of_one hX Finset.univ hb

/-- `K (log n + 1)^k ≤ n^b` for large `n`. -/
private lemma lazyFinalAux_eventually_polylog (k : ℕ) (K : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ n : ℕ in Filter.atTop, K * (Real.log n + 1) ^ k ≤ (n : ℝ) ^ b := by
  set e := b / (2 * (k + 1)) with he
  have he0 : 0 < e := by positivity
  have hek : e * k ≤ b / 2 := by
    calc e * k ≤ e * (k + 1) := mul_le_mul_of_nonneg_left (by linarith) he0.le
      _ = b / 2 := by
          rw [he]
          field_simp
  have hpow := (tendsto_rpow_atTop (by positivity : 0 < b / 2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hpow.eventually_ge_atTop (|K| * (1 / e + 1) ^ k + 1),
    Filter.eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by linarith
  simp only [Function.comp_apply] at hn
  have hlog := Real.log_le_rpow_div hnpos.le he0
  have h1 : 1 ≤ (n : ℝ) ^ e := Real.one_le_rpow hn1' he0.le
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg hn1'
  have h2 : Real.log n + 1 ≤ (1 / e + 1) * (n : ℝ) ^ e := by
    have : (n : ℝ) ^ e / e = 1 / e * (n : ℝ) ^ e := by ring
    nlinarith
  have h3 : (Real.log n + 1) ^ k ≤ (1 / e + 1) ^ k * (n : ℝ) ^ (b / 2) := by
    have e1 : ((n : ℝ) ^ e) ^ k ≤ (n : ℝ) ^ (b / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      exact Real.rpow_le_rpow_of_exponent_le hn1' hek
    calc (Real.log n + 1) ^ k ≤ ((1 / e + 1) * (n : ℝ) ^ e) ^ k :=
          pow_le_pow_left₀ (by positivity) h2 k
      _ = (1 / e + 1) ^ k * ((n : ℝ) ^ e) ^ k := mul_pow _ _ _
      _ ≤ (1 / e + 1) ^ k * (n : ℝ) ^ (b / 2) :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
  have h4 : (n : ℝ) ^ b = (n : ℝ) ^ (b / 2) * (n : ℝ) ^ (b / 2) := by
    rw [← Real.rpow_add hnpos]
    ring_nf
  have h5 : 0 ≤ (n : ℝ) ^ (b / 2) := by positivity
  calc K * (Real.log n + 1) ^ k ≤ |K| * (Real.log n + 1) ^ k :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    _ ≤ |K| * ((1 / e + 1) ^ k * (n : ℝ) ^ (b / 2)) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg K)
    _ ≤ (n : ℝ) ^ (b / 2) * (n : ℝ) ^ (b / 2) := by
        nlinarith [mul_le_mul_of_nonneg_right hn h5]
    _ = (n : ℝ) ^ b := h4.symm

/-- `x n^(−2a) ≤ n^(−a)` when `x ≤ n^a`. -/
private lemma lazyFinalAux_mul_rpow_le {n : ℕ} {x a : ℝ} (hn : (0 : ℝ) < n)
    (hx : x ≤ (n : ℝ) ^ a) : x * (n : ℝ) ^ (-(2 * a)) ≤ (n : ℝ) ^ (-a) := by
  have e1 : (n : ℝ) ^ (-(2 * a)) = (n : ℝ) ^ (-a) * (n : ℝ) ^ (-a) := by
    rw [← Real.rpow_add hn]
    ring_nf
  have e2 : (n : ℝ) ^ a * (n : ℝ) ^ (-a) = 1 := by
    rw [Real.rpow_neg hn.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hn _).ne']
  have h0 : 0 ≤ (n : ℝ) ^ (-a) := Real.rpow_nonneg hn.le _
  rw [e1]
  calc x * ((n : ℝ) ^ (-a) * (n : ℝ) ^ (-a)) ≤
        (n : ℝ) ^ a * ((n : ℝ) ^ (-a) * (n : ℝ) ^ (-a)) :=
        mul_le_mul_of_nonneg_right hx (mul_nonneg h0 h0)
    _ = (n : ℝ) ^ (-a) := by rw [← mul_assoc, e2, one_mul]

/-- The deterministic facts about `m₀ = (1 − η) p_ac n`, `η = log(1/p_ac) / (2 log n)`, for
large `n`: Lemma A.4 applies to `G(m, p)` for every `m ≥ m₀` (`lazyFinalAux_log_le_of_le`),
`p m₀ > log n`, and `m₀ ≥ p_ac n / 2`. -/
private lemma lazyFinalAux_m₀ {n : ℕ} {lam p pac : ℝ} (hlam : 0 < lam) (hpac0 : 0 < pac)
    (hpac1 : pac ≤ 1) (hpn : (1 + lam) * Real.log n ≤ p * pac * n)
    (h1 : 2 ≤ Real.log n) (h2 : Real.log (1 / pac) ≤ Real.log n)
    (h3 : 2 * (4 / lam + 4) / pac ≤ n)
    (h4 : (1 + lam) * Real.log (1 / pac) < 2 * lam * Real.log n) :
    4 / lam + 4 ≤ (1 - Real.log (1 / pac) / (2 * Real.log n)) * pac * n ∧
      (1 + lam) * Real.log ((1 - Real.log (1 / pac) / (2 * Real.log n)) * pac * n) ≤
        p * ((1 - Real.log (1 / pac) / (2 * Real.log n)) * pac * n) ∧
      1 + lam ≤ p * ((1 - Real.log (1 / pac) / (2 * Real.log n)) * pac * n) ∧
      Real.log n < p * ((1 - Real.log (1 / pac) / (2 * Real.log n)) * pac * n) ∧
      pac * n / 2 ≤ (1 - Real.log (1 / pac) / (2 * Real.log n)) * pac * n := by
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) h3
  set L := Real.log n with hL
  set ℓ := Real.log (1 / pac) with hℓ
  have hL0 : 0 < L := by linarith
  have hL0' : L ≠ 0 := hL0.ne'
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (one_le_one_div hpac0 hpac1)
  set η := ℓ / (2 * L) with hη
  have hη0 : 0 ≤ η := div_nonneg hℓ0 (by linarith)
  have hη1 : η ≤ 1 / 2 := by
    rw [hη, div_le_iff₀ (by linarith)]
    linarith
  have hηL : η * L = ℓ / 2 := by
    rw [hη]
    field_simp
  have hpn' : 0 < pac * n := mul_pos hpac0 hnpos
  set m₀ := (1 - η) * pac * n with hm₀
  have hhalf : pac * n / 2 ≤ m₀ := by
    have := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) / 2 ≤ 1 - η) hpn'.le
    rw [hm₀]
    linarith
  have hm₀pos : 0 < m₀ := by linarith
  have hA4 : 4 / lam + 4 ≤ m₀ := by
    rw [div_le_iff₀ hpac0] at h3
    linarith
  -- `p m₀ ≥ (1 − η)(1 + λ) log n = (1 + λ) log n − (1 + λ) log(1/p_ac) / 2`
  have hpm : (1 + lam) * L - (1 + lam) * (ℓ / 2) ≤ p * m₀ := by
    have := mul_le_mul_of_nonneg_left hpn (by linarith : (0 : ℝ) ≤ 1 - η)
    have e : (1 - η) * ((1 + lam) * L) = (1 + lam) * L - (1 + lam) * (ℓ / 2) := by
      rw [← hηL]
      ring
    rw [hm₀]
    linarith
  -- `log m₀ ≤ log (p_ac n) = log n − log(1/p_ac)`
  have hlogm₀ : Real.log m₀ ≤ L - ℓ := by
    have hle : m₀ ≤ pac * n := by
      have := mul_le_mul_of_nonneg_right (by linarith : 1 - η ≤ (1 : ℝ)) hpn'.le
      rw [hm₀]
      linarith
    have h := Real.log_le_log hm₀pos hle
    rw [Real.log_mul hpac0.ne' hnpos.ne'] at h
    have : Real.log pac = -ℓ := by
      rw [hℓ, one_div, Real.log_inv, neg_neg]
    linarith
  have hℓ1 : 0 ≤ (1 + lam) * ℓ := mul_nonneg (by linarith) hℓ0
  refine ⟨hA4, ?_, ?_, ?_, hhalf⟩
  · have := mul_le_mul_of_nonneg_left hlogm₀ (by linarith : (0 : ℝ) ≤ 1 + lam)
    linarith
  · have h5 : 1 ≤ L - ℓ / 2 := by linarith
    have := mul_le_mul_of_nonneg_left h5 (by linarith : (0 : ℝ) ≤ 1 + lam)
    linarith
  · linarith

/-- The number of days `⌈A₁ L / q⌉ + ⌈L⌉` is at most `(A₁/q + 3)(L + 1)²`. -/
private lemma lazyFinalAux_T_le {L q A₁ : ℝ} (hL0 : 0 ≤ L) (hq0 : 0 < q) (hA₁ : 0 < A₁) :
    ((⌈A₁ * L / q⌉₊ + ⌈1 * L⌉₊ : ℕ) : ℝ) ≤ (A₁ / q + 3) * (L + 1) ^ 2 := by
  have hT₁ : (⌈A₁ * L / q⌉₊ : ℝ) < A₁ * L / q + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hA₁.le hL0) hq0.le)
  have hT₂ : (⌈1 * L⌉₊ : ℝ) < 1 * L + 1 := Nat.ceil_lt_add_one (by linarith)
  have hAq : A₁ * L / q = A₁ / q * L := by ring
  have hAq0 : 0 ≤ A₁ / q := div_nonneg hA₁.le hq0.le
  have hsq : L ≤ (L + 1) ^ 2 := by nlinarith
  have hsq1 : 1 ≤ (L + 1) ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left hsq hAq0
  push_cast
  linarith

/-- The degree failures of the `T` days, first part: `T m₀^(−λ/2) ≤ n^(−λ/4) / 2` when
`m₀ ≥ p_ac n / 2` and `2 (2/p_ac)^(λ/2) T ≤ n^(λ/4)`. -/
private lemma lazyFinalAux_term_m₀ {n : ℕ} {lam pac m₀ T : ℝ} (hlam : 0 < lam)
    (hpac0 : 0 < pac) (hn : (0 : ℝ) < n) (hm : pac * n / 2 ≤ m₀) (hT0 : 0 ≤ T)
    (hT : 2 * (2 / pac) ^ (lam / 2) * T ≤ (n : ℝ) ^ (lam / 4)) :
    T * m₀ ^ (-(lam / 2)) ≤ (n : ℝ) ^ (-(lam / 4)) / 2 := by
  have hpos : 0 < pac * n / 2 := by positivity
  have h1 : m₀ ^ (-(lam / 2)) ≤ (pac * n / 2) ^ (-(lam / 2)) :=
    Real.rpow_le_rpow_of_nonpos hpos hm (by linarith)
  have h2 : (pac * n / 2) ^ (-(lam / 2)) =
      (2 / pac) ^ (lam / 2) * (n : ℝ) ^ (-(2 * (lam / 4))) := by
    rw [show pac * (n : ℝ) / 2 = pac / 2 * n by ring, Real.mul_rpow (by positivity) hn.le,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ pac / 2), ← Real.inv_rpow (by positivity),
      inv_div, show -(2 * (lam / 4)) = -(lam / 2) by ring]
  have h3 := lazyFinalAux_mul_rpow_le hn hT
  have h4 : T * m₀ ^ (-(lam / 2)) ≤
      T * ((2 / pac) ^ (lam / 2) * (n : ℝ) ^ (-(2 * (lam / 4)))) := by
    rw [← h2]
    exact mul_le_mul_of_nonneg_left h1 hT0
  have e : T * ((2 / pac) ^ (lam / 2) * (n : ℝ) ^ (-(2 * (lam / 4)))) =
      2 * (2 / pac) ^ (lam / 2) * T * (n : ℝ) ^ (-(2 * (lam / 4))) / 2 := by ring
  linarith

/-- The degree failures of the `T` days, second part: `T β ≤ n^(−λ/4) / 2`, where `β` is the
probability that fewer than `m₀` vertices are active: `β = 0` if `p_ac = 1`
(`lazyFinalAux_bad_one`), and otherwise `β ≤ exp(−η² p_ac n / 2) ≤ n^(−λ/4 − 1)` for large `n`
(`lazyFinalAux_bad`). -/
private lemma lazyFinalAux_term_beta {n : ℕ} {lam pac pup T : ℝ} (hlam : 0 < lam)
    (hpac0 : 0 < pac) (hpac1 : pac ≤ 1) (h1 : 2 ≤ Real.log n) (hT0 : 0 ≤ T) (hTn : 2 * T ≤ n)
    (h5 : 8 * (lam / 4 + 1) / (Real.log (1 / pac) ^ 2 * pac) * (Real.log n + 1) ^ 3 ≤ n) :
    T * (dayLaw n pac pup).real {d | ((actSet d).ncard : ℝ) <
      (1 - Real.log (1 / pac) / (2 * Real.log n)) * pac * n} ≤
      (n : ℝ) ^ (-(lam / 4)) / 2 := by
  have hL0 : 0 < Real.log n := by linarith
  have hnpos : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      norm_num at h1
    · exact_mod_cast h
  have hB0 : 0 ≤ (n : ℝ) ^ (-(lam / 4)) := Real.rpow_nonneg hnpos.le _
  rcases lt_or_eq_of_le hpac1 with hlt | heq
  · -- `p_ac < 1`: Chernoff's lower tail
    set ℓ := Real.log (1 / pac) with hℓ
    have hℓ0 : 0 < ℓ := Real.log_pos (one_lt_one_div hpac0 hlt)
    set η := ℓ / (2 * Real.log n) with hη
    have hη0 : 0 < η := div_pos hℓ0 (by linarith)
    have hbad := lazyFinalAux_bad (pup := pup) hpac0 hpac1 hη0 hnpos
    have hK : 8 * (lam / 4 + 1) * (Real.log n + 1) ^ 3 ≤ ℓ ^ 2 * pac * n := by
      have hpos : 0 < ℓ ^ 2 * pac := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos] at h5
      linarith
    have hL3 : Real.log n ^ 3 ≤ (Real.log n + 1) ^ 3 := pow_le_pow_left₀ hL0.le (by linarith) 3
    have hexp : Real.exp (-(η ^ 2 * pac * n / 2)) ≤ (n : ℝ) ^ (-(lam / 4 + 1)) := by
      rw [Real.rpow_def_of_pos hnpos]
      apply Real.exp_le_exp.mpr
      have e : η ^ 2 * pac * n / 2 = ℓ ^ 2 * pac * n / (8 * Real.log n ^ 2) := by
        rw [hη]
        field_simp
        ring
      have key : (lam / 4 + 1) * Real.log n ≤ ℓ ^ 2 * pac * n / (8 * Real.log n ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_left hL3 (by positivity : (0 : ℝ) ≤ 8 * (lam / 4 + 1))
        nlinarith
      rw [e]
      linarith
    have hsplit : (n : ℝ) ^ (-(lam / 4 + 1)) = (n : ℝ) ^ (-(lam / 4)) * (n : ℝ)⁻¹ := by
      rw [show -(lam / 4 + 1) = -(lam / 4) + -1 by ring, Real.rpow_add hnpos, Real.rpow_neg_one]
    have hβ := le_trans hbad hexp
    calc T * (dayLaw n pac pup).real {d | ((actSet d).ncard : ℝ) < (1 - η) * pac * n}
        ≤ T * (n : ℝ) ^ (-(lam / 4 + 1)) := mul_le_mul_of_nonneg_left hβ hT0
      _ = T / n * (n : ℝ) ^ (-(lam / 4)) := by
          rw [hsplit]
          ring
      _ ≤ 1 / 2 * (n : ℝ) ^ (-(lam / 4)) := by
          apply mul_le_mul_of_nonneg_right _ hB0
          rw [div_le_iff₀ hnpos]
          linarith
      _ = (n : ℝ) ^ (-(lam / 4)) / 2 := by ring
  · -- `p_ac = 1`: all vertices are active almost surely
    subst heq
    have h0 : Real.log (1 / 1) = 0 := by simp
    rw [h0, zero_div, sub_zero, one_mul, one_mul, lazyFinalAux_bad_one, mul_zero]
    positivity

/-- The never-updating failures: `(T₁ + 1) (α log n / 2) n^(−q) ≤ n^(−q/2)` once
`(A₁/q + 3)(log n + 1)² ≤ n^(q/2)`. -/
private lemma lazyFinalAux_term_upd {n : ℕ} {q A₁ α : ℝ} (hn : (0 : ℝ) < n)
    (hL0 : 0 ≤ Real.log n) (hq0 : 0 < q) (hA₁ : 0 < A₁) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (h7 : (A₁ / q + 3) * (Real.log n + 1) ^ 2 ≤ (n : ℝ) ^ (q / 2)) :
    ((⌈A₁ * Real.log n / q⌉₊ + 1 : ℕ) : ℝ) * (α * Real.log n / 2 * (n : ℝ) ^ (-q)) ≤
      (n : ℝ) ^ (-(q / 2)) := by
  set L := Real.log n with hL
  have hT₁' : (⌈A₁ * L / q⌉₊ : ℝ) < A₁ * L / q + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hA₁.le hL0) hq0.le)
  have hAq : A₁ * L / q = A₁ / q * L := by ring
  have hAq0 : 0 ≤ A₁ / q := div_nonneg hA₁.le hq0.le
  have hsq : L ≤ (L + 1) ^ 2 := by nlinarith
  have hsq2 : L * L / 2 ≤ (L + 1) ^ 2 := by nlinarith
  have h2 : ((⌈A₁ * L / q⌉₊ + 1 : ℕ) : ℝ) * (α * L / 2) ≤ (n : ℝ) ^ (q / 2) := by
    push_cast
    have hαL : α * L / 2 ≤ L / 2 := by
      have := mul_le_mul_of_nonneg_right hα1 hL0
      linarith
    have hT1 : (⌈A₁ * L / q⌉₊ : ℝ) + 1 ≤ A₁ / q * L + 2 := by linarith
    have hαL0 : 0 ≤ α * L / 2 := div_nonneg (mul_nonneg hα0 hL0) (by norm_num)
    calc ((⌈A₁ * L / q⌉₊ : ℝ) + 1) * (α * L / 2) ≤ (A₁ / q * L + 2) * (L / 2) :=
          mul_le_mul hT1 hαL hαL0 (by nlinarith)
      _ ≤ (A₁ / q + 3) * (L + 1) ^ 2 := by
          have := mul_le_mul_of_nonneg_left hsq2 hAq0
          have e : (A₁ / q * L + 2) * (L / 2) = A₁ / q * (L * L / 2) + L := by ring
          rw [e]
          linarith
      _ ≤ _ := h7
  have e2 : -q = -(2 * (q / 2)) := by ring
  rw [e2, ← mul_assoc]
  exact lazyFinalAux_mul_rpow_le hn h2

/-- The conditions on large `n` in the proof of Proposition 4.4. -/
private lemma lazyFinalAux_large {A₁ lam pac pup : ℝ} (hlam : 0 < lam) (hpac0 : 0 < pac)
    (hpup0 : 0 < pup) :
    ∃ N : ℕ, ∀ n ≥ N, 2 ≤ Real.log n ∧ Real.log (1 / pac) ≤ Real.log n ∧
      2 * (4 / lam + 4) / pac ≤ n ∧ (1 + lam) * Real.log (1 / pac) < 2 * lam * Real.log n ∧
      8 * (lam / 4 + 1) / (Real.log (1 / pac) ^ 2 * pac) * (Real.log n + 1) ^ 3 ≤ n ∧
      2 * (2 / pac) ^ (lam / 2) * (A₁ / (pup * pac) + 3) * (Real.log n + 1) ^ 2 ≤
        (n : ℝ) ^ (lam / 4) ∧
      (A₁ / (pup * pac) + 3) * (Real.log n + 1) ^ 2 ≤ (n : ℝ) ^ (pup * pac / 2) ∧
      2 * (A₁ / (pup * pac) + 3) * (Real.log n + 1) ^ 2 ≤ n := by
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log n) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have e4 : ∀ᶠ n : ℕ in Filter.atTop,
      (1 + lam) * Real.log (1 / pac) / (2 * lam) < Real.log n := hlog.eventually_gt_atTop _
  have e5 := lazyFinalAux_eventually_polylog 3
    (8 * (lam / 4 + 1) / (Real.log (1 / pac) ^ 2 * pac)) one_pos
  have e6 := lazyFinalAux_eventually_polylog 2
    (2 * (2 / pac) ^ (lam / 2) * (A₁ / (pup * pac) + 3)) (by positivity : 0 < lam / 4)
  have e7 := lazyFinalAux_eventually_polylog 2 (A₁ / (pup * pac) + 3)
    (by positivity : 0 < pup * pac / 2)
  have e8 := lazyFinalAux_eventually_polylog 2 (2 * (A₁ / (pup * pac) + 3)) one_pos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((hlog.eventually_ge_atTop 2).and
    ((hlog.eventually_ge_atTop (Real.log (1 / pac))).and
      (((tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
        (2 * (4 / lam + 4) / pac)).and (e4.and (e5.and (e6.and (e7.and e8)))))))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hN n hn
  rw [Real.rpow_one] at a5 a8
  refine ⟨a1, a2, a3, ?_, a5, a6, a7, a8⟩
  rw [div_lt_iff₀ (by positivity)] at a4
  linarith

/-- Proposition 4.4 for one `n` satisfying the conditions of `lazyFinalAux_large`. -/
private lemma lazyFinalAux_main {n : ℕ} {A₁ lam pac pup p : ℝ} (B₀ : Set (Fin n))
    (hA₁ : 0 < A₁) (hlam : 0 < lam) (hpac0 : 0 < pac) (hpac1 : pac ≤ 1) (hpup0 : 0 < pup)
    (hpup1 : pup ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1) (hpn : (1 + lam) * Real.log n ≤ p * pac * n)
    (h1 : 2 ≤ Real.log n) (h2 : Real.log (1 / pac) ≤ Real.log n)
    (h3 : 2 * (4 / lam + 4) / pac ≤ n)
    (h4 : (1 + lam) * Real.log (1 / pac) < 2 * lam * Real.log n)
    (h5 : 8 * (lam / 4 + 1) / (Real.log (1 / pac) ^ 2 * pac) * (Real.log n + 1) ^ 3 ≤ n)
    (h6 : 2 * (2 / pac) ^ (lam / 2) * (A₁ / (pup * pac) + 3) * (Real.log n + 1) ^ 2 ≤
      (n : ℝ) ^ (lam / 4))
    (h7 : (A₁ / (pup * pac) + 3) * (Real.log n + 1) ^ 2 ≤ (n : ℝ) ^ (pup * pac / 2))
    (h8 : 2 * (A₁ / (pup * pac) + 3) * (Real.log n + 1) ^ 2 ≤ n) :
    lazyProb n p pac pup (fun G c =>
      (∃ t₀ : ℕ, (t₀ : ℝ) ≤ A₁ * Real.log n / (pup * pac) ∧
        ((lazyBlueAfter G c B₀ t₀).ncard : ℝ) ≤ alphaDeg lam * Real.log n / 2) ∧
      lazyBlueAfter G c B₀ (⌈A₁ * Real.log n / (pup * pac)⌉₊ + ⌈1 * Real.log n⌉₊) ≠ ∅) ≤
      1 * (n : ℝ) ^ (-(lam / 4)) + 1 * (n : ℝ) ^ (-(pup * pac / 2)) := by
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) h3
  have hL0 : 0 ≤ Real.log n := by linarith
  have hq0 : 0 < pup * pac := mul_pos hpup0 hpac0
  have hα0 : 0 < alphaDeg lam := Real.exp_pos _
  have hα1 : alphaDeg lam ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 < 8 / lam := by positivity
    linarith)
  obtain ⟨hm4, hmlog, hm1, hmL, hmhalf⟩ :=
    lazyFinalAux_m₀ hlam hpac0 hpac1 hpn h1 h2 h3 h4
  have hT₂ : Real.log n ≤ (⌈1 * Real.log n⌉₊ : ℝ) := by
    have := Nat.le_ceil (1 * Real.log n)
    linarith
  have hT := lazyFinalAux_T_le (A₁ := A₁) hL0 hq0 hA₁
  have hT0 : (0 : ℝ) ≤ ((⌈A₁ * Real.log n / (pup * pac)⌉₊ + ⌈1 * Real.log n⌉₊ : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hT6 : 2 * (2 / pac) ^ (lam / 2) *
      ((⌈A₁ * Real.log n / (pup * pac)⌉₊ + ⌈1 * Real.log n⌉₊ : ℕ) : ℝ) ≤
      (n : ℝ) ^ (lam / 4) := by
    have := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ 2 * (2 / pac) ^ (lam / 2))
    linarith
  have hT8 : 2 * ((⌈A₁ * Real.log n / (pup * pac)⌉₊ + ⌈1 * Real.log n⌉₊ : ℕ) : ℝ) ≤ n := by
    linarith
  -- step 3: the degree failures
  have hdeg := lazyFinalAux_degree_event (pac := pac) (pup := pup) hlam hp0 hp1 hm4 hmlog hm1
    hmL (⌈A₁ * Real.log n / (pup * pac)⌉₊ + ⌈1 * Real.log n⌉₊)
  have hQ1 := lazyFinalAux_term_m₀ hlam hpac0 hnpos hmhalf hT0 hT6
  have hQ2 := lazyFinalAux_term_beta (pup := pup) hlam hpac0 hpac1 h1 hT0 hT8 h5
  -- step 2: the never-updating failures
  have hupd := lazyFinalAux_update_event (p := p) hpac0.le hpac1 hpup0.le hpup1
    (b := alphaDeg lam * Real.log n / 2) (by positivity) hnpos B₀
    ⌈A₁ * Real.log n / (pup * pac)⌉₊ ⌈1 * Real.log n⌉₊ hT₂
  have hQ3 := lazyFinalAux_term_upd hnpos hL0 hq0 hA₁ hα0.le hα1 h7
  refine le_trans (lazyProb_mono fun G c h =>
    lazyFinalAux_contain G c B₀ _ _ (Nat.le_ceil _) h) (le_trans (lazyProb_or_le _ _) ?_)
  linarith

/-- **Proposition 4.4** (`S:prop:lazy-final`; unlabelled in the paper). Under the assumptions of
Theorem 4.1 and `|B_{t*₁}| ≤ α_λ (log n)/2`, where `t*₁ = O(p_up⁻¹ p_ac⁻¹ log n)` comes from
Proposition 4.3, there is `t*₂ = t*₁ + O(log n)` such that Red wins after day `t*₂` with
probability at least `1 − O(n^(−λ/4)) − O(n^(−p_up p_ac / 2))`.

Reading: for every `A₁`, the probability that some day `t₀ ≤ A₁ log n / (p_up p_ac)` has
`|B_{t₀}| ≤ α_λ (log n)/2` while Blue is not empty on day
`⌈A₁ log n / (p_up p_ac)⌉ + ⌈A log n⌉` is at most `C n^(−λ/4) + C n^(−p_up p_ac / 2)`.

The proof (with `A = C = 1`) is the paper's. (1) If on each day of `[t₀, T)` every active vertex
has more than `α_λ log n` active neighbours and `|B_{t₀}| ≤ α_λ (log n)/2`, an updating vertex
sees fewer active Blue than active Red neighbours and turns Red, so a vertex that is Blue on day
`T` is in `B_{t₀}` and did not update on these days (`lazyFinalAux_mem_of_degree`). (2) Given the
graph and the days before `t₀`, one of the at most `α_λ (log n)/2` vertices of `B_{t₀}` does not
update on `k ≥ ⌈log n⌉` days with probability at most
`(α_λ (log n)/2) (1 − p_up p_ac)^k ≤ (α_λ (log n)/2) n^(−p_up p_ac)` (`lazyFinalAux_never_update`);
a union bound over `t₀ ≤ A₁ log n / (p_up p_ac)` gives `O(n^(−p_up p_ac / 2))`. (3) On each day
`t`, given the set `A_t` of the `m` active vertices, the subgraph `G[A_t]` is `G(m, p)`, and
Lemma A.4 (`lemmaA_4`) with `ε = λ` gives it minimum degree at least `α_λ p m` except with
probability `m^(−λ/2)` (`lazyFinalAux_good`, `lazyFinalAux_day`); a union bound over the
`O(log n / (p_up p_ac))` days gives `O(n^(−λ/4))`.

Departure from the paper (gaps that the paper leaves in step (3), filled along its lines): Lemma A.4
needs `p m ≥ (1 + λ) log m`, which the paper does not check for `m = |A_t|`. With
`η = log(1/p_ac) / (2 log n)` and `m₀ = (1 − η) p_ac n`, it holds for every `m ≥ m₀` once `n` is
large (`lazyFinalAux_m₀`, `lazyFinalAux_log_le_of_le`), and Chernoff's lower tail bounds the
probability of `m < m₀` by `exp(−η² p_ac n / 2) = n^(−ω(1))` (`lazyFinalAux_bad`; if `p_ac = 1`,
then `m = n` almost surely, `lazyFinalAux_bad_one`). The paper's minimum degree
"`≥ α_λ p p_ac n`" is used in the form "every active vertex has more than `α_λ log n` active
neighbours", which follows from `α_λ p m ≥ α_λ p m₀ > α_λ log n` for large `n` and is what step (1)
needs. -/
theorem proposition4_4 :
    ∃ A C : ℝ, ∀ A₁ lam pac pup : ℝ, 0 < A₁ → 0 < lam → 0 < pac → pac ≤ 1 → 0 < pup → pup ≤ 1 →
      ∃ N : ℕ, ∀ n ≥ N, ∀ (p : ℝ) (B₀ : Set (Fin n)), 0 < p → p ≤ 1 →
        (1 + lam) * Real.log n ≤ p * pac * n →
        lazyProb n p pac pup (fun G c =>
          (∃ t₀ : ℕ, (t₀ : ℝ) ≤ A₁ * Real.log n / (pup * pac) ∧
            ((lazyBlueAfter G c B₀ t₀).ncard : ℝ) ≤ alphaDeg lam * Real.log n / 2) ∧
          lazyBlueAfter G c B₀ (⌈A₁ * Real.log n / (pup * pac)⌉₊ + ⌈A * Real.log n⌉₊) ≠ ∅) ≤
          C * (n : ℝ) ^ (-(lam / 4)) + C * (n : ℝ) ^ (-(pup * pac / 2)) := by
  refine ⟨1, 1, ?_⟩
  intro A₁ lam pac pup hA₁ hlam hpac0 hpac1 hpup0 hpup1
  obtain ⟨N, hN⟩ := lazyFinalAux_large (A₁ := A₁) hlam hpac0 hpup0
  refine ⟨N, ?_⟩
  intro n hn p B₀ hp0 hp1 hpn
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hN n hn
  exact lazyFinalAux_main B₀ hA₁ hlam hpac0 hpac1 hpup0 hpup1 hp0 hp1 hpn h1 h2 h3 h4 h5 h6 h7 h8

end PowerOfFew.Sparse

end
