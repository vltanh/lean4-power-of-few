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

/-- Products of two independent Bernoulli families on a product space form a Bernoulli family. -/
private lemma lazyFinalAux_isBernoulliFamily_prod {Ω₁ Ω₂ ι : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] [Fintype ι] {μ : Measure Ω₁} {ν : Measure Ω₂} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {p q : ℝ} {X : ι → Ω₁ → ℝ} {Z : ι → Ω₂ → ℝ}
    (hX : IsBernoulliFamily μ p X) (hZ : IsBernoulliFamily ν q Z) :
    IsBernoulliFamily (μ.prod ν) (p * q) (fun i ω => X i ω.1 * Z i ω.2) := by
  have hXm := hX.measurable
  have hZm := hZ.measurable
  have hWm : ∀ i, Measurable (fun ω : Ω₁ × Ω₂ => (X i ω.1, Z i ω.2)) := fun i =>
    ((hXm i).comp measurable_fst).prodMk ((hZm i).comp measurable_snd)
  -- the pairs `(X i, Z i)` are independent
  have hW : iIndepFun (fun i (ω : Ω₁ × Ω₂) => (X i ω.1, Z i ω.2)) (μ.prod ν) := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hWm i).aemeasurable)]
    have hX' := hX.indep.map_fun_eq_pi_map (fun i => (hXm i).aemeasurable)
    have hZ' := hZ.indep.map_fun_eq_pi_map (fun i => (hZm i).aemeasurable)
    have hXv : Measurable (fun (ω : Ω₁) (i : ι) => X i ω) := measurable_pi_iff.mpr hXm
    have hZv : Measurable (fun (ω : Ω₂) (i : ι) => Z i ω) := measurable_pi_iff.mpr hZm
    have hmarg : ∀ i, (μ.prod ν).map (fun ω : Ω₁ × Ω₂ => (X i ω.1, Z i ω.2)) =
        (μ.map (X i)).prod (ν.map (Z i)) := fun i => by
      rw [Measure.map_prod_map μ ν (hXm i) (hZm i)]
      rfl
    have hjoint : (fun (ω : Ω₁ × Ω₂) (i : ι) => (X i ω.1, Z i ω.2)) =
        (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι).symm ∘
          Prod.map (fun (ω : Ω₁) (i : ι) => X i ω) (fun (ω : Ω₂) (i : ι) => Z i ω) := by
      funext ω i
      rfl
    rw [hjoint, ← Measure.map_map (MeasurableEquiv.measurable _) (hXv.prodMap hZv),
      ← Measure.map_prod_map μ ν hXv hZv, hX', hZ',
      ((measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι (fun i => μ.map (X i))
        (fun i => ν.map (Z i))).symm _).map_eq]
    simp_rw [hmarg]
  refine ⟨fun i => ((hXm i).comp measurable_fst).mul ((hZm i).comp measurable_snd), ?_, ?_, ?_⟩
  · exact hW.comp (fun _ x => x.1 * x.2) (fun _ => measurable_fst.mul measurable_snd)
  · intro i ω
    rcases hX.zero_or_one i ω.1 with h | h <;> rcases hZ.zero_or_one i ω.2 with h' | h' <;>
      simp [h, h']
  · intro i
    have : {ω : Ω₁ × Ω₂ | X i ω.1 * Z i ω.2 = 1} =
        {ω₁ | X i ω₁ = 1} ×ˢ {ω₂ | Z i ω₂ = 1} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_prod]
      rcases hX.zero_or_one i ω.1 with h | h <;> rcases hZ.zero_or_one i ω.2 with h' | h' <;>
        simp [h, h']
    rw [this, measureReal_prod_prod, hX.prob_one, hZ.prob_one]

/-- Transferring a Bernoulli family along a measurable map. -/
private lemma lazyFinalAux_isBernoulliFamily_map {Ω Ω' ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [Fintype ι] {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → Ω'}
    (hg : Measurable g) {q : ℝ} {X : ι → Ω' → ℝ} (hXm : ∀ i, Measurable (X i))
    (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (hX : IsBernoulliFamily μ q (fun i ω => X i (g ω))) :
    IsBernoulliFamily (μ.map g) q X := by
  refine ⟨hXm, ?_, h01, ?_⟩
  · rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hXm i).aemeasurable),
      Measure.map_map (measurable_pi_iff.mpr hXm) hg,
      show ((fun ω i => X i ω) ∘ g) = fun ω i => X i (g ω) from rfl,
      hX.indep.map_fun_eq_pi_map (fun i => (hX.measurable i).aemeasurable)]
    congr 1
    funext i
    rw [Measure.map_map (hXm i) hg]
    rfl
  · intro i
    rw [show {ω | X i ω = 1} = X i ⁻¹' {1} from rfl,
      map_measureReal_apply hg (hXm i (measurableSet_singleton 1))]
    exact hX.prob_one i

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

open Classical in
/-- The edge indicators at `v` form a Bernoulli(`p`) family under `G(n, p)`. -/
private lemma lazyFinalAux_isBernoulliFamily_adj {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (v : Fin n) :
    IsBernoulliFamily (SimpleGraph.binomialRandom (Fin n) (toUnit p)) p
      (fun (u : {u : Fin n // u ≠ v}) (G : SimpleGraph (Fin n)) =>
        if G.Adj v u.1 then (1 : ℝ) else 0) := by
  rw [binomialRandom_eq_map_edgeLaw]
  refine lazyFinalAux_isBernoulliFamily_map measurable_graphOfEdges
    (fun u => fun s _ => measurableSet_simpleGraph _) (fun u G => by split_ifs <;> simp) ?_
  have e : (fun (u : {u : Fin n // u ≠ v}) (ω : EdgeVars n) =>
      if (graphOfEdges ω).Adj v u.1 then (1 : ℝ) else 0) = fun u => edgeInd s(v, u.1) := by
    funext u ω
    have hadj : (graphOfEdges ω).Adj v u.1 ↔ ω s(v, u.1) := by
      rw [adj_graphOfEdges]
      exact ⟨fun h => h.2, fun h => ⟨u.2.symm, h⟩⟩
    unfold edgeInd
    by_cases h : ω s(v, u.1) <;> simp [h, hadj]
  -- the edges at `v`, among the pairs of distinct vertices
  have hinj : Function.Injective
      (fun u : {u : Fin n // u ≠ v} => (⟨s(v, u.1), by
        rw [Sym2.mk_isDiag_iff]; exact u.2.symm⟩ : OffDiag n)) := by
    intro u u' h
    exact Subtype.ext (Sym2.congr_right.mp (congrArg Subtype.val h))
  have h := (isBernoulliFamily_edgeInd (n := n) hp0 hp1).comp hinj
  rw [← e] at h
  exact h

open Classical in
/-- The indicators `1[u ∼ v] 1[u active]`, `u ≠ v`, form a Bernoulli(`p p_ac`) family under
`G(n, p) ⊗ dayLaw`: the number of active neighbours of `v` is `Bin(n − 1, p p_ac)`. -/
private lemma lazyFinalAux_isBernoulliFamily_actAdj {n : ℕ} {p pac pup : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hpac0 : 0 ≤ pac) (hpac1 : pac ≤ 1) (v : Fin n) :
    IsBernoulliFamily ((SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod (dayLaw n pac pup))
      (p * pac) (fun (u : {u : Fin n // u ≠ v}) x =>
        (if x.1.Adj v u.1 then (1 : ℝ) else 0) * (if x.2.1 u.1 then 1 else 0)) :=
  lazyFinalAux_isBernoulliFamily_prod (lazyFinalAux_isBernoulliFamily_adj hp0 hp1 v)
    ((isBernoulliFamily_act (pup := pup) hpac0 hpac1).comp Subtype.val_injective)

open Classical in
/-- The number of active neighbours of `v` as a sum of the indicators above. -/
private lemma lazyFinalAux_nbrCount_eq_sum {n : ℕ} (G : SimpleGraph (Fin n)) (d : DayCoins n)
    (v : Fin n) :
    (nbrCount G (actSet d) v : ℝ) = ∑ u : {u : Fin n // u ≠ v},
      (if G.Adj v u.1 then (1 : ℝ) else 0) * (if d.1 u.1 then 1 else 0) := by
  rw [← Finset.sum_subtype (Finset.univ.filter (· ≠ v)) (by simp)
    (fun u => (if G.Adj v u then (1 : ℝ) else 0) * (if d.1 u then 1 else 0))]
  simp_rw [ite_zero_mul_ite_zero, mul_one]
  rw [Finset.sum_boole]
  unfold nbrCount
  rw [Set.ncard_eq_toFinset_card']
  congr 2
  ext u
  simp only [Set.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(G.ne_of_adj h1).symm, h1, h2⟩
  · rintro ⟨_, h1, h2⟩
    exact ⟨h1, h2⟩

/-- There are `n − 1` vertices other than `v`. -/
private lemma lazyFinalAux_card_ne {n : ℕ} (v : Fin n) :
    ((Finset.univ : Finset {u : Fin n // u ≠ v}).card : ℝ) = n - 1 := by
  have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact v.elim0)
  rw [Finset.card_univ, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq,
    Nat.cast_sub h1, Nat.cast_one]

/-- The lower bound on the relative entropy in the proof of Lemma A.4:
`D(β r ‖ r) ≥ r (1 − β + β log β)` for `0 < r < 1` and `0 < β ≤ 1`. -/
private lemma lazyFinalAux_klBern_ge {r β : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) : r * (1 - β + β * Real.log β) ≤ klBern (β * r) r := by
  unfold klBern
  have hβr : β * r / r = β := by field_simp
  have h1 : 0 < 1 - β * r := by nlinarith
  have h2 : 0 < 1 - r := by linarith
  have hlog : 1 - (1 - r) / (1 - β * r) ≤ Real.log ((1 - β * r) / (1 - r)) := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos h1 h2)
    rwa [inv_div] at this
  have hmul : (1 - β * r) * (1 - (1 - r) / (1 - β * r)) = r - β * r := by
    field_simp
    ring
  have := mul_le_mul_of_nonneg_left hlog h1.le
  rw [hmul] at this
  rw [hβr]
  nlinarith

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
the days `t₀, …, t₀ + k − 1` every vertex has more than `b` active neighbours, then an updating
vertex sees fewer active Blue neighbours (at most `|B_t| ≤ b / 2`) than active Red ones (more than
`b − b / 2`), so it is Red the next day: `B_{t+1} = B_t \ (A_t ∩ U_t)`. Hence every vertex that is
Blue on day `t₀ + k` is Blue on day `t₀` and does not update on any of these days. -/
private lemma lazyFinalAux_mem_of_degree {n : ℕ} (G : SimpleGraph (Fin n)) (c : ℕ → DayCoins n)
    (B₀ : Set (Fin n)) (t₀ : ℕ) {b : ℝ}
    (hB : ((lazyBlueAfter G c B₀ t₀).ncard : ℝ) ≤ b / 2) :
    ∀ k : ℕ, (∀ s, t₀ ≤ s → s < t₀ + k → ∀ v, b < nbrCount G (actSet (c s)) v) →
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
      have hdegv := hdeg (t₀ + k) (by omega) (by omega) v
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

/-- `32 < e^7`. -/
private lemma lazyFinalAux_exp_seven : (32 : ℝ) < Real.exp 7 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have : (2 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) h2 7
  rw [← Real.exp_nat_mul] at this
  norm_num at this
  linarith

/-- The numeric fact of the proof of Lemma A.4: with `t = −log α_λ = 8/λ + 7`,
`α_λ (1 − log α_λ) = e^(−t) (1 + t) = 8 (1/λ + 1) e^(−8/λ − 7) < λ / (4 (1 + λ))`. -/
private lemma lazyFinalAux_alpha_bound {lam : ℝ} (hlam : 0 < lam) :
    alphaDeg lam * (1 - Real.log (alphaDeg lam)) < lam / (4 * (1 + lam)) := by
  unfold alphaDeg
  rw [Real.log_exp]
  have hE : Real.exp (-(8 / lam + 7)) = (Real.exp (8 / lam) * Real.exp 7)⁻¹ := by
    rw [Real.exp_neg, Real.exp_add]
  -- `(1 + 1/λ)² ≤ e^(2/λ) ≤ e^(8/λ)`
  have h1 : (1 + 1 / lam) ^ 2 ≤ Real.exp (8 / lam) := by
    have ha : 1 + 1 / lam ≤ Real.exp (1 / lam) := by linarith [Real.add_one_le_exp (1 / lam)]
    calc (1 + 1 / lam) ^ 2 ≤ Real.exp (1 / lam) ^ 2 := pow_le_pow_left₀ (by positivity) ha 2
      _ = Real.exp (2 * (1 / lam)) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ Real.exp (8 / lam) := Real.exp_le_exp.mpr (by
          rw [mul_one_div]
          exact div_le_div_of_nonneg_right (by norm_num) hlam.le)
  have h7 := lazyFinalAux_exp_seven
  have hX : 0 < (1 + lam) ^ 2 / lam := by positivity
  have hA : (1 + lam) ^ 2 / lam ≤ lam * Real.exp (8 / lam) := by
    have : (1 + lam) ^ 2 / lam = lam * (1 + 1 / lam) ^ 2 := by
      field_simp
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h1 hlam.le
  rw [hE, inv_mul_eq_div, div_lt_div_iff₀ (by positivity) (by positivity)]
  have hL : (1 - -(8 / lam + 7)) * (4 * (1 + lam)) = 32 * ((1 + lam) ^ 2 / lam) := by
    field_simp
    ring
  rw [hL]
  calc 32 * ((1 + lam) ^ 2 / lam) < Real.exp 7 * ((1 + lam) ^ 2 / lam) :=
        mul_lt_mul_of_pos_right h7 hX
    _ ≤ Real.exp 7 * (lam * Real.exp (8 / lam)) :=
        mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le
    _ = lam * (Real.exp (8 / lam) * Real.exp 7) := by ring

/-- `α_λ < 1/2`. -/
private lemma lazyFinalAux_alpha_lt {lam : ℝ} (hlam : 0 < lam) : alphaDeg lam < 1 / 2 := by
  unfold alphaDeg
  have h7 := lazyFinalAux_exp_seven
  calc Real.exp (-(8 / lam + 7)) ≤ Real.exp (-7) :=
        Real.exp_le_exp.mpr (by have : 0 < 8 / lam := by positivity
                                linarith)
    _ = (Real.exp 7)⁻¹ := Real.exp_neg 7
    _ < 1 / 2 := by
        rw [inv_eq_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
        linarith

/-- The last computation of the proof of Lemma A.4: with `α = α_λ`, `n ≥ 4/λ + 4` and
`r n ≥ (1 + λ) log n`, the union over the `n` vertices of the per-vertex bound
`exp(−r n (1 − α + α log α − 1/n))` is `e^(−T)` with `T ≥ T' log n`,
`T' = λ − (1 + λ) α (1 − log α) − (1 + λ)/n ≥ λ/2`; so it is at most `n^(−λ/2)`. -/
private lemma lazyFinalAux_A4_numeric {n : ℕ} {lam r : ℝ} (hlam : 0 < lam)
    (hn : 4 / lam + 4 ≤ n) (hrn : (1 + lam) * Real.log n ≤ r * n) :
    (n : ℝ) * Real.exp (-(r * n * (1 - alphaDeg lam + alphaDeg lam *
      Real.log (alphaDeg lam)) - r)) ≤ (n : ℝ) ^ (-(lam / 2)) := by
  set α := alphaDeg lam with hα
  have hnpos : (0 : ℝ) < n := by have : 0 < 4 / lam := by positivity
                                 linarith
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg (by have : 0 < 4 / lam := by positivity
                                                   linarith)
  set f := 1 - α + α * Real.log α with hf
  have hαb := lazyFinalAux_alpha_bound hlam
  rw [← hα] at hαb
  have h1 : (1 + lam) * (α * (1 - Real.log α)) < lam / 4 := by
    have := mul_lt_mul_of_pos_left hαb (by linarith : (0 : ℝ) < 1 + lam)
    rwa [show (1 + lam) * (lam / (4 * (1 + lam))) = lam / 4 by field_simp] at this
  have h2 : (1 + lam) / n ≤ lam / 4 := by
    rw [div_le_iff₀ hnpos]
    have : lam * (4 / lam + 4) = 4 + 4 * lam := by field_simp
    nlinarith
  -- `T' = (1 + λ)(f − 1/n) − 1 ≥ λ/2`
  have hT' : 1 + lam / 2 ≤ (1 + lam) * (f - 1 / n) := by
    have e : (1 + lam) * (f - 1 / n) = 1 + lam - (1 + lam) * (α * (1 - Real.log α)) -
        (1 + lam) / n := by rw [hf]; ring
    rw [e]
    linarith
  have hg0 : 0 ≤ f - 1 / n := by
    by_contra h
    push Not at h
    have : (1 + lam) * (f - 1 / n) < 0 := mul_neg_of_pos_of_neg (by linarith) h
    linarith
  -- `T = r n (f − 1/n) − log n ≥ (λ/2) log n`
  have hT : (1 + lam / 2) * Real.log n ≤ r * n * (f - 1 / n) := by
    calc (1 + lam / 2) * Real.log n ≤ (1 + lam) * (f - 1 / n) * Real.log n :=
          mul_le_mul_of_nonneg_right hT' hL0
      _ = (1 + lam) * Real.log n * (f - 1 / n) := by ring
      _ ≤ r * n * (f - 1 / n) := mul_le_mul_of_nonneg_right hrn hg0
  have e2 : r * n * f - r = r * n * (f - 1 / n) := by field_simp
  rw [e2, Real.rpow_def_of_pos hnpos]
  calc (n : ℝ) * Real.exp (-(r * n * (f - 1 / n))) =
        Real.exp (Real.log n - r * n * (f - 1 / n)) := by
        rw [Real.exp_sub, Real.exp_log hnpos, Real.exp_neg]
        ring
    _ ≤ Real.exp (Real.log n * -(lam / 2)) := Real.exp_le_exp.mpr (by nlinarith)

open Classical in
/-- Lemma A.4's bound for one vertex, for its active neighbours (the repair of the degree step of
Proposition 4.4). Under `G(n, p) ⊗ dayLaw`, the number of active neighbours of `v` is
`Bin(n − 1, r)`, `r = p p_ac` (`lazyFinalAux_isBernoulliFamily_actAdj`); as in the proof of
Lemma A.4, Chernoff's bound in relative-entropy form at `α n / (n − 1)` and
`D(β r ‖ r) ≥ r (1 − β + β log β)` show that it is at most `α r n` with probability at most
`exp(−r n (1 − α + α log α − 1/n))`. -/
private lemma lazyFinalAux_vertex {n : ℕ} {p pac pup α : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hpac0 : 0 < pac) (hpac1 : pac ≤ 1) (hα0 : 0 < α) (hα : α < 1 / 2) (hn : 2 ≤ n)
    (v : Fin n) :
    ((SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod (dayLaw n pac pup)).real
      {x | (nbrCount x.1 (actSet x.2) v : ℝ) ≤ α * (p * pac) * n} ≤
      Real.exp (-(p * pac * n * (1 - α + α * Real.log α) - p * pac)) := by
  have hY := lazyFinalAux_isBernoulliFamily_actAdj (pup := pup) hp0.le hp1 hpac0.le hpac1 v
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  have hcard := lazyFinalAux_card_ne v
  set r := p * pac with hr
  have hr0 : 0 < r := mul_pos hp0 hpac0
  have hr1 : r ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hp1 hpac0.le
    linarith
  set s := (Finset.univ : Finset {u : Fin n // u ≠ v}) with hs
  have hset : {x : SimpleGraph (Fin n) × DayCoins n |
        (nbrCount x.1 (actSet x.2) v : ℝ) ≤ α * r * n} =
      {x | ∑ u ∈ s, (if x.1.Adj v u.1 then (1 : ℝ) else 0) * (if x.2.1 u.1 then 1 else 0) ≤
        (α * r * n / (n - 1)) * (s.card : ℝ)} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [← lazyFinalAux_nbrCount_eq_sum, hcard, div_mul_cancel₀ _ hn1.ne']
  rw [hset]
  rcases lt_or_eq_of_le hr1 with hr1 | hr1
  · -- `r < 1`: Chernoff's bound in relative-entropy form, at `β r` with `β = α n / (n − 1)`
    set β := α * n / (n - 1) with hβ
    have hβ0 : 0 < β := by positivity
    have hαβ : α ≤ β := by
      rw [hβ, le_div_iff₀ hn1]
      nlinarith
    have hβ1 : β ≤ 1 := by
      rw [hβ, div_le_one hn1]
      nlinarith
    have ha : α * r * n / (n - 1) = β * r := by
      rw [hβ]
      ring
    rw [ha]
    refine le_trans (hY.measureReal_sum_le_le_exp_klBern hr0 hr1 s (by positivity)
      (by nlinarith)) ?_
    rw [hcard]
    apply Real.exp_le_exp.mpr
    have hkl := lazyFinalAux_klBern_ge hr0 hr1 hβ0 hβ1
    have e1 : (n - 1) * β = α * n := by
      rw [hβ]
      field_simp
    have hlog : Real.log α ≤ Real.log β := Real.log_le_log hα0 hαβ
    have hmain : r * n * (1 - α + α * Real.log α) - r ≤ (n - 1) * klBern (β * r) r := by
      calc r * n * (1 - α + α * Real.log α) - r =
            r * ((n - 1) - α * n + α * n * Real.log α) := by ring
        _ ≤ r * ((n - 1) - α * n + α * n * Real.log β) := by
            have : α * n * Real.log α ≤ α * n * Real.log β :=
              mul_le_mul_of_nonneg_left hlog (by positivity)
            nlinarith
        _ = (n - 1) * (r * (1 - β + β * Real.log β)) := by
            rw [← e1]
            ring
        _ ≤ (n - 1) * klBern (β * r) r := mul_le_mul_of_nonneg_left hkl hn1.le
    linarith
  · -- `r = 1`: every vertex has `n − 1` active neighbours almost surely
    rw [hr1] at hY
    rw [lazyFinalAux_measureReal_sum_le_of_one hY s ?_]
    · exact (Real.exp_pos _).le
    · rw [hcard, div_mul_cancel₀ _ hn1.ne', hr1]
      nlinarith

/-- The repaired degree step of Proposition 4.4, for one day (Lemma A.4's argument applied to the
active neighbours): under `G(n, p) ⊗ dayLaw`, some vertex has at most `α_λ p p_ac n` active
neighbours with probability at most `n^(−λ/2)`. -/
private lemma lazyFinalAux_day {n : ℕ} {lam p pac pup : ℝ} (hlam : 0 < lam) (hp0 : 0 < p)
    (hp1 : p ≤ 1) (hpac0 : 0 < pac) (hpac1 : pac ≤ 1) (hn : 4 / lam + 4 ≤ n)
    (hpn : (1 + lam) * Real.log n ≤ p * pac * n) :
    ((SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod (dayLaw n pac pup)).real
      {x | ∃ v, (nbrCount x.1 (actSet x.2) v : ℝ) ≤ alphaDeg lam * (p * pac) * n} ≤
      (n : ℝ) ^ (-(lam / 2)) := by
  have hn2 : 2 ≤ n := by
    have : (0 : ℝ) < 4 / lam := by positivity
    have : (2 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hα0 : 0 < alphaDeg lam := Real.exp_pos _
  have hα := lazyFinalAux_alpha_lt hlam
  have hU : {x : SimpleGraph (Fin n) × DayCoins n |
        ∃ v, (nbrCount x.1 (actSet x.2) v : ℝ) ≤ alphaDeg lam * (p * pac) * n} =
      ⋃ v, {x | (nbrCount x.1 (actSet x.2) v : ℝ) ≤ alphaDeg lam * (p * pac) * n} := by
    ext x
    simp
  rw [hU]
  refine le_trans (measureReal_iUnion_fintype_le _) ?_
  refine le_trans (Finset.sum_le_sum fun v _ =>
    lazyFinalAux_vertex hp0 hp1 hpac0 hpac1 hα0 hα hn2 v) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact lazyFinalAux_A4_numeric hlam hn hpn

/-- `K (log n + 1)² ≤ n^b` for large `n`. -/
private lemma lazyFinalAux_eventually_polylog (K : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ n : ℕ in Filter.atTop, K * (Real.log n + 1) ^ 2 ≤ (n : ℝ) ^ b := by
  have hpow := (tendsto_rpow_atTop (by positivity : 0 < b / 2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hpow.eventually_ge_atTop (|K| * (4 / b + 1) ^ 2 + 1),
    Filter.eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by linarith
  simp only [Function.comp_apply] at hn
  have hlog := Real.log_le_rpow_div hnpos.le (by positivity : 0 < b / 4)
  have h1 : 1 ≤ (n : ℝ) ^ (b / 4) := Real.one_le_rpow hn1' (by positivity)
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg hn1'
  have h2 : Real.log n + 1 ≤ (4 / b + 1) * (n : ℝ) ^ (b / 4) := by
    have : (n : ℝ) ^ (b / 4) / (b / 4) = 4 / b * (n : ℝ) ^ (b / 4) := by
      field_simp
    nlinarith
  have h3 : (Real.log n + 1) ^ 2 ≤ (4 / b + 1) ^ 2 * (n : ℝ) ^ (b / 2) := by
    have e : (n : ℝ) ^ (b / 2) = ((n : ℝ) ^ (b / 4)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      ring_nf
    rw [e, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 2
  have h4 : (n : ℝ) ^ b = (n : ℝ) ^ (b / 2) * (n : ℝ) ^ (b / 2) := by
    rw [← Real.rpow_add hnpos]
    ring_nf
  have h5 : 0 ≤ (n : ℝ) ^ (b / 2) := by positivity
  calc K * (Real.log n + 1) ^ 2 ≤ |K| * (Real.log n + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    _ ≤ |K| * ((4 / b + 1) ^ 2 * (n : ℝ) ^ (b / 2)) :=
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
  calc x * ((n : ℝ) ^ (-a) * (n : ℝ) ^ (-a)) ≤ (n : ℝ) ^ a * ((n : ℝ) ^ (-a) * (n : ℝ) ^ (-a)) :=
        mul_le_mul_of_nonneg_right hx (mul_nonneg h0 h0)
    _ = (n : ℝ) ^ (-a) := by rw [← mul_assoc, e2, one_mul]

/-- Steps 1 and 3 of the proof of Proposition 4.4, deterministically: if some day
`t₀ ≤ x ≤ T₁` has `|B_{t₀}| ≤ b / 2` and Blue is not empty on day `T₁ + T₂`, then either some vertex
has at most `b` active neighbours on some day before `T₁ + T₂`, or some vertex of `B_{t₀}` does not
update on any of the days `t₀, …, T₁ + T₂ − 1` (`lazyFinalAux_mem_of_degree`). -/
private lemma lazyFinalAux_contain {n : ℕ} (G : SimpleGraph (Fin n)) (c : ℕ → DayCoins n)
    (B₀ : Set (Fin n)) {x b : ℝ} (T₁ T₂ : ℕ) (hx : x ≤ T₁)
    (h : (∃ t₀ : ℕ, (t₀ : ℝ) ≤ x ∧ ((lazyBlueAfter G c B₀ t₀).ncard : ℝ) ≤ b / 2) ∧
      lazyBlueAfter G c B₀ (T₁ + T₂) ≠ ∅) :
    (∃ t ∈ Finset.range (T₁ + T₂), ∃ v, (nbrCount G (actSet (c t)) v : ℝ) ≤ b) ∨
    (∃ t₀ ∈ Finset.range (T₁ + 1), ((lazyBlueAfter G c B₀ t₀).ncard : ℝ) ≤ b / 2 ∧
      ∃ v ∈ lazyBlueAfter G c B₀ t₀, ∀ s, t₀ ≤ s → s < t₀ + (T₁ + T₂ - t₀) →
        ¬ ((c s).1 v = true ∧ (c s).2 v = true)) := by
  obtain ⟨⟨t₀, ht₀, hB⟩, hne⟩ := h
  by_cases hdeg : ∃ t ∈ Finset.range (T₁ + T₂), ∃ v, (nbrCount G (actSet (c t)) v : ℝ) ≤ b
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
      (fun s _ hs2 u => hdeg s (Finset.mem_range.mpr (by omega)) u) v hv
    exact ⟨v, this.1, this.2⟩

/-- Step 3 of the proof of Proposition 4.4 (repaired), over `T` days: by the union bound and
`lazyFinalAux_day`, some vertex has at most `b ≤ α_λ p p_ac n` active neighbours on some day
before `T` with probability at most `T n^(−λ/2)`. The event of one day depends on the graph and
that day's coins only (`lazyProb_eq_of_day`). -/
private lemma lazyFinalAux_degree_event {n : ℕ} {lam p pac pup b : ℝ} (hlam : 0 < lam)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hpac0 : 0 < pac) (hpac1 : pac ≤ 1) (hn : 4 / lam + 4 ≤ n)
    (hpn : (1 + lam) * Real.log n ≤ p * pac * n) (hb : b ≤ alphaDeg lam * (p * pac) * n)
    (T : ℕ) :
    lazyProb n p pac pup (fun G c => ∃ t ∈ Finset.range T, ∃ v,
      (nbrCount G (actSet (c t)) v : ℝ) ≤ b) ≤ (T : ℝ) * (n : ℝ) ^ (-(lam / 2)) := by
  refine le_trans (lazyProb_exists_le _ _) ?_
  have hday : ∀ t ∈ Finset.range T, lazyProb n p pac pup (fun G c => ∃ v,
      (nbrCount G (actSet (c t)) v : ℝ) ≤ b) ≤ (n : ℝ) ^ (-(lam / 2)) := by
    intro t _
    rw [lazyProb_eq_of_day t (fun G d => ∃ v, (nbrCount G (actSet d) v : ℝ) ≤ b)]
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
      (lazyFinalAux_day (pup := pup) hlam hp0 hp1 hpac0 hpac1 hn hpn)
    rintro x ⟨v, hv⟩
    exact ⟨v, le_trans hv hb⟩
  refine le_trans (Finset.sum_le_sum hday) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

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

/-- The end of the proof of Proposition 4.4: the numbers of days are `O(log n)`, so for large `n`
(`(A₁/q + 3)(log n + 1)² ≤ n^(λ/4)` and `≤ n^(q/2)`) the two bounds are at most `n^(−λ/4)` and
`n^(−q/2)`. -/
private lemma lazyFinalAux_count_le {n : ℕ} {lam q A₁ α : ℝ} (hn : (0 : ℝ) < n)
    (hL0 : 0 ≤ Real.log n) (hq0 : 0 < q) (hA₁ : 0 < A₁) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hpolyl : (A₁ / q + 3) * (Real.log n + 1) ^ 2 ≤ (n : ℝ) ^ (lam / 4))
    (hpolyq : (A₁ / q + 3) * (Real.log n + 1) ^ 2 ≤ (n : ℝ) ^ (q / 2)) :
    ((⌈A₁ * Real.log n / q⌉₊ + ⌈1 * Real.log n⌉₊ : ℕ) : ℝ) * (n : ℝ) ^ (-(lam / 2)) +
      ((⌈A₁ * Real.log n / q⌉₊ + 1 : ℕ) : ℝ) * (α * Real.log n / 2 * (n : ℝ) ^ (-q)) ≤
      1 * (n : ℝ) ^ (-(lam / 4)) + 1 * (n : ℝ) ^ (-(q / 2)) := by
  set L := Real.log n with hL
  have hT₁' : (⌈A₁ * L / q⌉₊ : ℝ) < A₁ * L / q + 1 := Nat.ceil_lt_add_one (by positivity)
  have hT₂' : (⌈1 * L⌉₊ : ℝ) < 1 * L + 1 := Nat.ceil_lt_add_one (by positivity)
  have hAq : A₁ * L / q = A₁ / q * L := by ring
  have hAq0 : 0 ≤ A₁ / q := by positivity
  have hsq : L ≤ (L + 1) ^ 2 := by nlinarith
  have hsq1 : 1 ≤ (L + 1) ^ 2 := by nlinarith
  have hsq2 : L * L / 2 ≤ (L + 1) ^ 2 := by nlinarith
  have h1 : ((⌈A₁ * L / q⌉₊ + ⌈1 * L⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) ^ (lam / 4) := by
    push_cast
    have := mul_le_mul_of_nonneg_left hsq hAq0
    linarith
  have h2 : ((⌈A₁ * L / q⌉₊ + 1 : ℕ) : ℝ) * (α * L / 2) ≤ (n : ℝ) ^ (q / 2) := by
    push_cast
    have hαL : α * L / 2 ≤ L / 2 := by
      have := mul_le_mul_of_nonneg_right hα1 hL0
      linarith
    have hT1 : (⌈A₁ * L / q⌉₊ : ℝ) + 1 ≤ A₁ / q * L + 2 := by linarith
    have hαL0 : 0 ≤ α * L / 2 := by positivity
    calc ((⌈A₁ * L / q⌉₊ : ℝ) + 1) * (α * L / 2) ≤ (A₁ / q * L + 2) * (L / 2) :=
          mul_le_mul hT1 hαL hαL0 (by positivity)
      _ ≤ (A₁ / q + 3) * (L + 1) ^ 2 := by
          have := mul_le_mul_of_nonneg_left hsq2 hAq0
          have e : (A₁ / q * L + 2) * (L / 2) = A₁ / q * (L * L / 2) + L := by ring
          rw [e]
          linarith
      _ ≤ _ := hpolyq
  have e1 : -(lam / 2) = -(2 * (lam / 4)) := by ring
  have e2 : -q = -(2 * (q / 2)) := by ring
  rw [e1, e2, ← mul_assoc]
  have k1 := lazyFinalAux_mul_rpow_le hn h1
  have k2 := lazyFinalAux_mul_rpow_le hn h2
  linarith

/-- **Proposition 4.4** (`S:prop:lazy-final`; unlabelled in the paper). Under the assumptions of
Theorem 4.1 and `|B_{t*₁}| ≤ α_λ (log n)/2`, where `t*₁ = O(p_up⁻¹ p_ac⁻¹ log n)` comes from
Proposition 4.3, there is `t*₂ = t*₁ + O(log n)` such that Red wins after day `t*₂` with
probability at least `1 − O(n^(−λ/4)) − O(n^(−p_up p_ac / 2))`.

Reading: for every `A₁`, the probability that some day `t₀ ≤ A₁ log n / (p_up p_ac)` has
`|B_{t₀}| ≤ α_λ (log n)/2` while Blue is not empty on day
`⌈A₁ log n / (p_up p_ac)⌉ + ⌈A log n⌉` is at most `C n^(−λ/4) + C n^(−p_up p_ac / 2)`.

The proof (with `A = C = 1`) is the paper's. (1) If every vertex has more than `α_λ log n`
active neighbours on each day of `[t₀, T)` and `|B_{t₀}| ≤ α_λ (log n)/2`, an updating vertex sees
fewer active Blue than active Red neighbours and turns Red, so a vertex that is Blue on day `T` is
in `B_{t₀}` and did not update on these days (`lazyFinalAux_mem_of_degree`). (2) Given the graph
and the days before `t₀`, one of the at most `α_λ (log n)/2` vertices of `B_{t₀}` does not update
on `k ≥ ⌈log n⌉` days with probability at most `(α_λ (log n)/2) (1 − p_up p_ac)^k ≤
(α_λ (log n)/2) n^(−p_up p_ac)` (`lazyFinalAux_never_update`); a union bound over
`t₀ ≤ A₁ log n / (p_up p_ac)` gives `O(n^(−p_up p_ac / 2))`. (3) The degree condition of (1) fails
on one of the `O(log n)` days with probability `O(log n) n^(−λ/2) ≤ n^(−λ/4)` for large `n`.

Departure from the paper (step (3)): the paper applies Lemma A.4 to the subgraph `G[A_t]` induced
on the active vertices, a `G(|A_t|, p)`, and claims minimum degree at least `α_λ p p_ac n` with
probability `1 − (p_ac n)^(−λ/2)`. Lemma A.4 does not apply as claimed: it needs
`p |A_t| ≥ (1 + ε) log |A_t|`, and when `p_ac n` is of order `log n` (allowed: `p = 1`,
`p_ac n = (1 + λ) log n`) `|A_t|` falls below `(1 − η) p_ac n` with probability only
`n^(−O(η²))`, not `O(n^(−λ/4))`; and Lemma A.4 with `ε < λ` gives `α_ε < α_λ`, too small for
step (1). The proof runs Lemma A.4's own argument on the active neighbours instead: the number of
active neighbours `∑_{u ≠ v} 1[u ∼ v] 1[u ∈ A_t]` of a vertex is `Bin(n − 1, p p_ac)` under
`G(n, p) ⊗ dayLaw` (`lazyFinalAux_isBernoulliFamily_actAdj`), and Chernoff's bound in
relative-entropy form with the computation of Lemma A.4's proof (`D(αq ‖ q) ≥ q (1 − α + α log α)`
and `α_λ (1 − log α_λ) < λ / (4 (1 + λ))`) shows that some vertex has at most `α_λ p p_ac n`
active neighbours on a given day with probability at most `n^(−λ/2)` once `n ≥ 4/λ + 4`
(`lazyFinalAux_day`). Lemma A.4 (`lemmaA_4`) itself is not used. -/
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
  have hq0 : 0 < pup * pac := mul_pos hpup0 hpac0
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    ((lazyFinalAux_eventually_polylog (A₁ / (pup * pac) + 3) (by positivity : 0 < lam / 4)).and
      (lazyFinalAux_eventually_polylog (A₁ / (pup * pac) + 3)
        (by positivity : 0 < pup * pac / 2)))
  refine ⟨max N₁ ⌈4 / lam + 4⌉₊, ?_⟩
  intro n hn p B₀ hp0 hp1 hpn
  obtain ⟨hpolyl, hpolyq⟩ := hN₁ n (le_trans (le_max_left _ _) hn)
  have hn4 : 4 / lam + 4 ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hn)
  have hn1 : (1 : ℝ) ≤ n := by
    have : (0 : ℝ) < 4 / lam := by positivity
    linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hα0 : 0 < alphaDeg lam := Real.exp_pos _
  have hα1 : alphaDeg lam ≤ 1 := le_trans (lazyFinalAux_alpha_lt hlam).le (by norm_num)
  -- `α_λ log n ≤ α_λ p p_ac n`
  have hb : alphaDeg lam * Real.log n ≤ alphaDeg lam * (p * pac) * n := by
    have h1 : Real.log n ≤ (1 + lam) * Real.log n := by
      have := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ 1 + lam) hL0
      linarith
    have := mul_le_mul_of_nonneg_left (le_trans h1 hpn) hα0.le
    linarith
  have hT₂ : Real.log n ≤ (⌈1 * Real.log n⌉₊ : ℝ) := by
    have := Nat.le_ceil (1 * Real.log n)
    linarith
  exact le_trans (lazyProb_mono fun G c h =>
      lazyFinalAux_contain G c B₀ _ _ (Nat.le_ceil _) h)
    (le_trans (lazyProb_or_le _ _)
      (le_trans (add_le_add
        (lazyFinalAux_degree_event hlam hp0 hp1 hpac0 hpac1 hn4 hpn hb _)
        (lazyFinalAux_update_event hpac0.le hpac1 hpup0.le hpup1 (by positivity) hnpos B₀ _ _
          hT₂))
        (lazyFinalAux_count_le hnpos hL0 hq0 hA₁ hα0.le hα1 hpolyl hpolyq)))

end PowerOfFew.Sparse

end
