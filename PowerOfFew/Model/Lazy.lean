module

public import PowerOfFew.Model.Gnp
public import PowerOfFew.Model.Majority

/-!
# Majority dynamics with random activations and updates: the model

Tools for Section 4 of the sparse paper (Definition 1.6: `lazyStep`, `lazyBlueAfter`,
`lazyLaw`, `lazyProb` in `PowerOfFew/Defs.lean`).

* One day: `lazyStep_eq` splits the next day's Blue set into the current Blue vertices that do not
  update and the updating vertices that are Blue in the hypothetical step `hypoStep`, in which
  every vertex observes the active vertices (the sparse paper's equation
  (main-lazy-details-temp0)). For an active vertex, the hypothetical step is majority dynamics on
  the subgraph induced by the active vertices (`enumSet_mem_hypoStep_iff`). The dynamics is
  monotone in the Blue set, and `∅` is absorbing.
* Induced subgraphs: the subgraph of `G(n, p)` induced on `m` vertices is `G(m, p)`
  (`binomialRandom_map_comap`, `gnpProb_comap`, `gnpProb_inducedOn`).
* The law: the coins of a day are independent of the graph and of the coins of the other days
  (`lazyProb_and_day`, `lazyProb_le_of_forall_day`, `lazyProb_eq_of_day`), and the coins of one
  day are independent Bernoulli variables (`isBernoulliFamily_act`, `isBernoulliFamily_upd`,
  `isBernoulliFamily_actUpd`), the update coins independent of the activation coins
  (`dayLaw_real_le_of_forall_act`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew

variable {n : ℕ}

/-! ### One day -/

/-- The active vertices of a day. -/
abbrev actSet (d : DayCoins n) : Set (Fin n) := {v | d.1 v = true}

/-- The vertices whose update coin is `true` on a day (they update if they are active). -/
abbrev updSet (d : DayCoins n) : Set (Fin n) := {v | d.2 v = true}

/-- The hypothetical Blue set of the next day if every vertex updated, observing the vertices of
`A` only: the paper's `hypo B` (written `B̃`) for the subgraph induced by the active vertices
`A`. -/
def hypoStep (G : SimpleGraph (Fin n)) (A B : Set (Fin n)) : Set (Fin n) :=
  {v | nbrCount G (A ∩ Bᶜ) v < nbrCount G (A ∩ B) v ∨
    (nbrCount G (A ∩ Bᶜ) v = nbrCount G (A ∩ B) v ∧ v ∈ B)}

/-- Equation (main-lazy-details-temp0) of the sparse paper: the next day's Blue set consists of
the current Blue vertices that do not update and of the updating vertices that are Blue in the
hypothetical step. -/
theorem lazyStep_eq (G : SimpleGraph (Fin n)) (A U B : Set (Fin n)) :
    lazyStep G A U B = (B \ (A ∩ U)) ∪ (A ∩ U ∩ hypoStep G A B) := by
  sorry

theorem hypoStep_mono (G : SimpleGraph (Fin n)) (A : Set (Fin n)) {B B' : Set (Fin n)}
    (h : B ⊆ B') : hypoStep G A B ⊆ hypoStep G A B' := by
  sorry

theorem lazyStep_mono (G : SimpleGraph (Fin n)) (A U : Set (Fin n)) {B B' : Set (Fin n)}
    (h : B ⊆ B') : lazyStep G A U B ⊆ lazyStep G A U B' := by
  sorry

@[simp] theorem lazyStep_empty (G : SimpleGraph (Fin n)) (A U : Set (Fin n)) :
    lazyStep G A U ∅ = ∅ := by
  sorry

theorem lazyBlueAfter_zero (G : SimpleGraph (Fin n)) (c : ℕ → DayCoins n) (B₀ : Set (Fin n)) :
    lazyBlueAfter G c B₀ 0 = B₀ := rfl

theorem lazyBlueAfter_succ (G : SimpleGraph (Fin n)) (c : ℕ → DayCoins n) (B₀ : Set (Fin n))
    (t : ℕ) :
    lazyBlueAfter G c B₀ (t + 1) =
      lazyStep G (actSet (c t)) (updSet (c t)) (lazyBlueAfter G c B₀ t) := rfl

/-- Running `s` days and then `t` more days, with the coins shifted by `s`. -/
theorem lazyBlueAfter_add (G : SimpleGraph (Fin n)) (c : ℕ → DayCoins n) (B₀ : Set (Fin n))
    (s t : ℕ) :
    lazyBlueAfter G c B₀ (s + t) =
      lazyBlueAfter G (fun i => c (s + i)) (lazyBlueAfter G c B₀ s) t := by
  sorry

/-- The dynamics is monotone in the initial Blue set. -/
theorem lazyBlueAfter_mono (G : SimpleGraph (Fin n)) (c : ℕ → DayCoins n) {B₀ B₀' : Set (Fin n)}
    (h : B₀ ⊆ B₀') (t : ℕ) : lazyBlueAfter G c B₀ t ⊆ lazyBlueAfter G c B₀' t := by
  sorry

/-- Once Blue is empty, it stays empty. -/
theorem lazyBlueAfter_eq_empty_of_le (G : SimpleGraph (Fin n)) (c : ℕ → DayCoins n)
    (B₀ : Set (Fin n)) {s t : ℕ} (hs : lazyBlueAfter G c B₀ s = ∅) (hst : s ≤ t) :
    lazyBlueAfter G c B₀ t = ∅ := by
  sorry

/-- The Blue set after `t` days depends only on the coins of the first `t` days. -/
theorem lazyBlueAfter_congr (G : SimpleGraph (Fin n)) {c c' : ℕ → DayCoins n}
    (B₀ : Set (Fin n)) {t : ℕ} (h : ∀ i < t, c i = c' i) :
    lazyBlueAfter G c B₀ t = lazyBlueAfter G c' B₀ t := by
  sorry

/-! ### Induced subgraphs -/

/-- The increasing enumeration `Fin |A| ↪ Fin n` of a set of vertices `A`. -/
def enumSet (A : Set (Fin n)) : Fin A.ncard ↪ Fin n :=
  ((Set.toFinite A).toFinset.orderEmbOfFin (Set.ncard_eq_toFinset_card A).symm).toEmbedding

theorem range_enumSet (A : Set (Fin n)) : Set.range (enumSet A) = A := by
  sorry

/-- The subgraph of `G` induced on `A`, with its vertices numbered `0, …, |A| − 1` in increasing
order. -/
def inducedOn (G : SimpleGraph (Fin n)) (A : Set (Fin n)) : SimpleGraph (Fin A.ncard) :=
  G.comap (enumSet A)

theorem ncard_preimage_enumSet (A S : Set (Fin n)) :
    (enumSet A ⁻¹' S).ncard = (A ∩ S).ncard := by
  sorry

theorem nbrCount_inducedOn (G : SimpleGraph (Fin n)) (A S : Set (Fin n)) (i : Fin A.ncard) :
    nbrCount (inducedOn G A) (enumSet A ⁻¹' S) i = nbrCount G (A ∩ S) (enumSet A i) := by
  sorry

theorem degree_inducedOn (G : SimpleGraph (Fin n)) (A : Set (Fin n)) (i : Fin A.ncard) :
    degree (inducedOn G A) i = nbrCount G A (enumSet A i) := by
  sorry

/-- For an active vertex, the hypothetical step is majority dynamics on the subgraph induced by
the active vertices. -/
theorem enumSet_mem_hypoStep_iff (G : SimpleGraph (Fin n)) (A B : Set (Fin n))
    (i : Fin A.ncard) :
    enumSet A i ∈ hypoStep G A B ↔ i ∈ majorityStep (inducedOn G A) (enumSet A ⁻¹' B) := by
  sorry

/-- The active vertices that are Blue in the hypothetical step are, renumbered, the next day's
Blue set of majority dynamics on the active subgraph. -/
theorem inter_hypoStep_eq_image (G : SimpleGraph (Fin n)) (A B : Set (Fin n)) :
    A ∩ hypoStep G A B = enumSet A '' majorityStep (inducedOn G A) (enumSet A ⁻¹' B) := by
  sorry

theorem ncard_inter_hypoStep (G : SimpleGraph (Fin n)) (A B : Set (Fin n)) :
    (A ∩ hypoStep G A B).ncard = (majorityStep (inducedOn G A) (enumSet A ⁻¹' B)).ncard := by
  sorry

/-- **Induced subgraphs of `G(n, p)`.** The subgraph of `G(n, p)` induced on `m` distinct vertices
is `G(m, p)`. -/
theorem binomialRandom_map_comap {m : ℕ} (f : Fin m ↪ Fin n) (p : unitInterval) :
    (SimpleGraph.binomialRandom (Fin n) p).map (SimpleGraph.comap f) =
      SimpleGraph.binomialRandom (Fin m) p := by
  sorry

theorem gnpProb_comap {m : ℕ} (f : Fin m ↪ Fin n) (p : ℝ) (P : SimpleGraph (Fin m) → Prop) :
    gnpProb n p (fun G => P (G.comap f)) = gnpProb m p P := by
  sorry

theorem gnpProb_inducedOn (A : Set (Fin n)) (p : ℝ) (P : SimpleGraph (Fin A.ncard) → Prop) :
    gnpProb n p (fun G => P (inducedOn G A)) = gnpProb A.ncard p P := by
  sorry

/-! ### The law of the graph and the coins -/

instance (n : ℕ) (pac pup : ℝ) : IsProbabilityMeasure (dayLaw n pac pup) := by
  sorry

instance (n : ℕ) (p pac pup : ℝ) : IsProbabilityMeasure (lazyLaw n p pac pup) := by
  sorry

variable {p pac pup : ℝ}

theorem lazyProb_nonneg (P : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop) :
    0 ≤ lazyProb n p pac pup P := by
  sorry

theorem lazyProb_le_one (P : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop) :
    lazyProb n p pac pup P ≤ 1 := by
  sorry

theorem lazyProb_mono {P Q : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop}
    (h : ∀ G c, P G c → Q G c) : lazyProb n p pac pup P ≤ lazyProb n p pac pup Q := by
  sorry

theorem lazyProb_or_le (P Q : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop) :
    lazyProb n p pac pup (fun G c => P G c ∨ Q G c) ≤
      lazyProb n p pac pup P + lazyProb n p pac pup Q := by
  sorry

/-- The union bound. -/
theorem lazyProb_exists_le {ι : Type*} (s : Finset ι)
    (P : ι → SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop) :
    lazyProb n p pac pup (fun G c => ∃ i ∈ s, P i G c) ≤
      ∑ i ∈ s, lazyProb n p pac pup (P i) := by
  sorry

/-- An event has probability `1 - x` or more when its complement has probability at most `x`. -/
theorem le_lazyProb_of_not_le {P : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop} {x : ℝ}
    (h : lazyProb n p pac pup (fun G c => ¬ P G c) ≤ x) : 1 - x ≤ lazyProb n p pac pup P := by
  sorry

/-- An event about the graph only has its probability under `G(n, p)`. -/
theorem lazyProb_graph (P : SimpleGraph (Fin n) → Prop) :
    lazyProb n p pac pup (fun G _ => P G) = gnpProb n p P := by
  sorry

/-- At `p = 1` the graph is complete. -/
theorem lazyProb_one (P : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop) :
    lazyProb n 1 pac pup P = lazyProb n 1 pac pup (fun _ c => P ⊤ c) := by
  sorry

/-- The coins of day `t` are independent of the graph and of the coins of the earlier days. -/
theorem lazyProb_and_day (t : ℕ) (P : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop)
    (hP : ∀ G c c', (∀ i < t, c i = c' i) → (P G c ↔ P G c')) (Q : DayCoins n → Prop) :
    lazyProb n p pac pup (fun G c => P G c ∧ Q (c t)) =
      lazyProb n p pac pup P * (dayLaw n pac pup).real {d | Q d} := by
  sorry

/-- Conditioning on the graph and on the coins of the other days: if an event depends on the
coins of the days up to `t` only and, whatever the graph and the coins of the other days, the coins
of day `t` make it happen with probability at most `ε`, then its probability is at most `ε`. -/
theorem lazyProb_le_of_forall_day {ε : ℝ} (t : ℕ)
    (P : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop)
    (hP : ∀ G c c', (∀ i ≤ t, c i = c' i) → (P G c ↔ P G c'))
    (h : ∀ G c, (dayLaw n pac pup).real {d | P G (Function.update c t d)} ≤ ε) :
    lazyProb n p pac pup P ≤ ε := by
  sorry

/-- Conditioning on the graph and on the coins of the days before `t`: the coins of the `k` days
`t, …, t + k − 1` are independent of them, with law `dayLaw^k`. If an event depends on the coins
of the days before `t + k` only and, whatever the graph and the coins of the other days, the coins
of those `k` days make it happen with probability at most `ε`, then its probability is at most
`ε`. -/
theorem lazyProb_le_of_forall_days {ε : ℝ} (t k : ℕ)
    (P : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop)
    (hP : ∀ G c c', (∀ i < t + k, c i = c' i) → (P G c ↔ P G c'))
    (h : ∀ (G : SimpleGraph (Fin n)) (c : ℕ → DayCoins n),
      (Measure.pi fun _ : Fin k => dayLaw n pac pup).real
      {w : Fin k → DayCoins n |
        P G (fun i => if hi : t ≤ i ∧ i < t + k then w ⟨i - t, by omega⟩ else c i)} ≤ ε) :
    lazyProb n p pac pup P ≤ ε := by
  sorry

/-- An event about the graph and the coins of day `t` only has its probability under the product
of `G(n, p)` and the law of one day's coins. -/
theorem lazyProb_eq_of_day (t : ℕ) (Q : SimpleGraph (Fin n) → DayCoins n → Prop) :
    lazyProb n p pac pup (fun G c => Q G (c t)) =
      ((SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod (dayLaw n pac pup)).real
        {x | Q x.1 x.2} := by
  sorry

/-- The product of `G(n, p)` and the law of one day's coins, as an average over the coins. -/
theorem prod_dayLaw_real_eq_sum (Q : SimpleGraph (Fin n) → DayCoins n → Prop) :
    ((SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod (dayLaw n pac pup)).real
        {x | Q x.1 x.2} =
      ∑ d : DayCoins n, (dayLaw n pac pup).real {d} * gnpProb n p (fun G => Q G d) := by
  sorry

theorem dayLaw_real_singleton (hpac0 : 0 ≤ pac) (hpac1 : pac ≤ 1) (hpup0 : 0 ≤ pup)
    (hpup1 : pup ≤ 1) (d : DayCoins n) :
    (dayLaw n pac pup).real {d} =
      (∏ v, if d.1 v then pac else 1 - pac) * ∏ v, if d.2 v then pup else 1 - pup := by
  sorry

/-- The update coins of a day are independent of its activation coins. -/
theorem dayLaw_real_le_of_forall_act {ε : ℝ} (Q : (Fin n → Bool) → (Fin n → Bool) → Prop)
    (h : ∀ a, (Measure.pi fun _ : Fin n => bernoulliMeasure true false (toUnit pup)).real
      {u | Q a u} ≤ ε) :
    (dayLaw n pac pup).real {d | Q d.1 d.2} ≤ ε := by
  sorry

/-- Independent coins, each `true` with probability `q`, as a Bernoulli family. -/
theorem isBernoulliFamily_coins {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsBernoulliFamily (Measure.pi fun _ : Fin n => bernoulliMeasure true false (toUnit q)) q
      (fun v ω => if ω v then 1 else 0) := by
  sorry

/-- The activation indicators of a day are independent Bernoulli(`p_ac`) variables. -/
theorem isBernoulliFamily_act (hpac0 : 0 ≤ pac) (hpac1 : pac ≤ 1) :
    IsBernoulliFamily (dayLaw n pac pup) pac (fun v d => if d.1 v then 1 else 0) := by
  sorry

/-- The update coins of a day are independent Bernoulli(`p_up`) variables. -/
theorem isBernoulliFamily_upd (hpup0 : 0 ≤ pup) (hpup1 : pup ≤ 1) :
    IsBernoulliFamily (dayLaw n pac pup) pup (fun v d => if d.2 v then 1 else 0) := by
  sorry

/-- The indicators that a vertex updates on a day are independent Bernoulli(`p_ac p_up`)
variables. -/
theorem isBernoulliFamily_actUpd (hpac0 : 0 ≤ pac) (hpac1 : pac ≤ 1) (hpup0 : 0 ≤ pup)
    (hpup1 : pup ≤ 1) :
    IsBernoulliFamily (dayLaw n pac pup) (pac * pup)
      (fun v d => if d.1 v = true ∧ d.2 v = true then 1 else 0) := by
  sorry

open Classical in
/-- The number of vertices of `S` whose coin is `true`, as a sum of indicators. -/
theorem ncard_inter_setOf_eq_sum (S : Set (Fin n)) (ω : Fin n → Bool) :
    ((S ∩ {v | ω v = true}).ncard : ℝ) = ∑ v ∈ S.toFinset, (if ω v then 1 else 0 : ℝ) := by
  sorry

end PowerOfFew

end
