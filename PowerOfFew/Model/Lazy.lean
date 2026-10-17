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

The statements about the law rest on one fact (the private lemma `lazyAux_measurePreserving`):
the map sending the graph and the coins to the graph, the coins of the days `0, …, t - 1` and the
coins of the days `t, …, t + k - 1` sends `lazyLaw` to the product `G(n, p) ⊗ dayLaw^t ⊗ dayLaw^k`.
Every event that depends on finitely many days is then an event of this finite (hence discrete)
product space, where Fubini's theorem applies.
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
  ext v
  simp only [lazyStep, hypoStep, Set.mem_ofPred_eq, Set.mem_union, Set.mem_sdiff,
    Set.mem_inter_iff]
  tauto

/-- `nbrCount G S v` is monotone in `S`. -/
private lemma lazyAux_nbrCount_mono (G : SimpleGraph (Fin n)) {S S' : Set (Fin n)} (h : S ⊆ S')
    (v : Fin n) : nbrCount G S v ≤ nbrCount G S' v := by
  unfold nbrCount
  exact Set.ncard_le_ncard fun _ hu => ⟨hu.1, h hu.2⟩

theorem hypoStep_mono (G : SimpleGraph (Fin n)) (A : Set (Fin n)) {B B' : Set (Fin n)}
    (h : B ⊆ B') : hypoStep G A B ⊆ hypoStep G A B' := by
  intro v hv
  have h1 : nbrCount G (A ∩ B) v ≤ nbrCount G (A ∩ B') v :=
    lazyAux_nbrCount_mono G (Set.inter_subset_inter_right A h) v
  have h2 : nbrCount G (A ∩ B'ᶜ) v ≤ nbrCount G (A ∩ Bᶜ) v :=
    lazyAux_nbrCount_mono G (Set.inter_subset_inter_right A (Set.compl_subset_compl.2 h)) v
  simp only [hypoStep, Set.mem_ofPred_eq] at hv ⊢
  rcases hv with hv | ⟨hv, hvB⟩
  · exact Or.inl (by omega)
  · rcases (h2.trans (hv.le.trans h1)).lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, h hvB⟩

theorem lazyStep_mono (G : SimpleGraph (Fin n)) (A U : Set (Fin n)) {B B' : Set (Fin n)}
    (h : B ⊆ B') : lazyStep G A U B ⊆ lazyStep G A U B' := by
  rw [lazyStep_eq, lazyStep_eq]
  exact Set.union_subset_union (Set.sdiff_subset_sdiff_left h)
    (Set.inter_subset_inter_right _ (hypoStep_mono G A h))

@[simp] theorem lazyStep_empty (G : SimpleGraph (Fin n)) (A U : Set (Fin n)) :
    lazyStep G A U ∅ = ∅ := by
  ext v
  simp [lazyStep, nbrCount]

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
  induction t with
  | zero => rfl
  | succ t ih =>
    show lazyBlueAfter G c B₀ (s + t + 1) = _
    rw [lazyBlueAfter_succ, ih]
    rfl

/-- The dynamics is monotone in the initial Blue set. -/
theorem lazyBlueAfter_mono (G : SimpleGraph (Fin n)) (c : ℕ → DayCoins n) {B₀ B₀' : Set (Fin n)}
    (h : B₀ ⊆ B₀') (t : ℕ) : lazyBlueAfter G c B₀ t ⊆ lazyBlueAfter G c B₀' t := by
  induction t with
  | zero => exact h
  | succ t ih =>
    rw [lazyBlueAfter_succ, lazyBlueAfter_succ]
    exact lazyStep_mono G _ _ ih

/-- Once Blue is empty, it stays empty. -/
theorem lazyBlueAfter_eq_empty_of_le (G : SimpleGraph (Fin n)) (c : ℕ → DayCoins n)
    (B₀ : Set (Fin n)) {s t : ℕ} (hs : lazyBlueAfter G c B₀ s = ∅) (hst : s ≤ t) :
    lazyBlueAfter G c B₀ t = ∅ := by
  induction t, hst using Nat.le_induction with
  | base => exact hs
  | succ t _ ih => rw [lazyBlueAfter_succ, ih, lazyStep_empty]

/-- The Blue set after `t` days depends only on the coins of the first `t` days. -/
theorem lazyBlueAfter_congr (G : SimpleGraph (Fin n)) {c c' : ℕ → DayCoins n}
    (B₀ : Set (Fin n)) {t : ℕ} (h : ∀ i < t, c i = c' i) :
    lazyBlueAfter G c B₀ t = lazyBlueAfter G c' B₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [lazyBlueAfter_succ, lazyBlueAfter_succ, ih fun i hi => h i (by omega), h t (by omega)]

/-! ### Induced subgraphs -/

/-- The increasing enumeration `Fin |A| ↪ Fin n` of a set of vertices `A`. -/
def enumSet (A : Set (Fin n)) : Fin A.ncard ↪ Fin n :=
  ((Set.toFinite A).toFinset.orderEmbOfFin (Set.ncard_eq_toFinset_card A).symm).toEmbedding

theorem range_enumSet (A : Set (Fin n)) : Set.range (enumSet A) = A := by
  rw [enumSet, RelEmbedding.coe_toEmbedding, Finset.range_orderEmbOfFin,
    Set.Finite.coe_toFinset]

/-- The subgraph of `G` induced on `A`, with its vertices numbered `0, …, |A| − 1` in increasing
order. -/
def inducedOn (G : SimpleGraph (Fin n)) (A : Set (Fin n)) : SimpleGraph (Fin A.ncard) :=
  G.comap (enumSet A)

theorem ncard_preimage_enumSet (A S : Set (Fin n)) :
    (enumSet A ⁻¹' S).ncard = (A ∩ S).ncard := by
  rw [← Set.ncard_image_of_injective _ (enumSet A).injective, Set.image_preimage_eq_inter_range,
    range_enumSet, Set.inter_comm]

theorem nbrCount_inducedOn (G : SimpleGraph (Fin n)) (A S : Set (Fin n)) (i : Fin A.ncard) :
    nbrCount (inducedOn G A) (enumSet A ⁻¹' S) i = nbrCount G (A ∩ S) (enumSet A i) := by
  have h : {j | (inducedOn G A).Adj i j ∧ j ∈ enumSet A ⁻¹' S} =
      enumSet A ⁻¹' {u | G.Adj (enumSet A i) u ∧ u ∈ S} := by
    ext j
    simp [inducedOn]
  have h2 : A ∩ {u | G.Adj (enumSet A i) u ∧ u ∈ S} =
      {u | G.Adj (enumSet A i) u ∧ u ∈ A ∩ S} := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  unfold nbrCount
  rw [h, ncard_preimage_enumSet, h2]

theorem degree_inducedOn (G : SimpleGraph (Fin n)) (A : Set (Fin n)) (i : Fin A.ncard) :
    degree (inducedOn G A) i = nbrCount G A (enumSet A i) := by
  have h : (inducedOn G A).neighborSet i = enumSet A ⁻¹' G.neighborSet (enumSet A i) := by
    ext j
    simp [inducedOn]
  have h2 : A ∩ G.neighborSet (enumSet A i) = {u | G.Adj (enumSet A i) u ∧ u ∈ A} := by
    ext u
    simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet, Set.mem_ofPred_eq]
    tauto
  unfold degree nbrCount
  rw [h, ncard_preimage_enumSet, h2]

/-- For an active vertex, the hypothetical step is majority dynamics on the subgraph induced by
the active vertices. -/
theorem enumSet_mem_hypoStep_iff (G : SimpleGraph (Fin n)) (A B : Set (Fin n))
    (i : Fin A.ncard) :
    enumSet A i ∈ hypoStep G A B ↔ i ∈ majorityStep (inducedOn G A) (enumSet A ⁻¹' B) := by
  have h1 := nbrCount_inducedOn G A B i
  have h2 := nbrCount_inducedOn G A Bᶜ i
  rw [Set.preimage_compl] at h2
  simp only [hypoStep, majorityStep, Set.mem_ofPred_eq, Set.mem_preimage, h1, h2]

/-- The active vertices that are Blue in the hypothetical step are, renumbered, the next day's
Blue set of majority dynamics on the active subgraph. -/
theorem inter_hypoStep_eq_image (G : SimpleGraph (Fin n)) (A B : Set (Fin n)) :
    A ∩ hypoStep G A B = enumSet A '' majorityStep (inducedOn G A) (enumSet A ⁻¹' B) := by
  ext v
  constructor
  · rintro ⟨hvA, hv⟩
    have hvA' : v ∈ Set.range (enumSet A) := by rw [range_enumSet]; exact hvA
    obtain ⟨i, rfl⟩ := hvA'
    exact ⟨i, (enumSet_mem_hypoStep_iff G A B i).1 hv, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨?_, (enumSet_mem_hypoStep_iff G A B i).2 hi⟩
    have h : enumSet A i ∈ Set.range (enumSet A) := ⟨i, rfl⟩
    rwa [range_enumSet] at h

theorem ncard_inter_hypoStep (G : SimpleGraph (Fin n)) (A B : Set (Fin n)) :
    (A ∩ hypoStep G A B).ncard = (majorityStep (inducedOn G A) (enumSet A ⁻¹' B)).ncard := by
  rw [inter_hypoStep_eq_image, Set.ncard_image_of_injective _ (enumSet A).injective]

/-- The induced subgraph of the graph of the edge variables `ω` is the graph of the edge variables
of the pairs of the image. -/
private lemma lazyAux_comap_graphOfEdges {m : ℕ} (f : Fin m ↪ Fin n) (ω : EdgeVars n) :
    (graphOfEdges ω).comap f = graphOfEdges (fun e => ω (Sym2.map f e)) := by
  ext i j
  simp only [SimpleGraph.comap_adj, adj_graphOfEdges, Sym2.map_mk, ne_eq,
    f.injective.eq_iff]

/-- The edge variables of the pairs of the image of an injective map are independent with the
same laws: the restriction of `edgeLaw n p` along `f` is `edgeLaw m p`. -/
private lemma lazyAux_edgeLaw_map {m : ℕ} (f : Fin m ↪ Fin n) (p : ℝ) :
    (edgeLaw n p).map (fun ω e => ω (Sym2.map f e)) = edgeLaw m p := by
  rw [edgeLaw, edgeLaw, ← Measure.infinitePi_eq_pi,
    Measure.map_infinitePi_infinitePi_of_inj (Sym2.map.injective f.injective),
    Measure.infinitePi_eq_pi]
  congr 1
  funext e
  simp only [Sym2.isDiag_map f.injective]

/-- **Induced subgraphs of `G(n, p)`.** The subgraph of `G(n, p)` induced on `m` distinct vertices
is `G(m, p)`. -/
theorem binomialRandom_map_comap {m : ℕ} (f : Fin m ↪ Fin n) (p : unitInterval) :
    (SimpleGraph.binomialRandom (Fin n) p).map (SimpleGraph.comap f) =
      SimpleGraph.binomialRandom (Fin m) p := by
  have hp : toUnit (p : ℝ) = p := Set.projIcc_val zero_le_one p
  have hcomap : Measurable (SimpleGraph.comap (V := Fin m) (W := Fin n) f) :=
    fun _ _ => measurableSet_simpleGraph _
  have hres : Measurable (fun (ω : EdgeVars n) (e : Sym2 (Fin m)) => ω (Sym2.map f e)) :=
    fun _ _ => measurableSet_edgeVars _
  rw [← hp, binomialRandom_eq_map_edgeLaw, binomialRandom_eq_map_edgeLaw,
    Measure.map_map hcomap measurable_graphOfEdges, ← lazyAux_edgeLaw_map f,
    Measure.map_map measurable_graphOfEdges hres]
  congr 1
  funext ω
  exact lazyAux_comap_graphOfEdges f ω

theorem gnpProb_comap {m : ℕ} (f : Fin m ↪ Fin n) (p : ℝ) (P : SimpleGraph (Fin m) → Prop) :
    gnpProb n p (fun G => P (G.comap f)) = gnpProb m p P := by
  unfold gnpProb
  rw [← binomialRandom_map_comap f (toUnit p),
    map_measureReal_apply (fun _ _ => measurableSet_simpleGraph _) (measurableSet_simpleGraph _)]
  rfl

theorem gnpProb_inducedOn (A : Set (Fin n)) (p : ℝ) (P : SimpleGraph (Fin A.ncard) → Prop) :
    gnpProb n p (fun G => P (inducedOn G A)) = gnpProb A.ncard p P :=
  gnpProb_comap (enumSet A) p P

/-! ### The law of the graph and the coins -/

instance (n : ℕ) (pac pup : ℝ) : IsProbabilityMeasure (dayLaw n pac pup) := by
  unfold dayLaw
  infer_instance

instance (n : ℕ) (p pac pup : ℝ) : IsProbabilityMeasure (lazyLaw n p pac pup) := by
  unfold lazyLaw
  infer_instance

/-- Singletons of graphs are measurable (every set of graphs on `Fin n` is). -/
private lemma lazyAux_msc : MeasurableSingletonClass (SimpleGraph (Fin n)) :=
  ⟨fun _ => measurableSet_simpleGraph _⟩

variable {p pac pup : ℝ}

theorem lazyProb_nonneg (P : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop) :
    0 ≤ lazyProb n p pac pup P :=
  measureReal_nonneg

theorem lazyProb_le_one (P : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop) :
    lazyProb n p pac pup P ≤ 1 :=
  measureReal_le_one

theorem lazyProb_mono {P Q : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop}
    (h : ∀ G c, P G c → Q G c) : lazyProb n p pac pup P ≤ lazyProb n p pac pup Q :=
  measureReal_mono fun x hx => h x.1 x.2 hx

theorem lazyProb_or_le (P Q : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop) :
    lazyProb n p pac pup (fun G c => P G c ∨ Q G c) ≤
      lazyProb n p pac pup P + lazyProb n p pac pup Q :=
  measureReal_union_le (μ := lazyLaw n p pac pup)
    {x : SimpleGraph (Fin n) × (ℕ → DayCoins n) | P x.1 x.2}
    {x : SimpleGraph (Fin n) × (ℕ → DayCoins n) | Q x.1 x.2}

/-- The union bound. -/
theorem lazyProb_exists_le {ι : Type*} (s : Finset ι)
    (P : ι → SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop) :
    lazyProb n p pac pup (fun G c => ∃ i ∈ s, P i G c) ≤
      ∑ i ∈ s, lazyProb n p pac pup (P i) := by
  unfold lazyProb
  have h : {x : SimpleGraph (Fin n) × (ℕ → DayCoins n) | ∃ i ∈ s, P i x.1 x.2} =
      ⋃ i ∈ s, {x | P i x.1 x.2} := by
    ext x
    simp
  rw [h]
  exact measureReal_biUnion_finset_le _ _

/-- An event has probability `1 - x` or more when its complement has probability at most `x`. -/
theorem le_lazyProb_of_not_le {P : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop} {x : ℝ}
    (h : lazyProb n p pac pup (fun G c => ¬ P G c) ≤ x) : 1 - x ≤ lazyProb n p pac pup P := by
  have h1 := measureReal_union_le (μ := lazyLaw n p pac pup) {y | P y.1 y.2} {y | P y.1 y.2}ᶜ
  rw [Set.union_compl_self, probReal_univ] at h1
  change (lazyLaw n p pac pup).real {y | P y.1 y.2}ᶜ ≤ x at h
  unfold lazyProb
  linarith

/-- An event about the graph only has its probability under `G(n, p)`. -/
theorem lazyProb_graph (P : SimpleGraph (Fin n) → Prop) :
    lazyProb n p pac pup (fun G _ => P G) = gnpProb n p P := by
  have h : {x : SimpleGraph (Fin n) × (ℕ → DayCoins n) | P x.1} = {G | P G} ×ˢ Set.univ := by
    ext x
    simp
  show (lazyLaw n p pac pup).real {x | P x.1} = _
  rw [h, lazyLaw, measureReal_prod_prod, probReal_univ, mul_one]
  rfl

/-- At `p = 1` the graph is complete. -/
theorem lazyProb_one (P : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop) :
    lazyProb n 1 pac pup P = lazyProb n 1 pac pup (fun _ c => P ⊤ c) := by
  have := lazyAux_msc (n := n)
  have h1 : toUnit 1 = 1 := Subtype.ext (toUnit_coe zero_le_one le_rfl)
  have hlaw : lazyLaw n 1 pac pup =
      (Measure.infinitePi fun _ : ℕ => dayLaw n pac pup).map (Prod.mk ⊤) := by
    rw [lazyLaw, h1, SimpleGraph.binomialRandom_one, Measure.dirac_prod]
  simp only [lazyProb, hlaw, measureReal_def, (measurableEmbedding_prodMk_left _).map_apply]
  rfl

/-- The coins of the days `0, …, t - 1` and of the days `t, …, t + k - 1`. -/
private def lazyAux_split (t k : ℕ) (c : ℕ → DayCoins n) :
    (Fin t → DayCoins n) × (Fin k → DayCoins n) :=
  (fun i => c i, fun j => c (t + j))

/-- The coins of the days `0, …, t - 1` and of the days `t, …, t + k - 1` are independent, with
laws `dayLaw^t` and `dayLaw^k`. -/
private lemma lazyAux_measurePreserving_split (pac pup : ℝ) (t k : ℕ) :
    MeasurePreserving (lazyAux_split (n := n) t k)
      (Measure.infinitePi fun _ : ℕ => dayLaw n pac pup)
      ((Measure.pi fun _ : Fin t => dayLaw n pac pup).prod
        (Measure.pi fun _ : Fin k => dayLaw n pac pup)) := by
  let g : Fin t ⊕ Fin k → ℕ := Sum.elim (fun i => (i : ℕ)) (fun j => t + (j : ℕ))
  have hg : Function.Injective g := by
    rintro (i | i) (j | j) h
    · simp only [g, Sum.elim_inl] at h
      exact congrArg Sum.inl (Fin.ext h)
    · simp only [g, Sum.elim_inl, Sum.elim_inr] at h
      have := i.isLt
      omega
    · simp only [g, Sum.elim_inl, Sum.elim_inr] at h
      have := j.isLt
      omega
    · simp only [g, Sum.elim_inr] at h
      exact congrArg Sum.inr (Fin.ext (by omega))
  have h1 : MeasurePreserving (fun (c : ℕ → DayCoins n) (a : Fin t ⊕ Fin k) => c (g a))
      (Measure.infinitePi fun _ : ℕ => dayLaw n pac pup)
      (Measure.pi fun _ : Fin t ⊕ Fin k => dayLaw n pac pup) := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.map_infinitePi_infinitePi_of_inj hg, Measure.infinitePi_eq_pi]
  exact (measurePreserving_sumPiEquivProdPi (fun _ : Fin t ⊕ Fin k => dayLaw n pac pup)).comp h1

/-- The graph, the coins of the days `0, …, t - 1` and the coins of the days `t, …, t + k - 1` are
independent, with laws `G(n, p)`, `dayLaw^t` and `dayLaw^k`. -/
private lemma lazyAux_measurePreserving (p pac pup : ℝ) (t k : ℕ) :
    MeasurePreserving
      (fun x : SimpleGraph (Fin n) × (ℕ → DayCoins n) =>
        ((x.1, fun i : Fin t => x.2 i), fun j : Fin k => x.2 (t + j)))
      (lazyLaw n p pac pup)
      (((SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod
          (Measure.pi fun _ : Fin t => dayLaw n pac pup)).prod
        (Measure.pi fun _ : Fin k => dayLaw n pac pup)) := by
  have h1 := (MeasurePreserving.id (SimpleGraph.binomialRandom (Fin n) (toUnit p))).prod
    (lazyAux_measurePreserving_split (n := n) pac pup t k)
  have h2 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (SimpleGraph.binomialRandom (Fin n) (toUnit p))
      (Measure.pi fun _ : Fin t => dayLaw n pac pup)
      (Measure.pi fun _ : Fin k => dayLaw n pac pup))
  exact h2.comp h1

/-- The graph, the coins of the days `0, …, t - 1` and the coins of day `t` are independent, with
laws `G(n, p)`, `dayLaw^t` and `dayLaw`. -/
private lemma lazyAux_measurePreserving_day (p pac pup : ℝ) (t : ℕ) :
    MeasurePreserving
      (fun x : SimpleGraph (Fin n) × (ℕ → DayCoins n) => ((x.1, fun i : Fin t => x.2 i), x.2 t))
      (lazyLaw n p pac pup)
      (((SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod
          (Measure.pi fun _ : Fin t => dayLaw n pac pup)).prod (dayLaw n pac pup)) := by
  have h := ((MeasurePreserving.id ((SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod
    (Measure.pi fun _ : Fin t => dayLaw n pac pup))).prod
    (measurePreserving_funUnique (dayLaw n pac pup) (Fin 1))).comp
    (lazyAux_measurePreserving (n := n) p pac pup t 1)
  exact h

/-- An event that depends on the graph and on the coins of the days before `t + k` has its
probability under `G(n, p) ⊗ dayLaw^t ⊗ dayLaw^k`. -/
private lemma lazyAux_lazyProb_eq (t k : ℕ) (P : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop)
    (F : (SimpleGraph (Fin n) × (Fin t → DayCoins n)) × (Fin k → DayCoins n) → Prop)
    (hF : ∀ G c, P G c ↔ F ((G, fun i : Fin t => c i), fun j : Fin k => c (t + j))) :
    lazyProb n p pac pup P =
      (((SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod
          (Measure.pi fun _ : Fin t => dayLaw n pac pup)).prod
        (Measure.pi fun _ : Fin k => dayLaw n pac pup)).real {y | F y} := by
  have := lazyAux_msc (n := n)
  rw [← (lazyAux_measurePreserving p pac pup t k).measureReal_preimage
    (Set.to_countable _).measurableSet.nullMeasurableSet]
  unfold lazyProb
  congr 1
  ext x
  exact hF x.1 x.2

/-- An event that depends on the graph and on the coins of the days up to `t` has its
probability under `G(n, p) ⊗ dayLaw^t ⊗ dayLaw`. -/
private lemma lazyAux_lazyProb_eq_day (t : ℕ) (P : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop)
    (F : (SimpleGraph (Fin n) × (Fin t → DayCoins n)) × DayCoins n → Prop)
    (hF : ∀ G c, P G c ↔ F ((G, fun i : Fin t => c i), c t)) :
    lazyProb n p pac pup P =
      (((SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod
          (Measure.pi fun _ : Fin t => dayLaw n pac pup)).prod (dayLaw n pac pup)).real
        {y | F y} := by
  have := lazyAux_msc (n := n)
  rw [← (lazyAux_measurePreserving_day p pac pup t).measureReal_preimage
    (Set.to_countable _).measurableSet.nullMeasurableSet]
  unfold lazyProb
  congr 1
  ext x
  exact hF x.1 x.2

/-- The coins `w` on the days `0, …, t - 1`, and the default coins afterwards. -/
private def lazyAux_ext (t : ℕ) (w : Fin t → DayCoins n) : ℕ → DayCoins n :=
  fun i => if hi : i < t then w ⟨i, hi⟩ else default

private lemma lazyAux_ext_eq (t : ℕ) (c : ℕ → DayCoins n) {i : ℕ} (hi : i < t) :
    lazyAux_ext t (fun j : Fin t => c j) i = c i := by
  simp [lazyAux_ext, hi]

/-- The coins of day `t` are independent of the graph and of the coins of the earlier days. -/
theorem lazyProb_and_day (t : ℕ) (P : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop)
    (hP : ∀ G c c', (∀ i < t, c i = c' i) → (P G c ↔ P G c')) (Q : DayCoins n → Prop) :
    lazyProb n p pac pup (fun G c => P G c ∧ Q (c t)) =
      lazyProb n p pac pup P * (dayLaw n pac pup).real {d | Q d} := by
  have hPe : ∀ G (c : ℕ → DayCoins n),
      P G c ↔ (G, fun i : Fin t => c i) ∈ {z : SimpleGraph (Fin n) × (Fin t → DayCoins n) |
        P z.1 (lazyAux_ext t z.2)} :=
    fun G c => hP G c _ fun i hi => (lazyAux_ext_eq t c hi).symm
  rw [lazyAux_lazyProb_eq_day t (fun G c => P G c ∧ Q (c t))
      (fun y => y ∈ {z : SimpleGraph (Fin n) × (Fin t → DayCoins n) |
        P z.1 (lazyAux_ext t z.2)} ×ˢ {d | Q d}) (fun G c => and_congr (hPe G c) Iff.rfl),
    lazyAux_lazyProb_eq_day t P
      (fun y => y ∈ {z : SimpleGraph (Fin n) × (Fin t → DayCoins n) |
        P z.1 (lazyAux_ext t z.2)} ×ˢ (Set.univ : Set (DayCoins n)))
      (fun G c => (hPe G c).trans ⟨fun h => ⟨h, Set.mem_univ _⟩, fun h => h.1⟩),
    Set.ofPred_mem_eq, Set.ofPred_mem_eq, measureReal_prod_prod, measureReal_prod_prod,
    probReal_univ, mul_one]

/-- Conditioning on the graph and on the coins of the other days: if an event depends on the
coins of the days up to `t` only and, whatever the graph and the coins of the other days, the coins
of day `t` make it happen with probability at most `ε`, then its probability is at most `ε`. -/
theorem lazyProb_le_of_forall_day {ε : ℝ} (t : ℕ)
    (P : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop)
    (hP : ∀ G c c', (∀ i ≤ t, c i = c' i) → (P G c ↔ P G c'))
    (h : ∀ G c, (dayLaw n pac pup).real {d | P G (Function.update c t d)} ≤ ε) :
    lazyProb n p pac pup P ≤ ε := by
  have := lazyAux_msc (n := n)
  have hε : 0 ≤ ε := measureReal_nonneg.trans (h ⊥ fun _ => default)
  rw [lazyAux_lazyProb_eq_day t P
    (fun y => P y.1.1 (Function.update (lazyAux_ext t y.1.2) t y.2)) fun G c => hP G c _ ?_]
  · rw [measureReal_def]
    refine ENNReal.toReal_le_of_le_ofReal hε ?_
    rw [Measure.prod_apply (Set.to_countable _).measurableSet]
    calc _ ≤ ∫⁻ _, ENNReal.ofReal ε ∂((SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod
          (Measure.pi fun _ : Fin t => dayLaw n pac pup)) :=
          lintegral_mono fun y =>
            (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε).2
              (h y.1 (lazyAux_ext t y.2))
      _ = ENNReal.ofReal ε := by rw [lintegral_const, measure_univ, mul_one]
  · intro i hi
    rcases hi.lt_or_eq with hi | rfl
    · rw [Function.update_of_ne hi.ne, lazyAux_ext_eq t c hi]
    · rw [Function.update_self]

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
  have := lazyAux_msc (n := n)
  have hε : 0 ≤ ε := measureReal_nonneg.trans (h ⊥ fun _ => default)
  rw [lazyAux_lazyProb_eq t k P
    (fun y => P y.1.1 (fun i => if hi : t ≤ i ∧ i < t + k then y.2 ⟨i - t, by omega⟩
      else lazyAux_ext t y.1.2 i)) fun G c => hP G c _ ?_]
  · rw [measureReal_def]
    refine ENNReal.toReal_le_of_le_ofReal hε ?_
    rw [Measure.prod_apply (Set.to_countable _).measurableSet]
    calc _ ≤ ∫⁻ _, ENNReal.ofReal ε ∂((SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod
          (Measure.pi fun _ : Fin t => dayLaw n pac pup)) :=
          lintegral_mono fun y =>
            (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε).2
              (h y.1 (lazyAux_ext t y.2))
      _ = ENNReal.ofReal ε := by rw [lintegral_const, measure_univ, mul_one]
  · intro i hi
    by_cases hti : t ≤ i
    · rw [dite_eq_left ⟨hti, hi⟩]
      show c i = c (t + (i - t))
      congr 1
      omega
    · rw [dite_eq_right fun h => hti h.1, lazyAux_ext_eq t c (by omega)]

/-- An event about the graph and the coins of day `t` only has its probability under the product
of `G(n, p)` and the law of one day's coins. -/
theorem lazyProb_eq_of_day (t : ℕ) (Q : SimpleGraph (Fin n) → DayCoins n → Prop) :
    lazyProb n p pac pup (fun G c => Q G (c t)) =
      ((SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod (dayLaw n pac pup)).real
        {x | Q x.1 x.2} := by
  have := lazyAux_msc (n := n)
  have h : MeasurePreserving (Prod.map id (Function.eval t)) (lazyLaw n p pac pup)
      ((SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod (dayLaw n pac pup)) :=
    (MeasurePreserving.id _).prod
      (measurePreserving_eval_infinitePi (fun _ : ℕ => dayLaw n pac pup) t)
  rw [← h.measureReal_preimage (Set.to_countable _).measurableSet.nullMeasurableSet]
  rfl

/-- The product of `G(n, p)` and the law of one day's coins, as an average over the coins. -/
theorem prod_dayLaw_real_eq_sum (Q : SimpleGraph (Fin n) → DayCoins n → Prop) :
    ((SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod (dayLaw n pac pup)).real
        {x | Q x.1 x.2} =
      ∑ d : DayCoins n, (dayLaw n pac pup).real {d} * gnpProb n p (fun G => Q G d) := by
  have := lazyAux_msc (n := n)
  have hS : MeasurableSet {x : SimpleGraph (Fin n) × DayCoins n | Q x.1 x.2} :=
    (Set.to_countable _).measurableSet
  rw [measureReal_def, Measure.prod_apply_symm hS, lintegral_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def, mul_comm]
    rfl
  · intro d _
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

/-- The mass of a single colouring under the product of Bernoulli laws. -/
private lemma lazyAux_pi_real_singleton {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (χ : Fin n → Bool) :
    (Measure.pi fun _ : Fin n => bernoulliMeasure true false (toUnit q)).real {χ} =
      ∏ v, if χ v then q else 1 - q := by
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← measureReal_def]
  cases χ v
  · simp [toUnit_coe hq0 hq1]
  · simp [toUnit_coe hq0 hq1]

theorem dayLaw_real_singleton (hpac0 : 0 ≤ pac) (hpac1 : pac ≤ 1) (hpup0 : 0 ≤ pup)
    (hpup1 : pup ≤ 1) (d : DayCoins n) :
    (dayLaw n pac pup).real {d} =
      (∏ v, if d.1 v then pac else 1 - pac) * ∏ v, if d.2 v then pup else 1 - pup := by
  obtain ⟨a, u⟩ := d
  rw [dayLaw, ← Set.singleton_prod_singleton, measureReal_prod_prod,
    lazyAux_pi_real_singleton hpac0 hpac1, lazyAux_pi_real_singleton hpup0 hpup1]

/-- The update coins of a day are independent of its activation coins. -/
theorem dayLaw_real_le_of_forall_act {ε : ℝ} (Q : (Fin n → Bool) → (Fin n → Bool) → Prop)
    (h : ∀ a, (Measure.pi fun _ : Fin n => bernoulliMeasure true false (toUnit pup)).real
      {u | Q a u} ≤ ε) :
    (dayLaw n pac pup).real {d | Q d.1 d.2} ≤ ε := by
  have hε : 0 ≤ ε := measureReal_nonneg.trans (h fun _ => true)
  have hS : MeasurableSet {d : DayCoins n | Q d.1 d.2} := (Set.to_countable _).measurableSet
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal hε ?_
  rw [dayLaw, Measure.prod_apply hS]
  calc _ ≤ ∫⁻ _, ENNReal.ofReal ε
        ∂(Measure.pi fun _ : Fin n => bernoulliMeasure true false (toUnit pac)) :=
        lintegral_mono fun a =>
          (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε).2 (h a)
    _ = ENNReal.ofReal ε := by rw [lintegral_const, measure_univ, mul_one]

/-- A Bernoulli family stays one along a measure-preserving map. -/
private lemma lazyAux_isBernoulliFamily_comp {Ω Ω' ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [Fintype ι] {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {q : ℝ} {X : ι → Ω → ℝ} {f : Ω' → Ω} (hf : MeasurePreserving f μ' μ)
    (hX : IsBernoulliFamily μ q X) : IsBernoulliFamily μ' q (fun i ω => X i (f ω)) := by
  have hm : ∀ i, Measurable (fun ω => X i (f ω)) := fun i =>
    (hX.measurable i).comp hf.measurable
  refine ⟨hm, ?_, fun i ω => hX.zero_or_one i (f ω), fun i => ?_⟩
  · refine (iIndepFun_iff_map_fun_eq_pi_map fun i => (hm i).aemeasurable).2 ?_
    have h1 : μ'.map (fun ω i => X i (f ω)) = μ.map (fun ω i => X i ω) := by
      rw [← hf.map_eq, Measure.map_map (measurable_pi_iff.2 hX.measurable) hf.measurable]
      rfl
    have h2 : ∀ i, μ'.map (fun ω => X i (f ω)) = μ.map (X i) := fun i => by
      rw [← hf.map_eq, Measure.map_map (hX.measurable i) hf.measurable]
      rfl
    rw [h1, hX.indep.map_fun_eq_pi_map fun i => (hX.measurable i).aemeasurable]
    simp_rw [h2]
  · rw [← hX.prob_one i]
    exact hf.measureReal_preimage ((hX.measurable i) (measurableSet_singleton 1)).nullMeasurableSet

/-- The indicators that the coordinates of a product of copies of one probability measure have a
property form a Bernoulli family. -/
private lemma lazyAux_isBernoulliFamily_pi {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    [IsProbabilityMeasure ν] (R : Y → Prop) [DecidablePred R] (hR : MeasurableSet {y | R y})
    {q : ℝ} (hq : ν.real {y | R y} = q) :
    IsBernoulliFamily (Measure.pi fun _ : Fin n => ν) q (fun v ω => if R (ω v) then 1 else 0) := by
  have hm : Measurable (fun y : Y => if R y then (1 : ℝ) else 0) :=
    Measurable.ite hR measurable_const measurable_const
  refine ⟨fun v => hm.comp (measurable_pi_apply v),
    iIndepFun_pi (X := fun _ y => if R y then (1 : ℝ) else 0) (fun _ => hm.aemeasurable),
    fun v ω => ?_, fun v => ?_⟩
  · by_cases h : R (ω v) <;> simp [h]
  · have hset : {ω : Fin n → Y | (if R (ω v) then (1 : ℝ) else 0) = 1} =
        Function.eval v ⁻¹' {y | R y} := by
      ext ω
      by_cases h : R (ω v) <;> simp [h]
    rw [hset, (measurePreserving_eval (fun _ : Fin n => ν) v).measureReal_preimage
      hR.nullMeasurableSet, hq]

/-- Independent coins, each `true` with probability `q`, as a Bernoulli family. -/
theorem isBernoulliFamily_coins {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsBernoulliFamily (Measure.pi fun _ : Fin n => bernoulliMeasure true false (toUnit q)) q
      (fun v ω => if ω v then 1 else 0) := by
  refine lazyAux_isBernoulliFamily_pi _ (fun b => b = true) MeasurableSet.of_discrete ?_
  have h : {b : Bool | b = true} = {true} := by
    ext b
    simp
  rw [h, bernoulliMeasure_real_apply_of_mem_of_notMem _ (measurableSet_singleton _)
    (Set.mem_singleton true) (by simp), toUnit_coe hq0 hq1]

/-- The activation indicators of a day are independent Bernoulli(`p_ac`) variables. -/
theorem isBernoulliFamily_act (hpac0 : 0 ≤ pac) (hpac1 : pac ≤ 1) :
    IsBernoulliFamily (dayLaw n pac pup) pac (fun v d => if d.1 v then 1 else 0) :=
  lazyAux_isBernoulliFamily_comp (f := Prod.fst) measurePreserving_fst
    (isBernoulliFamily_coins hpac0 hpac1)

/-- The update coins of a day are independent Bernoulli(`p_up`) variables. -/
theorem isBernoulliFamily_upd (hpup0 : 0 ≤ pup) (hpup1 : pup ≤ 1) :
    IsBernoulliFamily (dayLaw n pac pup) pup (fun v d => if d.2 v then 1 else 0) :=
  lazyAux_isBernoulliFamily_comp (f := Prod.snd) measurePreserving_snd
    (isBernoulliFamily_coins hpup0 hpup1)

/-- The indicators that a vertex updates on a day are independent Bernoulli(`p_ac p_up`)
variables. -/
theorem isBernoulliFamily_actUpd (hpac0 : 0 ≤ pac) (hpac1 : pac ≤ 1) (hpup0 : 0 ≤ pup)
    (hpup1 : pup ≤ 1) :
    IsBernoulliFamily (dayLaw n pac pup) (pac * pup)
      (fun v d => if d.1 v = true ∧ d.2 v = true then 1 else 0) := by
  have hf := MeasurePreserving.symm (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin n))
    (measurePreserving_arrowProdEquivProdArrow Bool Bool (Fin n)
      (fun _ => bernoulliMeasure true false (toUnit pac))
      (fun _ => bernoulliMeasure true false (toUnit pup)))
  have hq : ((bernoulliMeasure true false (toUnit pac)).prod
      (bernoulliMeasure true false (toUnit pup))).real
        {y : Bool × Bool | y.1 = true ∧ y.2 = true} = pac * pup := by
    have h : {y : Bool × Bool | y.1 = true ∧ y.2 = true} = {true} ×ˢ {true} := by
      ext y
      simp [Prod.ext_iff]
    rw [h, measureReal_prod_prod,
      bernoulliMeasure_real_apply_of_mem_of_notMem _ (measurableSet_singleton _)
        (Set.mem_singleton true) (by simp),
      bernoulliMeasure_real_apply_of_mem_of_notMem _ (measurableSet_singleton _)
        (Set.mem_singleton true) (by simp), toUnit_coe hpac0 hpac1, toUnit_coe hpup0 hpup1]
  exact lazyAux_isBernoulliFamily_comp hf
    (lazyAux_isBernoulliFamily_pi (n := n) _ (fun y : Bool × Bool => y.1 = true ∧ y.2 = true)
      MeasurableSet.of_discrete hq)

open Classical in
/-- The number of vertices of `S` whose coin is `true`, as a sum of indicators. -/
theorem ncard_inter_setOf_eq_sum (S : Set (Fin n)) (ω : Fin n → Bool) :
    ((S ∩ {v | ω v = true}).ncard : ℝ) = ∑ v ∈ S.toFinset, (if ω v then 1 else 0 : ℝ) := by
  rw [Finset.sum_boole, ← Set.ncard_coe_finset]
  congr 2
  ext v
  simp

end PowerOfFew

end
