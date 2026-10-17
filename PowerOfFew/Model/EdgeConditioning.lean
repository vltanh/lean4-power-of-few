module

public import PowerOfFew.Model.Gnp
public import PowerOfFew.Model.Majority

/-!
# Conditioning on edges of `G(n, p)`

The tools of the papers' "Day One" arguments (dense paper, Claims 2.5 and 2.6; sparse paper,
Proposition 2.2):

* `nbrCount_graphOfEdges`: the number of neighbours of `v` in `S` is the sum of the indicators of
  the edges `vu`, `u ∈ S \ {v}`; these indicators form a Bernoulli family
  (`isBernoulliFamily_edgesAt`), so neighbour counts in disjoint sets are independent binomials;
* `dependsOn_mem_majorityStep`: whether `v` is Blue the next day depends only on the edges at `v`;
* `integral_mul_of_dependsOn_disjoint`: functions of disjoint sets of edges are independent;
* `edgeCondExp`, `integral_eq_edgeCondExp`: expectations with one edge variable fixed, and the law
  of total expectation over that edge;
* `covariance_shared_edge`: if `f` and `g` depend on disjoint sets of edges plus one common edge
  `e`, then `Cov(f, g) = p(1 − p)(a_f − b_f)(a_g − b_g)`, where `a` and `b` are the expectations
  with `e` present and absent (the dense paper's equation (2.3); the sparse paper's covariance
  identity in the proof of Proposition 2.2).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew

variable {n : ℕ} {p : ℝ}

/-- The pairs `{v, u}`, `u ≠ v`: the possible edges at `v`. -/
def edgesAt (v : Fin n) : Set (Sym2 (Fin n)) := {e | ∃ u, u ≠ v ∧ e = s(v, u)}

/-- The expectation of `f` under `G(n, p)` with the edge variable `e` set to `b`. -/
def edgeCondExp (n : ℕ) (p : ℝ) (e : Sym2 (Fin n)) (b : Prop) (f : EdgeVars n → ℝ) : ℝ :=
  ∫ ω, f (Function.update ω e b) ∂(edgeLaw n p)

open Classical in
/-- The number of neighbours of `v` in `S` is the sum of the indicators of the edges `vu`,
`u ∈ S \ {v}`. -/
theorem nbrCount_graphOfEdges (ω : EdgeVars n) (S : Set (Fin n)) (v : Fin n) :
    (nbrCount (graphOfEdges ω) S v : ℝ) =
      ∑ u ∈ Finset.univ.filter (fun u => u ∈ S ∧ u ≠ v), edgeInd s(v, u) ω := by
  have h1 : {u | (graphOfEdges ω).Adj v u ∧ u ∈ S} =
      ↑((Finset.univ.filter (fun u => u ∈ S ∧ u ≠ v)).filter (fun u => ω s(v, u))) := by
    ext u
    simp only [Set.mem_ofPred_eq, adj_graphOfEdges, Finset.coe_filter, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨huv, hω⟩, hS⟩
      exact ⟨⟨hS, Ne.symm huv⟩, hω⟩
    · rintro ⟨⟨hS, huv⟩, hω⟩
      exact ⟨⟨Ne.symm huv, hω⟩, hS⟩
  rw [nbrCount, h1, Set.ncard_coe_finset]
  simp only [edgeInd]
  rw [Finset.sum_boole]

/-- The indicators of the edges at `v` form a Bernoulli(`p`) family. -/
theorem isBernoulliFamily_edgesAt (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : Fin n) :
    IsBernoulliFamily (edgeLaw n p) p (fun u : {u : Fin n // u ≠ v} => edgeInd s(v, u.1)) := by
  let f : {u : Fin n // u ≠ v} → OffDiag n := fun u =>
    ⟨s(v, u.1), by rw [Sym2.mk_isDiag_iff]; exact Ne.symm u.2⟩
  have hinj : Function.Injective f := by
    intro u w h
    have h' : s(v, u.1) = s(v, w.1) := congrArg Subtype.val h
    exact Subtype.ext (Sym2.congr_right.1 h')
  exact (isBernoulliFamily_edgeInd hp0 hp1).comp hinj

/-- Whether `v` is Blue the next day depends only on the edges at `v`. -/
theorem dependsOn_mem_majorityStep (B : Set (Fin n)) (v : Fin n) :
    DependsOn (fun ω : EdgeVars n => v ∈ majorityStep (graphOfEdges ω) B) (edgesAt v) := by
  intro ω ω' h
  have hnbr : ∀ S : Set (Fin n),
      nbrCount (graphOfEdges ω) S v = nbrCount (graphOfEdges ω') S v := by
    intro S
    unfold nbrCount
    congr 1
    ext u
    simp only [Set.mem_ofPred_eq, adj_graphOfEdges]
    by_cases huv : v = u
    · simp [huv]
    · rw [h s(v, u) ⟨u, Ne.symm huv, rfl⟩]
  simp only [majorityStep, Set.mem_ofPred_eq, hnbr]

theorem edgesAt_inter_edgesAt {v w : Fin n} (hvw : v ≠ w) :
    edgesAt v ∩ edgesAt w = {s(v, w)} := by
  ext e
  simp only [edgesAt, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨u, _, rfl⟩, ⟨u', _, h⟩⟩
    rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact absurd h1 hvw
    · rw [h2]
  · rintro rfl
    exact ⟨⟨w, Ne.symm hvw, rfl⟩, ⟨v, hvw, Sym2.eq_swap⟩⟩

/-- Bounded functions of disjoint sets of edge variables are independent. -/
theorem integral_mul_of_dependsOn_disjoint {f g : EdgeVars n → ℝ} {s t : Set (Sym2 (Fin n))}
    (hf : DependsOn f s) (hg : DependsOn g t) (hst : Disjoint s t) {C : ℝ}
    (hfC : ∀ ω, |f ω| ≤ C) (hgC : ∀ ω, |g ω| ≤ C) :
    ∫ ω, f ω * g ω ∂(edgeLaw n p) = (∫ ω, f ω ∂(edgeLaw n p)) * ∫ ω, g ω ∂(edgeLaw n p) := by
  -- The coordinates of the product measure are independent.
  have hcoord : iIndepFun (fun (e : Sym2 (Fin n)) (ω : EdgeVars n) => ω e) (edgeLaw n p) :=
    iIndepFun_pi (μ := fun e : Sym2 (Fin n) => bernoulliMeasure (¬ e.IsDiag) False (toUnit p))
      (X := fun _ (b : Prop) => b) (fun _ => measurable_id.aemeasurable)
  have hST := hcoord.indepFun_set s t hst (fun e => measurable_pi_apply e)
  obtain ⟨F, hF⟩ := dependsOn_iff_exists_comp.1 hf
  obtain ⟨G, hG⟩ := dependsOn_iff_exists_comp.1 hg
  have hFG : IndepFun f g (edgeLaw n p) := by
    rw [hF, hG]
    exact hST.comp Measurable.of_discrete Measurable.of_discrete
  exact hFG.integral_fun_mul_eq_mul_integral Measurable.of_discrete.aestronglyMeasurable
    Measurable.of_discrete.aestronglyMeasurable

/-- The law of total expectation over one edge variable. -/
theorem integral_eq_edgeCondExp (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {e : Sym2 (Fin n)} (he : ¬ e.IsDiag)
    {f : EdgeVars n → ℝ} {C : ℝ} (hfC : ∀ ω, |f ω| ≤ C) :
    ∫ ω, f ω ∂(edgeLaw n p) = p * edgeCondExp n p e True f + (1 - p) * edgeCondExp n p e False f := by
  -- Split on the value of the edge variable `e`.
  have hsplit : ∀ ω, f ω = edgeInd e ω * f (Function.update ω e True) +
      (1 - edgeInd e ω) * f (Function.update ω e False) := by
    intro ω
    by_cases h : ω e
    · have h' : Function.update ω e True = ω := Function.update_eq_self_iff.2 (eq_true h).symm
      simp [edgeInd, h, h']
    · have h' : Function.update ω e False = ω := Function.update_eq_self_iff.2 (eq_false h).symm
      simp [edgeInd, h, h']
  -- The indicator of `e` and the functions with `e` fixed depend on disjoint sets of edges.
  have hind : DependsOn (edgeInd (n := n) e) {e} := by
    intro ω ω' h
    show edgeInd e ω = edgeInd e ω'
    rw [edgeInd, edgeInd, h e rfl]
  have hind' : DependsOn (fun ω : EdgeVars n => 1 - edgeInd e ω) {e} := by
    intro ω ω' h
    show 1 - edgeInd e ω = 1 - edgeInd e ω'
    rw [edgeInd, edgeInd, h e rfl]
  have hupd : ∀ b : Prop, DependsOn (fun ω : EdgeVars n => f (Function.update ω e b)) {e}ᶜ := by
    intro b ω ω' h
    have h' : Function.update ω e b = Function.update ω' e b := by
      funext i
      by_cases hi : i = e
      · rw [hi, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hi, Function.update_of_ne hi, h i hi]
    show f (Function.update ω e b) = f (Function.update ω' e b)
    rw [h']
  have hdisj : Disjoint ({e} : Set (Sym2 (Fin n))) {e}ᶜ := disjoint_compl_right
  have hbd : ∀ ω, |edgeInd e ω| ≤ max C 1 := by
    intro ω
    refine le_trans ?_ (le_max_right _ _)
    unfold edgeInd
    split_ifs <;> simp
  have hbd' : ∀ ω, |1 - edgeInd e ω| ≤ max C 1 := by
    intro ω
    refine le_trans ?_ (le_max_right _ _)
    unfold edgeInd
    split_ifs <;> simp
  have hbdf : ∀ (b : Prop) ω, |f (Function.update ω e b)| ≤ max C 1 :=
    fun b ω => (hfC _).trans (le_max_left _ _)
  have hp : ∫ ω, edgeInd e ω ∂(edgeLaw n p) = p :=
    (isBernoulliFamily_edgeInd (n := n) hp0 hp1).integral_eq ⟨e, he⟩
  have hp' : ∫ ω, (1 - edgeInd e ω) ∂(edgeLaw n p) = 1 - p := by
    rw [integral_sub (integrable_const _) Integrable.of_finite, hp]
    simp
  calc ∫ ω, f ω ∂(edgeLaw n p)
      = ∫ ω, (edgeInd e ω * f (Function.update ω e True) +
          (1 - edgeInd e ω) * f (Function.update ω e False)) ∂(edgeLaw n p) := by
        congr 1
        ext ω
        exact hsplit ω
    _ = ∫ ω, edgeInd e ω * f (Function.update ω e True) ∂(edgeLaw n p) +
          ∫ ω, (1 - edgeInd e ω) * f (Function.update ω e False) ∂(edgeLaw n p) :=
        integral_add Integrable.of_finite Integrable.of_finite
    _ = p * edgeCondExp n p e True f + (1 - p) * edgeCondExp n p e False f := by
        rw [integral_mul_of_dependsOn_disjoint hind (hupd True) hdisj hbd (hbdf True),
          integral_mul_of_dependsOn_disjoint hind' (hupd False) hdisj hbd' (hbdf False), hp, hp']
        rfl

/-- **The covariance of two functions sharing one edge.** If `f` depends only on the edges in
`s ∪ {e}` and `g` only on those in `t ∪ {e}`, with `s`, `t` disjoint and `e ∉ s ∪ t`, then
`Cov(f, g) = p(1 − p)(a_f − b_f)(a_g − b_g)`, where `a` and `b` are the expectations with the edge
`e` present and absent. -/
theorem covariance_shared_edge (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {e : Sym2 (Fin n)} (he : ¬ e.IsDiag)
    {f g : EdgeVars n → ℝ} {s t : Set (Sym2 (Fin n))} (hf : DependsOn f (insert e s))
    (hg : DependsOn g (insert e t)) (hst : Disjoint s t) (hes : e ∉ s) (het : e ∉ t) {C : ℝ}
    (hfC : ∀ ω, |f ω| ≤ C) (hgC : ∀ ω, |g ω| ≤ C) :
    ∫ ω, f ω * g ω ∂(edgeLaw n p) - (∫ ω, f ω ∂(edgeLaw n p)) * ∫ ω, g ω ∂(edgeLaw n p) =
      p * (1 - p) * (edgeCondExp n p e True f - edgeCondExp n p e False f) *
        (edgeCondExp n p e True g - edgeCondExp n p e False g) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hfC fun _ => False)
  have hfgC : ∀ ω, |f ω * g ω| ≤ C * C := fun ω => by
    rw [abs_mul]
    exact mul_le_mul (hfC ω) (hgC ω) (abs_nonneg _) hC
  -- With the edge `e` fixed, `f` and `g` depend on the disjoint sets `s` and `t`.
  have hfix : ∀ (b : Prop) (h : EdgeVars n → ℝ) (u : Set (Sym2 (Fin n))), e ∉ u →
      DependsOn h (insert e u) → DependsOn (fun ω => h (Function.update ω e b)) u := by
    intro b h u heu hh ω ω' hωω'
    apply hh
    intro i hi
    rcases Set.mem_insert_iff.1 hi with rfl | hi
    · simp
    · have hie : i ≠ e := fun h' => heu (h' ▸ hi)
      simp [Function.update_of_ne hie, hωω' i hi]
  have hprod : ∀ b : Prop, edgeCondExp n p e b (fun ω => f ω * g ω) =
      edgeCondExp n p e b f * edgeCondExp n p e b g := fun b =>
    integral_mul_of_dependsOn_disjoint (hfix b f s hes hf) (hfix b g t het hg) hst
      (fun _ => hfC _) (fun _ => hgC _)
  rw [integral_eq_edgeCondExp hp0 hp1 he hfgC, integral_eq_edgeCondExp hp0 hp1 he hfC,
    integral_eq_edgeCondExp hp0 hp1 he hgC, hprod True, hprod False]
  ring

end PowerOfFew

end
