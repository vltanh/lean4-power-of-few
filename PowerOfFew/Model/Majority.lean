module

public import PowerOfFew.Defs
public import External.GolesOlivos.GolesOlivos

/-!
# Majority dynamics: basic facts

* The update rule in the papers' arithmetic form (`notMem_majorityStep_iff`): a vertex is Red the
  next day iff its Red neighbours outnumber its Blue neighbours minus one if it is Red today.
* Monotonicity (`majorityStep_mono`, `blueAfter_mono`): a larger Blue set today gives a larger
  Blue set tomorrow. The papers do not state this; the formalization uses it to reduce
  "at most `m` Blue vertices" to "exactly the largest admissible number".
* Unanimity is permanent (`majorityStep_empty`, `blueAfter_eq_empty_of_le`).
* `Shrinks G m₁ m₂`: every Blue set of at most `m₁` vertices has at most `m₂` Blue vertices the
  next day (the dense paper's "universal reduction", Definition 18 of its arXiv version).
* A Blue set of at most `m` vertices vanishes the next day when every degree exceeds `2m`
  (`majorityStep_eq_empty_of_lt_degree`).
* Majority dynamics is eventually periodic with period at most two
  (`blueAfter_eventually_period_two`), by the theorem of Goles and Olivos and of Poljak and Sůra
  for symmetric threshold networks (`External.GolesOlivos.eventually_period_two`): the tie-keeping
  majority rule is the threshold network with weights `w_{vu} = 2 [u ∼ v] + [u = v]` and
  thresholds `b_v = deg v + 1`.
-/

@[expose] public section

noncomputable section

namespace PowerOfFew

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- `G` shrinks every Blue set of at most `m₁` vertices to at most `m₂` vertices the next day. -/
def Shrinks (m₁ m₂ : ℝ) : Prop :=
  ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ m₁ → ((majorityStep G B).ncard : ℝ) ≤ m₂

theorem nbrCount_add_nbrCount_compl (B : Set (Fin n)) (v : Fin n) :
    nbrCount G B v + nbrCount G Bᶜ v = degree G v := by
  -- The Blue and the Red neighbours of `v` partition its neighbourhood.
  have h1 : {u | G.Adj v u ∧ u ∈ B} = G.neighborSet v ∩ B := rfl
  have h2 : {u | G.Adj v u ∧ u ∈ Bᶜ} = G.neighborSet v \ B := rfl
  unfold nbrCount degree
  rw [h1, h2]
  exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _

open Classical in
/-- A vertex is Red the next day iff its Blue neighbours are fewer than its Red neighbours, plus
one if it is Red today (dense paper, equation (2.1): `v ∈ R₁ ⟺ d_{R₀}(v) > d_{B₀}(v) − I₀(v)`). -/
theorem notMem_majorityStep_iff (B : Set (Fin n)) (v : Fin n) :
    v ∉ majorityStep G B ↔
      (nbrCount G B v : ℤ) < nbrCount G Bᶜ v + (if v ∈ B then 0 else 1) := by
  by_cases hv : v ∈ B
  · simp [majorityStep, hv]
    omega
  · simp [majorityStep, hv]

theorem majorityStep_mono {B B' : Set (Fin n)} (h : B ⊆ B') :
    majorityStep G B ⊆ majorityStep G B' := by
  intro v hv
  -- More Blue neighbours and fewer Red neighbours in `B'` than in `B`.
  have hB : nbrCount G B v ≤ nbrCount G B' v :=
    Set.ncard_le_ncard (fun u hu => ⟨hu.1, h hu.2⟩)
  have hC : nbrCount G B'ᶜ v ≤ nbrCount G Bᶜ v :=
    Set.ncard_le_ncard (fun u hu => ⟨hu.1, fun hu' => hu.2 (h hu')⟩)
  simp only [majorityStep, Set.mem_ofPred_eq] at hv ⊢
  rcases hv with hv | ⟨hv1, hv2⟩
  · left; omega
  · by_cases hlt : nbrCount G B'ᶜ v < nbrCount G B' v
    · exact Or.inl hlt
    · exact Or.inr ⟨by omega, h hv2⟩

@[simp] theorem majorityStep_empty : majorityStep G ∅ = ∅ := by
  ext v
  simp [majorityStep, nbrCount]

@[simp] theorem majorityStep_univ : majorityStep G Set.univ = Set.univ := by
  ext v
  have h0 : nbrCount G Set.univᶜ v = 0 := by simp [nbrCount]
  simp only [majorityStep, Set.mem_ofPred_eq, Set.mem_univ, and_true, iff_true, h0]
  omega

@[simp] theorem blueAfter_zero (B₀ : Set (Fin n)) : blueAfter G B₀ 0 = B₀ := rfl

theorem blueAfter_succ (B₀ : Set (Fin n)) (t : ℕ) :
    blueAfter G B₀ (t + 1) = majorityStep G (blueAfter G B₀ t) := by
  exact Function.iterate_succ_apply' _ _ _

theorem blueAfter_add (B₀ : Set (Fin n)) (s t : ℕ) :
    blueAfter G B₀ (s + t) = blueAfter G (blueAfter G B₀ s) t := by
  unfold blueAfter
  rw [add_comm, Function.iterate_add_apply]

theorem blueAfter_mono {B B' : Set (Fin n)} (h : B ⊆ B') (t : ℕ) :
    blueAfter G B t ⊆ blueAfter G B' t := by
  induction t with
  | zero => exact h
  | succ t ih =>
    rw [blueAfter_succ, blueAfter_succ]
    exact majorityStep_mono G ih

theorem blueAfter_eq_empty_of_le {B₀ : Set (Fin n)} {s t : ℕ} (h : blueAfter G B₀ s = ∅)
    (hst : s ≤ t) : blueAfter G B₀ t = ∅ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [blueAfter_add, h]
  exact Function.iterate_fixed (majorityStep_empty G) k

theorem blueAfter_eq_univ_of_le {B₀ : Set (Fin n)} {s t : ℕ} (h : blueAfter G B₀ s = Set.univ)
    (hst : s ≤ t) : blueAfter G B₀ t = Set.univ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [blueAfter_add, h]
  exact Function.iterate_fixed (majorityStep_univ G) k

/-- If every degree exceeds `2m`, every Blue set of at most `m` vertices vanishes the next day. -/
theorem majorityStep_eq_empty_of_lt_degree {m : ℝ} (hdeg : ∀ v, 2 * m < degree G v)
    {B : Set (Fin n)} (hB : (B.ncard : ℝ) ≤ m) : majorityStep G B = ∅ := by
  ext v
  -- `v` has at most `|B| ≤ m` Blue neighbours, hence more than `deg v − m > m` Red ones.
  have hle : nbrCount G B v ≤ B.ncard := Set.ncard_le_ncard (fun u hu => hu.2)
  have hsum := nbrCount_add_nbrCount_compl G B v
  have hlt : nbrCount G B v < nbrCount G Bᶜ v := by
    have h1 : (nbrCount G B v : ℝ) ≤ B.ncard := by exact_mod_cast hle
    have h2 : ((nbrCount G B v + nbrCount G Bᶜ v : ℕ) : ℝ) = degree G v := by rw [hsum]
    have h3 := hdeg v
    push_cast at h2
    exact_mod_cast (by linarith : (nbrCount G B v : ℝ) < nbrCount G Bᶜ v)
  simp only [majorityStep, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_or,
    not_and]
  exact ⟨by omega, fun h => absurd h (by omega)⟩

/-- Shrinking is monotone in the source bound and the target bound. -/
theorem Shrinks.mono {m₁ m₂ m₁' m₂' : ℝ} (h : Shrinks G m₁ m₂) (h₁ : m₁' ≤ m₁) (h₂ : m₂ ≤ m₂') :
    Shrinks G m₁' m₂' := by
  intro B hB
  exact (h B (hB.trans h₁)).trans h₂

/-! ### Majority dynamics as a symmetric threshold network -/

open Classical in
/-- The weights `w_{vu} = 2 [u ∼ v] + [u = v]`. -/
private def goAux_weight {n : ℕ} (G : SimpleGraph (Fin n)) (v u : Fin n) : ℝ :=
  (if G.Adj v u then 2 else 0) + (if u = v then 1 else 0)

/-- The thresholds `b_v = deg v + 1`. -/
private def goAux_thr {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℝ := (degree G v : ℝ) + 1

private theorem goAux_weight_symm {n : ℕ} (G : SimpleGraph (Fin n)) (v u : Fin n) :
    goAux_weight G v u = goAux_weight G u v := by
  unfold goAux_weight
  rw [G.adj_comm v u]
  by_cases h : u = v
  · subst h
    rfl
  · simp [h, Ne.symm h]

/-- The field of `v` in the state `y` is `2 · (number of Blue neighbours) + [v is Blue]`, where the
Blue vertices are those in the state `true`. -/
private theorem goAux_field_eq {n : ℕ} (G : SimpleGraph (Fin n)) (y : Fin n → Bool) (v : Fin n) :
    ∑ u, goAux_weight G v u * (if y u then 1 else 0) =
      2 * (nbrCount G {u | y u = true} v : ℝ) + (if y v then 1 else 0) := by
  classical
  have hcount : (nbrCount G {u | y u = true} v : ℝ) =
      ∑ u, if G.Adj v u ∧ y u = true then 1 else 0 := by
    have h : {u | G.Adj v u ∧ u ∈ {u | y u = true}} =
        ↑(Finset.univ.filter fun u => G.Adj v u ∧ y u = true) := by
      ext u
      simp
    unfold nbrCount
    rw [h, Set.ncard_coe_finset, Finset.natCast_card_filter]
  have hpt : ∀ u, goAux_weight G v u * (if y u then 1 else 0) =
      2 * (if G.Adj v u ∧ y u = true then 1 else 0) +
        (if u = v then (if y v then 1 else 0) else 0) := by
    intro u
    by_cases huv : u = v
    · subst huv
      simp [goAux_weight]
    · by_cases hadj : G.Adj v u <;> by_cases hy : y u <;> simp [goAux_weight, huv, hadj, hy]
  rw [hcount]
  simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]

/-- One step of the threshold network with the weights `goAux_weight G` and the thresholds
`goAux_thr G` is one day of majority dynamics: a vertex is Blue the next day iff
`deg v + 1 ≤ 2 · (number of Blue neighbours) + [v is Blue]`. -/
private theorem goAux_step_eq {n : ℕ} (G : SimpleGraph (Fin n)) (y : Fin n → Bool) :
    {v | External.GolesOlivos.step (goAux_weight G) (goAux_thr G) y v = true} =
      majorityStep G {v | y v = true} := by
  ext v
  have hsum := nbrCount_add_nbrCount_compl G {u | y u = true} v
  simp only [Set.mem_ofPred_eq, External.GolesOlivos.step, goAux_thr, decide_eq_true_eq,
    goAux_field_eq, majorityStep]
  cases hy : y v
  · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, and_false, or_false]
    constructor
    · intro h
      have h' : degree G v + 1 ≤ 2 * nbrCount G {u | y u = true} v := by exact_mod_cast h
      omega
    · intro h
      have h' : degree G v + 1 ≤ 2 * nbrCount G {u | y u = true} v := by omega
      exact_mod_cast h'
  · simp only [↓reduceIte, and_true]
    constructor
    · intro h
      have h' : degree G v + 1 ≤ 2 * nbrCount G {u | y u = true} v + 1 := by exact_mod_cast h
      omega
    · intro h
      have h' : degree G v + 1 ≤ 2 * nbrCount G {u | y u = true} v + 1 := by omega
      exact_mod_cast h'

/-- The Blue sets of majority dynamics are the states of the threshold network. -/
private theorem goAux_blueAfter_eq {n : ℕ} (G : SimpleGraph (Fin n)) (y : Fin n → Bool) (t : ℕ) :
    blueAfter G {v | y v = true} t =
      {v | (External.GolesOlivos.step (goAux_weight G) (goAux_thr G))^[t] y v = true} := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [blueAfter_succ, ih, ← goAux_step_eq, Function.iterate_succ_apply']

/-- **Goles–Olivos (1981), Poljak–Sůra (1983)**, for majority dynamics. Majority dynamics on a
finite graph becomes periodic with period at most `2`: from some day on, the Blue set on day
`t + 2` equals that on day `t`. The tie-keeping majority rule is the symmetric threshold network
with weights `w_{vu} = 2 [u ∼ v] + [u = v]` and thresholds `b_v = deg v + 1`
(`External.GolesOlivos.eventually_period_two`). -/
theorem blueAfter_eventually_period_two {n : ℕ} (G : SimpleGraph (Fin n)) (B₀ : Set (Fin n)) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, blueAfter G B₀ (t + 2) = blueAfter G B₀ t := by
  classical
  -- The initial state of the threshold network: unit `v` is on iff `v` is Blue.
  have hB₀ : {v | decide (v ∈ B₀) = true} = B₀ := by
    ext v
    simp
  obtain ⟨t₀, ht₀⟩ := External.GolesOlivos.eventually_period_two (goAux_weight G)
    (goAux_weight_symm G) (goAux_thr G) (fun v => decide (v ∈ B₀))
  refine ⟨t₀, fun t ht => ?_⟩
  rw [← hB₀, goAux_blueAfter_eq, goAux_blueAfter_eq, ht₀ t ht]

end PowerOfFew

end
