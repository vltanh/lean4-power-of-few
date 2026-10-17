module

public import PowerOfFew.Model.Majority

/-!
# Majority dynamics is eventually periodic with period at most two

The theorem of Goles and Olivos (*Comportement périodique des fonctions à seuil binaires et
applications*, Discrete Applied Mathematics 3 (1981) 93–105) and of Poljak and Sůra (*On
periodical behaviour in societies with symmetric influences*, Combinatorica 3 (1983) 119–121),
which the sparse paper cites in the proof of its Theorem 3.1: on a finite graph, majority dynamics
(with ties kept) is eventually periodic with period 1 or 2. It is proved here; see `README.md`.
-/

@[expose] public section

noncomputable section

namespace PowerOfFew

/-! ### The Goles–Olivos Lyapunov function

Write `xᵥ = +1` if `v` is Blue and `xᵥ = −1` if `v` is Red (`spin`). The tie-keeping majority
rule is the symmetric threshold network `xᵥ(t + 1) = sign(∑_{u ∼ v} xᵤ(t) + xᵥ(t) / 2)` with the
weights `w = A + I / 2`. Everything is doubled to stay in `ℤ`: `hᵥ = field G B v =
2 ∑_{u ∼ v} xᵤ + xᵥ = 2 ∑ᵤ w_{vu} xᵤ` is twice the local field, an odd integer whose sign is the
next spin of `v`, and `energy G B B' = −∑ᵥ x'ᵥ hᵥ = −2 ∑_{u, v} w_{vu} x'ᵥ xᵤ` is twice the
Goles–Olivos energy `E(t) = −∑_{u, v} w_{uv} xᵤ(t + 1) xᵥ(t)` of two consecutive colourings. It
does not increase, and it drops by at least `2` on each day `t` with `x(t + 2) ≠ x(t)`; since it
takes finitely many values, `x(t + 2) = x(t)` from some day on. -/

open Classical in
/-- The spin of `v`: `+1` if `v` is Blue (in `B`), `−1` if it is Red. -/
private def spin {n : ℕ} (B : Set (Fin n)) (v : Fin n) : ℤ := if v ∈ B then 1 else -1

/-- `∑_{u ∼ v} xᵤ`: the number of Blue neighbours of `v` minus the number of its Red ones. -/
private def nbrDiff {n : ℕ} (G : SimpleGraph (Fin n)) (B : Set (Fin n)) (v : Fin n) : ℤ :=
  (nbrCount G B v : ℤ) - nbrCount G Bᶜ v

/-- Twice the local field of `v` for the weights `w = A + I / 2`: `2 ∑_{u ∼ v} xᵤ + xᵥ`. -/
private def field {n : ℕ} (G : SimpleGraph (Fin n)) (B : Set (Fin n)) (v : Fin n) : ℤ :=
  2 * nbrDiff G B v + spin B v

/-- Twice the Goles–Olivos energy of the consecutive Blue sets `B` and `B'`. -/
private def energy {n : ℕ} (G : SimpleGraph (Fin n)) (B B' : Set (Fin n)) : ℤ :=
  -∑ v, spin B' v * field G B v

open Classical in
private lemma nbrCount_eq_sum {n : ℕ} (G : SimpleGraph (Fin n)) (S : Set (Fin n)) (v : Fin n) :
    (nbrCount G S v : ℤ) = ∑ u, if G.Adj v u ∧ u ∈ S then 1 else 0 := by
  classical
  have h : {u | G.Adj v u ∧ u ∈ S} = ↑(Finset.univ.filter fun u => G.Adj v u ∧ u ∈ S) := by
    ext u
    simp
  unfold nbrCount
  rw [h, Set.ncard_coe_finset, Finset.natCast_card_filter]

open Classical in
private lemma nbrDiff_eq_sum {n : ℕ} (G : SimpleGraph (Fin n)) (B : Set (Fin n)) (v : Fin n) :
    nbrDiff G B v = ∑ u, if G.Adj v u then spin B u else 0 := by
  unfold nbrDiff
  rw [nbrCount_eq_sum, nbrCount_eq_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hadj : G.Adj v u <;> by_cases hu : u ∈ B <;> simp [spin, hadj, hu]

/-- The symmetry of the adjacency matrix: `∑ᵥ x'ᵥ ∑_{u ∼ v} xᵤ = ∑ᵥ xᵥ ∑_{u ∼ v} x'ᵤ`. -/
private lemma sum_spin_mul_nbrDiff_comm {n : ℕ} (G : SimpleGraph (Fin n)) (B B' : Set (Fin n)) :
    ∑ v, spin B' v * nbrDiff G B v = ∑ v, spin B v * nbrDiff G B' v := by
  simp only [nbrDiff_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  by_cases h : G.Adj u v
  · simp [h, h.symm, mul_comm]
  · have h' : ¬G.Adj v u := fun h'' => h h''.symm
    simp [h, h']

/-- The energy, read with the roles of the two colourings exchanged (`w` is symmetric). -/
private lemma energy_eq_swap {n : ℕ} (G : SimpleGraph (Fin n)) (B B' : Set (Fin n)) :
    energy G B B' = -∑ v, spin B v * field G B' v := by
  have h := sum_spin_mul_nbrDiff_comm G B B'
  have e : ∀ C C' : Set (Fin n), ∑ v, spin C' v * field G C v =
      2 * ∑ v, spin C' v * nbrDiff G C v + ∑ v, spin C' v * spin C v := by
    intro C C'
    simp only [field, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [energy, e, e, h]
  congr 2
  exact Finset.sum_congr rfl fun v _ => mul_comm _ _

/-- The next colour of `v` is the sign of its (doubled) local field. -/
private lemma mem_majorityStep_iff_field_pos {n : ℕ} (G : SimpleGraph (Fin n))
    (B : Set (Fin n)) (v : Fin n) : v ∈ majorityStep G B ↔ 0 < field G B v := by
  unfold field nbrDiff spin
  by_cases hv : v ∈ B <;> simp [majorityStep, hv] <;> omega

/-- The (doubled) local field is odd, hence never `0`. -/
private lemma field_ne_zero {n : ℕ} (G : SimpleGraph (Fin n)) (B : Set (Fin n)) (v : Fin n) :
    field G B v ≠ 0 := by
  unfold field spin
  split_ifs <;> omega

/-- The change of energy over one day:
`E(t + 1) − E(t) = −∑ᵥ (xᵥ(t + 2) − xᵥ(t)) hᵥ(t + 1)`. -/
private lemma energy_sub_energy {n : ℕ} (G : SimpleGraph (Fin n)) (B₀ B₁ B₂ : Set (Fin n)) :
    energy G B₁ B₂ - energy G B₀ B₁ = -∑ v, (spin B₂ v - spin B₀ v) * field G B₁ v := by
  rw [energy_eq_swap G B₀ B₁, energy]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- Each term of the energy change is `≥ 0`, and `≥ 2` at a vertex whose colour on day `t + 2`
differs from its colour on day `t`, because `xᵥ(t + 2) = sign hᵥ(t + 1)` and `hᵥ(t + 1) ≠ 0`. -/
private lemma term_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (B₀ B₁ : Set (Fin n)) (v : Fin n) :
    0 ≤ (spin (majorityStep G B₁) v - spin B₀ v) * field G B₁ v ∧
      (¬(v ∈ majorityStep G B₁ ↔ v ∈ B₀) →
        2 ≤ (spin (majorityStep G B₁) v - spin B₀ v) * field G B₁ v) := by
  have hpos := mem_majorityStep_iff_field_pos G B₁ v
  have hne := field_ne_zero G B₁ v
  by_cases h2 : v ∈ majorityStep G B₁ <;> by_cases h0 : v ∈ B₀ <;>
    simp only [spin, h2, h0, ite_true, ite_false, iff_true, iff_false, true_iff, false_iff,
      not_true_eq_false, not_false_eq_true, sub_self, zero_mul, le_refl, true_and,
      IsEmpty.forall_iff, forall_const] at hpos ⊢ <;> omega

/-- **Goles–Olivos (1981), Poljak–Sůra (1983).** Majority dynamics on a finite graph becomes
periodic with period at most `2`: from some day on, the Blue set on day `t + 2` equals that on
day `t`. -/
theorem blueAfter_eventually_period_two {n : ℕ} (G : SimpleGraph (Fin n)) (B₀ : Set (Fin n)) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, blueAfter G B₀ (t + 2) = blueAfter G B₀ t := by
  -- The energy of days `t` and `t + 1`.
  set E : ℕ → ℤ := fun t => energy G (blueAfter G B₀ t) (blueAfter G B₀ (t + 1)) with hE
  -- It does not increase, and it drops when the colourings of days `t` and `t + 2` differ.
  have hstep : ∀ t, E (t + 1) ≤ E t ∧
      (blueAfter G B₀ (t + 2) ≠ blueAfter G B₀ t → E (t + 1) < E t) := by
    intro t
    have hB2 : blueAfter G B₀ (t + 2) = majorityStep G (blueAfter G B₀ (t + 1)) :=
      blueAfter_succ G B₀ (t + 1)
    have hdiff := energy_sub_energy G (blueAfter G B₀ t) (blueAfter G B₀ (t + 1))
      (blueAfter G B₀ (t + 2))
    have hterm := fun v => term_nonneg G (blueAfter G B₀ t) (blueAfter G B₀ (t + 1)) v
    rw [← hB2] at hterm
    have hsum : 0 ≤ ∑ v, (spin (blueAfter G B₀ (t + 2)) v - spin (blueAfter G B₀ t) v) *
        field G (blueAfter G B₀ (t + 1)) v :=
      Finset.sum_nonneg fun v _ => (hterm v).1
    refine ⟨?_, fun hne => ?_⟩
    · simp only [hE]
      linarith
    · obtain ⟨v, hv⟩ : ∃ v, ¬(v ∈ blueAfter G B₀ (t + 2) ↔ v ∈ blueAfter G B₀ t) :=
        not_forall.mp fun hall => hne (Set.ext hall)
      have h2 := (hterm v).2 hv
      have hle := Finset.single_le_sum (fun v _ => (hterm v).1) (Finset.mem_univ v)
      simp only [hE]
      linarith
  have hanti : Antitone E := antitone_nat_of_succ_le fun t => (hstep t).1
  -- The energy takes finitely many values, so it has a least value, reached on some day `t₀`.
  obtain ⟨b, hb⟩ : BddBelow (Set.range fun p : Set (Fin n) × Set (Fin n) => energy G p.1 p.2) :=
    (Set.finite_range _).bddBelow
  obtain ⟨m, ⟨t₀, ht₀⟩, hmin⟩ := Int.exists_least_of_bdd (P := fun z => ∃ t, E t = z)
    ⟨b, fun z ⟨t, ht⟩ => ht ▸ hb ⟨(blueAfter G B₀ t, blueAfter G B₀ (t + 1)), rfl⟩⟩ ⟨E 0, 0, rfl⟩
  -- From day `t₀` on the energy is constant, so the colourings of days `t` and `t + 2` agree.
  refine ⟨t₀, fun t ht => ?_⟩
  by_contra hne
  have h1 := (hstep t).2 hne
  have h2 : E t ≤ E t₀ := hanti ht
  have h3 : m ≤ E (t + 1) := hmin _ ⟨t + 1, rfl⟩
  omega

end PowerOfFew

end
