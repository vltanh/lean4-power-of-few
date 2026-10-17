module

public import PowerOfFew.Defs

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
  sorry

open Classical in
/-- A vertex is Red the next day iff its Blue neighbours are fewer than its Red neighbours, plus
one if it is Red today (dense paper, equation (2.1): `v ∈ R₁ ⟺ d_{R₀}(v) > d_{B₀}(v) − I₀(v)`). -/
theorem notMem_majorityStep_iff (B : Set (Fin n)) (v : Fin n) :
    v ∉ majorityStep G B ↔
      (nbrCount G B v : ℤ) < nbrCount G Bᶜ v + (if v ∈ B then 0 else 1) := by
  sorry

theorem majorityStep_mono {B B' : Set (Fin n)} (h : B ⊆ B') :
    majorityStep G B ⊆ majorityStep G B' := by
  sorry

@[simp] theorem majorityStep_empty : majorityStep G ∅ = ∅ := by
  sorry

@[simp] theorem majorityStep_univ : majorityStep G Set.univ = Set.univ := by
  sorry

@[simp] theorem blueAfter_zero (B₀ : Set (Fin n)) : blueAfter G B₀ 0 = B₀ := rfl

theorem blueAfter_succ (B₀ : Set (Fin n)) (t : ℕ) :
    blueAfter G B₀ (t + 1) = majorityStep G (blueAfter G B₀ t) := by
  sorry

theorem blueAfter_add (B₀ : Set (Fin n)) (s t : ℕ) :
    blueAfter G B₀ (s + t) = blueAfter G (blueAfter G B₀ s) t := by
  sorry

theorem blueAfter_mono {B B' : Set (Fin n)} (h : B ⊆ B') (t : ℕ) :
    blueAfter G B t ⊆ blueAfter G B' t := by
  sorry

theorem blueAfter_eq_empty_of_le {B₀ : Set (Fin n)} {s t : ℕ} (h : blueAfter G B₀ s = ∅)
    (hst : s ≤ t) : blueAfter G B₀ t = ∅ := by
  sorry

theorem blueAfter_eq_univ_of_le {B₀ : Set (Fin n)} {s t : ℕ} (h : blueAfter G B₀ s = Set.univ)
    (hst : s ≤ t) : blueAfter G B₀ t = Set.univ := by
  sorry

/-- If every degree exceeds `2m`, every Blue set of at most `m` vertices vanishes the next day. -/
theorem majorityStep_eq_empty_of_lt_degree {m : ℝ} (hdeg : ∀ v, 2 * m < degree G v)
    {B : Set (Fin n)} (hB : (B.ncard : ℝ) ≤ m) : majorityStep G B = ∅ := by
  sorry

/-- Shrinking is monotone in the source bound and the target bound. -/
theorem Shrinks.mono {m₁ m₂ m₁' m₂' : ℝ} (h : Shrinks G m₁ m₂) (h₁ : m₁' ≤ m₁) (h₂ : m₂ ≤ m₂') :
    Shrinks G m₁' m₂' := by
  sorry

end PowerOfFew

end
