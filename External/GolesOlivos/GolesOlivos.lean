module

public import Mathlib

/-!
# Symmetric threshold networks are eventually periodic with period at most two

E. Goles and J. Olivos, *Comportement périodique des fonctions à seuil binaires et applications*,
Discrete Applied Mathematics 3 (1981) 93–105; S. Poljak and M. Sůra, *On periodical behaviour in
societies with symmetric influences*, Combinatorica 3 (1983) 119–121: in a network of binary
threshold units with symmetric weights, updated synchronously, every orbit is eventually periodic
with period 1 or 2.

The proof is Goles and Olivos's Lyapunov function `E(t) = −∑ᵢⱼ wᵢⱼ xᵢ(t + 1) xⱼ(t) + ∑ᵢ bᵢ (xᵢ(t + 1) +
xᵢ(t))`, after lowering each threshold below the next attainable value of its field, which changes
no step and makes no field equal to its threshold: `E` does not increase, and it drops strictly on
each step `t` with `x(t + 2) ≠ x(t)`; since it takes finitely many values, `x(t + 2) = x(t)` from some
step on.
-/

@[expose] public section

noncomputable section

namespace External.GolesOlivos

/-- One synchronous step of the threshold network with weights `w` and thresholds `b` on the finite
set `ι`: unit `i` is on at the next step iff `∑ⱼ wᵢⱼ xⱼ ≥ bᵢ`, where `xⱼ ∈ {0, 1}` is the current
state of unit `j`. -/
def step {ι : Type*} [Fintype ι] (w : ι → ι → ℝ) (b : ι → ℝ) (x : ι → Bool) : ι → Bool :=
  fun i => decide (b i ≤ ∑ j, w i j * (if x j then 1 else 0))

/-! ### The Lyapunov function -/

section Lyapunov

variable {ι : Type*} [Fintype ι] (w : ι → ι → ℝ)

/-- The state `xᵢ ∈ {0, 1}` of unit `i`, as a real number. -/
private def goAux_val (x : ι → Bool) (i : ι) : ℝ := if x i then 1 else 0

/-- The field `∑ⱼ wᵢⱼ xⱼ` of unit `i` in the state `x`. -/
private def goAux_field (x : ι → Bool) (i : ι) : ℝ := ∑ j, w i j * goAux_val x j

/-- The Goles–Olivos energy of the consecutive states `x` and `x'`, with the thresholds `c`:
`E(x, x') = −∑ᵢⱼ wᵢⱼ x'ᵢ xⱼ + ∑ᵢ cᵢ (x'ᵢ + xᵢ)`. -/
private def goAux_energy (c : ι → ℝ) (x x' : ι → Bool) : ℝ :=
  -∑ i, goAux_val x' i * goAux_field w x i + ∑ i, c i * (goAux_val x' i + goAux_val x i)

/-- Lowering the thresholds. The field of unit `i` takes finitely many values, so `b i` can be
lowered to some `c i` above every attainable field below `b i`: the step is unchanged (a field is
`≥ b i` iff it is `> c i`), and no field equals `c i`. -/
private theorem goAux_lower (b : ι → ℝ) :
    ∃ c : ι → ℝ, ∀ (x : ι → Bool) (i : ι),
      (b i ≤ goAux_field w x i ↔ c i < goAux_field w x i) ∧ goAux_field w x i ≠ c i := by
  classical
  have key : ∀ i, ∃ c : ℝ, ∀ x : ι → Bool,
      (b i ≤ goAux_field w x i ↔ c < goAux_field w x i) ∧ goAux_field w x i ≠ c := by
    intro i
    -- The attainable fields below `b i`, together with `b i - 1`; their largest is `< b i`.
    let s : Finset ℝ :=
      insert (b i - 1) ((Finset.univ.image fun x : ι → Bool => goAux_field w x i).filter (· < b i))
    have hne : s.Nonempty := Finset.insert_nonempty _ _
    have hlt : s.max' hne < b i := by
      have hmem : s.max' hne ∈ s := s.max'_mem hne
      rcases Finset.mem_insert.mp hmem with h | h
      · rw [h]
        linarith
      · exact (Finset.mem_filter.mp h).2
    refine ⟨(s.max' hne + b i) / 2, fun x => ?_⟩
    by_cases h : b i ≤ goAux_field w x i
    · exact ⟨iff_of_true h (by linarith), (show (s.max' hne + b i) / 2 < goAux_field w x i by
        linarith).ne'⟩
    · have hle : goAux_field w x i ≤ s.max' hne :=
        s.le_max' _ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
          ⟨Finset.mem_image_of_mem _ (Finset.mem_univ x), lt_of_not_ge h⟩))
      exact ⟨iff_of_false h (not_lt.mpr (by linarith)),
        (show goAux_field w x i < (s.max' hne + b i) / 2 by linarith).ne⟩
  choose c hc using key
  exact ⟨c, fun x i => hc i x⟩

/-- The symmetry of the weights: `∑ᵢ x'ᵢ ∑ⱼ wᵢⱼ xⱼ = ∑ᵢ xᵢ ∑ⱼ wᵢⱼ x'ⱼ`. -/
private theorem goAux_sum_swap (hw : ∀ i j, w i j = w j i) (x x' : ι → Bool) :
    ∑ i, goAux_val x' i * goAux_field w x i = ∑ i, goAux_val x i * goAux_field w x' i := by
  simp only [goAux_field, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hw j i]
  ring

/-- The change of energy over one step:
`E(x(t + 1), x(t + 2)) − E(x(t), x(t + 1)) = −∑ᵢ (xᵢ(t + 2) − xᵢ(t)) (∑ⱼ wᵢⱼ xⱼ(t + 1) − cᵢ)`. -/
private theorem goAux_energy_sub (hw : ∀ i j, w i j = w j i) (c : ι → ℝ) (x₀ x₁ x₂ : ι → Bool) :
    goAux_energy w c x₁ x₂ - goAux_energy w c x₀ x₁ =
      -∑ i, (goAux_val x₂ i - goAux_val x₀ i) * (goAux_field w x₁ i - c i) := by
  have h₀ : goAux_energy w c x₀ x₁ = ∑ i, (c i * (goAux_val x₁ i + goAux_val x₀ i) -
      goAux_val x₀ i * goAux_field w x₁ i) := by
    rw [goAux_energy, goAux_sum_swap w hw x₀ x₁, Finset.sum_sub_distrib]
    ring
  have h₁ : goAux_energy w c x₁ x₂ = ∑ i, (c i * (goAux_val x₂ i + goAux_val x₁ i) -
      goAux_val x₂ i * goAux_field w x₁ i) := by
    rw [goAux_energy, Finset.sum_sub_distrib]
    ring
  rw [h₀, h₁, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Each term of the energy change is `≥ 0`, and `> 0` at a unit whose state at step `t + 2`
differs from its state at step `t`: `xᵢ(t + 2) = 1` iff the field `∑ⱼ wᵢⱼ xⱼ(t + 1)` exceeds `cᵢ`,
and it never equals `cᵢ`. -/
private theorem goAux_term (b c : ι → ℝ)
    (hc : ∀ (x : ι → Bool) (i : ι),
      (b i ≤ goAux_field w x i ↔ c i < goAux_field w x i) ∧ goAux_field w x i ≠ c i)
    (x₀ x₁ : ι → Bool) (i : ι) :
    0 ≤ (goAux_val (step w b x₁) i - goAux_val x₀ i) * (goAux_field w x₁ i - c i) ∧
      (step w b x₁ i ≠ x₀ i →
        0 < (goAux_val (step w b x₁) i - goAux_val x₀ i) * (goAux_field w x₁ i - c i)) := by
  obtain ⟨hiff, hne⟩ := hc x₁ i
  have hstep : step w b x₁ i = decide (c i < goAux_field w x₁ i) :=
    decide_eq_decide.mpr hiff
  have hval : goAux_val (step w b x₁) i = if c i < goAux_field w x₁ i then 1 else 0 := by
    rw [goAux_val, hstep]
    simp
  rw [hval, hstep]
  by_cases h : c i < goAux_field w x₁ i
  · cases hx : x₀ i <;> simp [goAux_val, h, hx, h.le]
  · have hlt : goAux_field w x₁ i < c i := lt_of_le_of_ne (not_lt.mp h) hne
    cases hx : x₀ i <;> simp [goAux_val, h, hx, hlt, hlt.le]

end Lyapunov

/-- **Goles–Olivos (1981), Poljak–Sůra (1983)**: if the weights are symmetric, then from every state
the network is eventually periodic with period at most `2`: `x(t + 2) = x(t)` for all large `t`. -/
theorem eventually_period_two {ι : Type*} [Fintype ι] (w : ι → ι → ℝ) (hw : ∀ i j, w i j = w j i)
    (b : ι → ℝ) (x : ι → Bool) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, (step w b)^[t + 2] x = (step w b)^[t] x := by
  -- Lower the thresholds without changing the step.
  obtain ⟨c, hc⟩ := goAux_lower w b
  -- The energy of the states at steps `t` and `t + 1`.
  let E : ℕ → ℝ := fun t => goAux_energy w c ((step w b)^[t] x) ((step w b)^[t + 1] x)
  -- It does not increase, and it drops when the states at steps `t` and `t + 2` differ.
  have hdec : ∀ t, E (t + 1) ≤ E t ∧
      ((step w b)^[t + 2] x ≠ (step w b)^[t] x → E (t + 1) < E t) := by
    intro t
    have hE : E (t + 1) - E t = -∑ i, (goAux_val ((step w b)^[t + 2] x) i -
        goAux_val ((step w b)^[t] x) i) * (goAux_field w ((step w b)^[t + 1] x) i - c i) :=
      goAux_energy_sub w hw c _ _ _
    have h₂ : (step w b)^[t + 2] x = step w b ((step w b)^[t + 1] x) :=
      Function.iterate_succ_apply' _ _ _
    have hterm := fun i => goAux_term w b c hc ((step w b)^[t] x) ((step w b)^[t + 1] x) i
    rw [← h₂] at hterm
    have hsum : 0 ≤ ∑ i, (goAux_val ((step w b)^[t + 2] x) i -
        goAux_val ((step w b)^[t] x) i) * (goAux_field w ((step w b)^[t + 1] x) i - c i) :=
      Finset.sum_nonneg fun i _ => (hterm i).1
    refine ⟨by linarith, fun hne => ?_⟩
    obtain ⟨i, hi⟩ : ∃ i, (step w b)^[t + 2] x i ≠ (step w b)^[t] x i := by
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    have hpos : 0 < ∑ i, (goAux_val ((step w b)^[t + 2] x) i -
        goAux_val ((step w b)^[t] x) i) * (goAux_field w ((step w b)^[t + 1] x) i - c i) :=
      Finset.sum_pos' (fun i _ => (hterm i).1) ⟨i, Finset.mem_univ i, (hterm i).2 hi⟩
    linarith
  have hanti : Antitone E := antitone_nat_of_succ_le fun t => (hdec t).1
  -- The energy takes finitely many values, so it has a least value, reached at some step `t₀`.
  have hfin : (Set.range E).Finite := by
    refine (Set.finite_range fun p : (ι → Bool) × (ι → Bool) => goAux_energy w c p.1 p.2).subset ?_
    rintro _ ⟨t, rfl⟩
    exact ⟨((step w b)^[t] x, (step w b)^[t + 1] x), rfl⟩
  obtain ⟨_, ⟨t₀, rfl⟩, hmin⟩ := Set.exists_min_image (Set.range E) id hfin ⟨E 0, 0, rfl⟩
  -- From step `t₀` on the energy is constant, so the states at steps `t` and `t + 2` agree.
  refine ⟨t₀, fun t ht => ?_⟩
  by_contra hne
  have h₁ := (hdec t).2 hne
  have h₂ : E t ≤ E t₀ := hanti ht
  have h₃ : E t₀ ≤ E (t + 1) := hmin _ ⟨t + 1, rfl⟩
  linarith

end External.GolesOlivos

end
