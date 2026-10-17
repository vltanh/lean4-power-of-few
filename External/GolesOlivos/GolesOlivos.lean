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

/-- **Goles–Olivos (1981), Poljak–Sůra (1983)**: if the weights are symmetric, then from every state
the network is eventually periodic with period at most `2`: `x(t + 2) = x(t)` for all large `t`. -/
theorem eventually_period_two {ι : Type*} [Fintype ι] (w : ι → ι → ℝ) (hw : ∀ i j, w i j = w j i)
    (b : ι → ℝ) (x : ι → Bool) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, (step w b)^[t + 2] x = (step w b)^[t] x := by
  sorry

end External.GolesOlivos

end
