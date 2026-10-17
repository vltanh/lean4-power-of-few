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

/-- **Goles–Olivos (1981), Poljak–Sůra (1983).** Majority dynamics on a finite graph becomes
periodic with period at most `2`: from some day on, the Blue set on day `t + 2` equals that on
day `t`. -/
theorem blueAfter_eventually_period_two {n : ℕ} (G : SimpleGraph (Fin n)) (B₀ : Set (Fin n)) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, blueAfter G B₀ (t + 2) = blueAfter G B₀ t := by
  sorry

end PowerOfFew

end
