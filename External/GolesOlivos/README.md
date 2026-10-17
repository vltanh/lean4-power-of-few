# Period at most two (proved)

**Sources.** E. Goles, J. Olivos, *Comportement périodique des fonctions à seuil binaires et
applications*, Discrete Applied Mathematics 3 (1981) 93–105; S. Poljak, M. Sůra, *On periodical
behaviour in societies with symmetric influences*, Combinatorica 3 (1983) 119–121: a network of
binary threshold units with symmetric weights, updated synchronously, is eventually periodic with
period 1 or 2. The sparse paper cites both in the proof of its Theorem 3.1, for majority dynamics.

**In the formalization.** [`GolesOlivos.lean`](GolesOlivos.lean) states and proves the theorem in
the sources' terms: `External.GolesOlivos.step w b` is one synchronous step of the threshold network
with weights `w` and thresholds `b` (unit `i` is on next iff `∑ⱼ wᵢⱼ xⱼ ≥ bᵢ`), and
`External.GolesOlivos.eventually_period_two` says that for symmetric `w` every orbit satisfies
`x(t + 2) = x(t)` from some step on. The proof is Goles and Olivos's Lyapunov function. The sources
could not be opened, so the theorem is named after its content, not after their numbering.

**Bridge.** The papers' majority rule, with ties kept, is the threshold network with weights
`w_{vu} = 2 [u ∼ v] + [u = v]` and thresholds `b_v = deg v + 1`;
`PowerOfFew.blueAfter_eventually_period_two` (`PowerOfFew/Model/Majority.lean`) proves this and
derives the papers' form.
