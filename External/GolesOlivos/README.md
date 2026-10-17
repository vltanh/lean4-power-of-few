# Period at most two (proved)

**Sources.** E. Goles, J. Olivos, *Comportement périodique des fonctions à seuil binaires et
applications*, Discrete Applied Mathematics 3 (1981) 93–105; S. Poljak, M. Sůra, *On periodical
behaviour in societies with symmetric influences*, Combinatorica 3 (1983) 119–121. The sparse paper
cites both in the proof of its Theorem 3.1: majority dynamics on a finite graph becomes periodic
with period 1 or 2.

**In the formalization.** `PowerOfFew.blueAfter_eventually_period_two` (`GolesOlivos.lean`), for the
tie-keeping majority rule of the papers, which is a symmetric threshold network with a small
positive self-weight. The proof uses the classical Lyapunov function of Goles and Olivos.
