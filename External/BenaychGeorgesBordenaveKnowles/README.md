# Benaych-Georges, Bordenave and Knowles, Theorem 3.2 (stated, not assumed)

**Source.** F. Benaych-Georges, C. Bordenave, A. Knowles, *Spectral radii of sparse random
matrices*, Ann. Inst. H. Poincaré Probab. Statist. 56 (2020), arXiv:1704.02945, Theorem 3.2 (the
inhomogeneous Erdős–Rényi graph): with `d = maxᵢ ∑ⱼ pᵢⱼ`, `κ = maxᵢⱼ pᵢⱼ / (d/n)`,
`q = √d ∧ n^(1/10) κ^(−1/9)` and `η = √(log n)/q`, if `q ≥ 1` then
`E‖A − E A‖ / √d ≤ 2 + C η / √(1 ∨ log η)` for a universal constant `C`.

**How the paper uses it.** The sparse paper's proof of Lemma A.7 takes the expectation bound
`E‖A − E A‖ = O(√(pn))` from it, quoted with `d = p(1 − p)(n − 1)` and
`η = √(log n)/min{√d, n^0.1}`; the difference only changes constants (REPORT.md, E26).

**In the formalization.** [`Theorem3_2.lean`](Theorem3_2.lean):
`External.BenaychGeorgesBordenaveKnowles.theorem3_2`, the homogeneous case `pᵢⱼ = p` (`i ≠ j`):
`d = p(n − 1)`, `κ = n/(n − 1)`, with Mathlib's binomial random graph and adjacency matrix. It is a
hypothesis only of `PowerOfFew.Sparse.lemmaA_7_of_bbk_blm`, the formalized derivation of Lemma A.7
from this theorem and from Theorem 6.10 of Boucheron, Lugosi and Massart
([`../BoucheronLugosiMassart/`](../BoucheronLugosiMassart/README.md)). The library proves Lemma
A.7 itself by Feige and Ofek's argument ([`../FeigeOfek/`](../FeigeOfek/README.md)), so no result
of the library assumes this theorem.

**What Lean lacks.** Mathlib has the operator norm of matrices but no moment method for random
matrices: the proof estimates `E tr Bˡ B*ˡ` for the non-backtracking matrix `B` and uses an
Ihara–Bass type formula.
