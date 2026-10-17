# Boucheron, Lugosi and Massart, Theorem 6.10 (stated, not assumed)

**Source.** S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities: A Nonasymptotic
Theory of Independence*, Oxford University Press (2013), Theorem 6.10 (first proved by Talagrand):
for independent `X₁, …, X_N` with values in `[0, 1]` and `f : [0, 1]^N → ℝ` separately convex with
`|f(x) − f(y)| ≤ ‖x − y‖`, `Z = f(X)` satisfies `P{Z > E Z + t} ≤ e^(−t²/2)` for `t > 0`.

**How the paper uses it.** The sparse paper's proof of Lemma A.7 applies it to
`2^(−1/2) ‖Z − E A‖_op` as a function of the upper-triangular entries, which gives `e^(−t²/4)` for
`‖A − E A‖_op`.

**In the formalization.** [`Theorem6_10.lean`](Theorem6_10.lean):
`External.BoucheronLugosiMassart.theorem6_10`, stated for real random variables on a probability
space in `Type`. It is a hypothesis only of `PowerOfFew.Sparse.lemmaA_7_of_bbk_blm`, the formalized
derivation of Lemma A.7 (see [`../BenaychGeorgesBordenaveKnowles/`](../BenaychGeorgesBordenaveKnowles/README.md));
no result of the library assumes it.

**What Lean lacks.** Talagrand's inequality: its proofs use the entropy method and logarithmic
Sobolev inequalities, which Mathlib does not have.
