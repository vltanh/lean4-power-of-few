# Audit of the papers and the formalization

Papers:

- **Dense paper.** Linh Tran and Van Vu, *Reaching a consensus on random networks: the power of
  few*, Theory of Computing 19 (2023), article 6 (arXiv:1911.10279). The audit was made against the
  LaTeX source of the journal version, which differs from arXiv v2 in its main theorems
  (Section 10, "Versions"). Line numbers `D:n` refer to that source.
- **Sparse paper.** BaoLinh Tran and Van Vu, *The "Power of Few" phenomenon: the sparse case*,
  arXiv:2302.05605v2, the accepted manuscript of Random Structures & Algorithms 66 (2025) e21260
  (whether it matches the typeset text was not checked). The audit was made against the LaTeX source
  of arXiv v2. Line numbers `S:n` refer to that source.

Section, result and equation numbers are the papers'. "Red wins" means that Blue is empty on some
day.

Status of the formalization:

- **Everything the papers prove is proved**, by the papers' own arguments: in the dense paper,
  Theorems 1.2, 1.3 and 1.6, Lemma 2.1 with Claims 2.5 and 2.6, Lemmas 2.3, 2.4, 3.2–3.6 and
  Appendix A; in the sparse paper, Theorems 1.2, 1.4, 1.5, 1.7, 3.1 and 4.1, Lemma 2.1, Proposition
  2.2, Lemmas 2.3–2.6, Propositions 4.2–4.4, Corollary A.2 and Lemmas A.3–A.7. The dense Theorem 1.5,
  which its paper states without proof, is derived from the sparse Theorem 1.2. The cited results
  that the proofs use are proved too (Section 2), except three.
- **The formalization is conditional** on three cited results, assumed as hypotheses named after
  their sources and written in the signature of every theorem that uses them: the Berry–Esseen
  inequality with Shevtsova's constant `0.56` ([`ShevtsovaBerryEsseen`](Challenge.lean#L207)), Theorem 3.2 of
  Benaych-Georges–Bordenave–Knowles on the spectral norm of sparse random matrices
  ([`BBKTheorem3_2`](Challenge.lean#L228)), and Theorem 6.10 of Boucheron–Lugosi–Massart, Talagrand's concentration
  inequality for separately convex Lipschitz functions ([`BLMTheorem6_10`](Challenge.lean#L244)). Lean has none of them
  (Section 2).
- **Three printed theorems are false**: the sparse paper's Theorem 1.5 (biased random colourings)
  and Theorems 1.7 and 4.1 (random activations and updates). The formalization proves that they are
  false ([`theorem1_5_printed_false`](PowerOfFew/Sparse/RandomColoring.lean#L644), [`theorem1_7_printed_false`](PowerOfFew/Sparse/ActivationCounterexample.lean#L882), [`theorem4_1_printed_false`](PowerOfFew/Sparse/ActivationCounterexample.lean#L898) and
  per-sequence forms; these use none of the assumed results) and proves corrected versions, agreed
  with the user (E13, E14). Other statements are formalized as printed, up to the readings and
  deviations of Section 6.
- **Build.** `lake build` succeeds; the only `sorry`s are the 13 statements of record in
  [`Challenge.lean`](Challenge.lean); there is no `axiom`. [`scripts/Audit.lean`](scripts/Audit.lean) checks every declaration of the
  library: all use only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). Palomar's Comparator
  (`lake env lake comparator --config=comparator.json`) accepts [`Solution.lean`](Solution.lean) against
  [`Challenge.lean`](Challenge.lean) under the Lean and NanoDa kernels.
- **Proofs.** Every proof follows its paper's argument. Nineteen results depart from it at one or
  more steps (eighteen departures), each to repair a step that is wrong or has a gap; none replaces a
  whole argument (Section 7). The route check ([`scripts/route_check.py`](scripts/route_check.py)) confirms that every proof uses
  the results that its paper's proof cites, with four recorded differences: one is departure 8, the
  other three are not departures (Section 8). Independent readers compared every formal proof with
  the TeX source.

## 1. Summary

- **Errors.** Three statements of the sparse paper are false: Theorem 1.5 needs a bias
  ω(n^(−1/2)), not only ω((pn)⁻¹) (E13); Theorems 1.7 and 4.1 need an initial gap
  Δ ≳ √(n/p_ac) for the first day, which their proof assumes and their statements omit, so the power
  of few is not robust under random activations, contrary to the abstract (E14; B. Tran's 2025
  thesis restates both theorems unchanged). In
  the dense paper, the proof of Theorem 1.2 computes P₁ ≤ 0.0902 where the true value at n = 1000 is
  0.0962 (the theorem holds: the total failure probability stays below 0.1, E4), the proof of
  Theorem 1.3 has the factor 4 where its own chain gives 8 (E5), and Lemma 3.5 states a bound that its
  proof gives only for n ≥ 1288 (E2). In the sparse paper, the variance bound 7n/12 of Proposition
  2.2 does not follow from its argument for p ≠ 1/2 (E15), and the definition of the hypothetical
  colouring in Section 4 is inconsistent with its use (E21). All other results hold, some only in
  the form their proofs give (Section 6).
- **Gaps.** The deduction of the dense Theorem 1.5 and the sparse Theorems 1.4 and 1.5 from the sparse
  Theorem 1.2 misses the case p > 1 − 10/n (E1); several "n large", "routine" or implicit steps
  needed an argument (E3, E5, E7–E10, E12, E16–E20, E22–E26). All are repaired along the papers'
  lines.
- **Missing hypotheses.** The corrected sparse Theorems 1.5, 1.7 and 4.1 (Section 4).
- **Redundant hypotheses.** Six hypotheses are not needed (Section 5).
- **Use of cited results.** The sparse paper quotes its own Lemma A.3 with a bound too small by the
  factor `2(1 − 2σ²)`, which leaves the variance bound `7n/12` unproved for `p ≠ 1/2` (E15). The other
  misuses do not affect the results: it applies Lemma A.3 outside its hypotheses (E15), quotes Lemma
  2.6 for what is the first half of its proof (E23), applies Lemma A.4 to the active subgraph without
  the concentration step it needs (E24), and quotes Theorem 3.2 of Benaych-Georges–Bordenave–Knowles
  with a different normalization (E26). All other cited results are used correctly.

## 2. Results from prior work and how the papers use them

### Proved

| Result | Where the papers use it | Source | Theorem in the formalization |
| --- | --- | --- | --- |
| Hoeffding's inequality | dense Theorem 3.1, in Lemmas 3.3 and 3.4 | W. Hoeffding, *J. Amer. Statist. Assoc.* 58 (1963) | [`ProbabilityTheory.measureReal_sum_ge_add_le_exp`](Basic/Probability/Concentration.lean#L60), [`ProbabilityTheory.measureReal_sum_le_sub_le_exp`](Basic/Probability/Concentration.lean#L99) ([`Basic/Probability/Concentration.lean`](Basic/Probability/Concentration.lean), from Mathlib's sub-Gaussian Hoeffding bound) |
| Chernoff's bounds | sparse paper, equations (29), (30), Lemmas A.4–A.6, Propositions 4.2–4.4 | standard | [`ProbabilityTheory.IsBernoulliFamily.measureReal_sum_le_le_exp_klBern`](Basic/Probability/Chernoff.lean#L191), [`ProbabilityTheory.IsBernoulliFamily.measureReal_sum_ge_le_exp`](Basic/Probability/Chernoff.lean#L258), [`ProbabilityTheory.IsBernoulliFamily.measureReal_sum_le_le_exp`](Basic/Probability/Chernoff.lean#L297) ([`Basic/Probability/Chernoff.lean`](Basic/Probability/Chernoff.lean)) |
| `C(2m, m) < 4^m/√(2m)` | dense Lemma 3.2 | J. Matoušek, J. Nešetřil, *Invitation to Discrete Mathematics*, Proposition 2.6.2 | [`Nat.centralBinom_lt_four_pow_div_sqrt`](Basic/Combinatorics/Choose.lean#L68) ([`Basic/Combinatorics/Choose.lean`](Basic/Combinatorics/Choose.lean)), by the book's product argument |
| `C(n, k) ≤ e^(n H(k/n))` | sparse Lemmas 2.3 and A.5 ("a routine Stirling bound", S:1081; S:1765) | standard | [`Nat.choose_le_exp_mul_binEntropy`](Basic/Combinatorics/Choose.lean#L169), from Stirling's bounds |
| Eventual period two of majority dynamics | sparse Theorem 3.1 | E. Goles, J. Olivos, *Discrete Appl. Math.* 3 (1981); S. Poljak, M. Sůra, *Combinatorica* 3 (1983) | [`PowerOfFew.blueAfter_eventually_period_two`](PowerOfFew/External/GolesOlivos/GolesOlivos.lean#L127) (`External/GolesOlivos/`), by the energy argument |

### Assumed (the formalization is conditional on these)

| Result | Where the papers use it | Source | Hypothesis | What Lean lacks |
| --- | --- | --- | --- | --- |
| Berry–Esseen inequality with constant 0.56, for independent, not necessarily identically distributed summands | dense Theorem 2.2 (Lemmas 2.3, 2.4, Claims 2.5, 2.6, Appendix A); sparse Theorem A.1 (Corollary A.2, Lemma A.3, Proposition 2.2, Theorem 1.4) | I. G. Shevtsova, *Doklady Math.* 82 (2010) 862–864 | [`ShevtsovaBerryEsseen`](Challenge.lean#L207) | Mathlib has the central limit theorem but no Berry–Esseen bound; the constant 0.56 rests on computer-assisted estimates of characteristic functions |
| `E‖A − EA‖/√d ≤ 2 + Cη/√(1 ∨ log η)` for `G(n, p)` | sparse Lemma A.7 | F. Benaych-Georges, C. Bordenave, A. Knowles, *Ann. IHP Probab. Stat.* 56 (2020), Theorem 3.2 | [`BBKTheorem3_2`](Challenge.lean#L228) | spectral norms of random matrices (moment method, non-backtracking matrices) |
| `P{Z > EZ + t} ≤ e^(−t²/2)` for separately convex 1-Lipschitz functions of independent `[0, 1]`-valued variables | sparse Lemma A.7 | S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities* (2013), Theorem 6.10 (Talagrand; Ledoux's proof) | [`BLMTheorem6_10`](Challenge.lean#L244) | Talagrand's inequality and the entropy method |

Each hypothesis was checked against its source: none is stronger than what the source proves
(`PowerOfFew/External/*/README.md`). In particular, the Berry–Esseen hypothesis allows summands
that are not identically distributed, which the papers need (Section 2, last table), and Shevtsova's
constant for that case is 0.5583 ≤ 0.56. The hypotheses are propositions, not classes or structures,
and a reader of each theorem sees exactly the ones it uses. They cannot be instantiated in the project
without proving the cited results, which is why they are assumed. The last two could be replaced by
the Feige–Ofek bound `‖A − EA‖ = O(√(pn))` with high probability, a large but elementary proof
(Section 11).

### Standard facts used without citation

| Fact | Where | In the formalization |
| --- | --- | --- |
| Chebyshev's inequality | dense Lemma 2.1; sparse Lemma 2.1, Proposition 4.2 | [`ProbabilityTheory.measureReal_ge_le_variance_div_sq`](Basic/Probability/Concentration.lean#L43) and its lower-tail twin, from Mathlib's `meas_ge_le_variance_div_sq` |
| Markov's inequality, union bound | everywhere | Mathlib (`mul_meas_ge_le_integral_of_nonneg`, `measureReal_biUnion_finset_le`) |
| Properties of `Φ`: monotone, `Φ₀` concave on `[0, ∞)`, `Φ₀(x)/x` decreasing | dense Theorems 1.2, 1.3; sparse Proposition 2.2 | [`PowerOfFew/Model/Normal.lean`](PowerOfFew/Model/Normal.lean); [`PowerOfFew.Φ_eq_cdf_gaussianReal`](PowerOfFew/Model/Normal.lean#L39) identifies `Φ` with Mathlib's Gaussian law |
| Independence of the edges of `G(n, p)`, conditioning on one edge | dense Claim 2.6; sparse Proposition 2.2 | [`PowerOfFew/Model/Gnp.lean`](PowerOfFew/Model/Gnp.lean), [`PowerOfFew/Model/EdgeConditioning.lean`](PowerOfFew/Model/EdgeConditioning.lean) |
| The subgraph of `G(n, p)` induced on `m` vertices is `G(m, p)`; the days' coins are independent | sparse Section 4 | [`PowerOfFew/Model/Lazy.lean`](PowerOfFew/Model/Lazy.lean) |
| Operator norm, Cauchy–Schwarz | sparse Lemma 2.5 | Mathlib |

### Does each paper use its cited results correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Berry–Esseen (Shevtsova) | dense Section 2; sparse Appendix A | correct. Both papers state it without "independent" (E27) and apply it to independent summands. The summands `±(Ber(p) − p)` are not identically distributed unless `p = 1/2`, so the general constant is needed, and 0.56 is valid. |
| Hoeffding | dense Lemmas 3.3, 3.4 | correct; display (3.2) drops the factor 2, which the next display uses (E8) |
| Chernoff | sparse paper | correct |
| Matoušek–Nešetřil | dense Lemma 3.2 | correct |
| Goles–Olivos, Poljak–Sůra | sparse Theorem 3.1 | correct |
| Benaych-Georges–Bordenave–Knowles, Theorem 3.2 | sparse Lemma A.7 | applied loosely but correctly: quoted with `d = p(1 − p)(n − 1)` (the theorem has `d = p(n − 1)`), with a bound on `η` that ignores one branch of `q`, and without the case `q < 1` (E26); its conclusion `E‖A − EA‖ = O(√(pn))` is what the paper uses, and it holds |
| Boucheron–Lugosi–Massart, Theorem 6.10 | sparse Lemma A.7 | correct |
| Stirling's bound | sparse Lemmas 2.3, A.5 | correct |

Cited only for context, not in proofs: Mossel–Neeman–Tamuz, Mossel–Tamuz, Benjamini–Chan–O'Donnell–
Tamuz–Tan, Fountoulakis–Kang–Makai (the dense paper's Theorem 1.4, which the papers re-derive in
delayed form), Berkowitz–Devlin, Sah–Sawhney, Chakraborti–Kim–Lee–Tran, Zehmakan.

## 3. Errors and gaps in the papers

### The dense paper (Theory of Computing 2023)

**E1. Theorem 1.5 (D:442–447), and the sparse Theorems 1.4 and 1.5.** The dense paper states
Theorem 1.5 without proof, as a consequence of the sparse paper. That deduction, and the sparse
paper's proofs of its Theorems 1.4 and 1.5 (S:342–351, S:389–394), apply the sparse Theorem 1.2,
which assumes `pn ≤ n − 10`; the case `p > 1 − 10/n` is not treated. Gap; the dense Theorem 1.5 and the
sparse Theorem 1.4 hold, and so does the corrected sparse Theorem 1.5 (E13). The
formalization proves the near-complete case separately: if Red leads by `m > 1` vertices on
`G(n, p)` with `pn > n − 10`, Red is unanimous after two days with probability at least
`1 − 40/(m − 1) − 2048/n` ([`colorAux_nearComplete`](PowerOfFew/Sparse/ColoringAux.lean#L465)). One day does not suffice: at `p = 1 − 9/n` the
number of non-neighbours of a vertex is about Poisson(9). (Departure 13; the dense Theorem 1.5 has no
proof in its paper, and its formal proof uses the same two-day argument.)

**E2. Theorem 1.6, the bound P₂, and Lemma 3.5 (D:498, D:1297, D:1320).** Theorem 1.6 prints
`P₂(n) = n⁻¹ exp(−(.076n − 1.38√n))`; the proof of Lemma 3.5 computes `.076n − 1.83√n`
(`12.8/7 = 1.8286`), so 1.38 is a transposition. Lemma 3.5 states `1 − n⁻¹ exp(−.025n)`, which its
proof gives only when `.025n ≤ .076n − 1.83√n`, that is for `n ≥ 1288`: the statement claims more
than the proof gives. The results hold with `P₂(n) = n⁻¹ exp(−(.076n − 1.83√n))`; Theorem 1.2 is
unaffected (`P₂(1000) ≈ 1.3 · 10⁻¹¹`). The formalization uses the coefficient 1.83 ([`denseP2`](Challenge.lean#L179)) and
proves the printed `.025n` form for `n ≥ 1288` ([`lemma3_5_printed`](PowerOfFew/Dense/Shrinking.lean#L650)).

**E3. Theorem 1.6, Parts 2–4 (D:496–509).** The parts are written as conditional probabilities,
for example `P(|B₂| ≤ .4n | |B₁| ≤ n/2 − .8√n/p) ≥ 1 − P₂`, but Lemmas 3.5, 3.6 and 3.3, which the
paper calls Parts 2, 3 and 4, prove that with probability at least `1 − Pₜ` the graph shrinks every
Blue set below the threshold. Read literally, the conditional bounds do not follow; the final bound
`1 − (P₁ + P₂ + P₃ + P₄)` does. Gap in the statement; the formalization states Parts 2–4 as the
lemmas prove them (Section 6).

**E4. Theorem 1.2, proof (D:556–558).** "A routine calculation shows P₁ ≤ .0902": at `n = 1000`,
`P₁(1000, 1/2, 5) = .09624` (`F = 2.10145`), and `P₁ > .0902` exactly for `1000 ≤ n ≤ 4979`. The
total failure probability is below `.0963 + 10⁻¹⁰ < .1`, so Theorem 1.2 holds; the monotonicity of
`P₁` in `n`, which the calculation needs, is immediate but not argued. Error, harmless. The
formalization shows `P₁ ≤ .0965` (departure 1).

**E5. Theorem 1.3, proof (D:588–620).** The proof takes `n` and `cₙ` "both sufficiently large",
which the claimed `K(p) = 4Φ₀(2√p)⁻² + 1` does not cover; its displayed chain gives
`2/(mφ/2)² = 8φ⁻² m⁻²` (`φ = Φ₀(2√p)`, `m = min{√n, cₙ}`), not `4φ⁻² m⁻²`; and the `+1` absorbs
`P₂ + P₃ + P₄` only for `n ≳ 80/p³`, which is not implied even inside the main case (for `p = .1`,
`n = 10⁴`, `cₙ = 100`: `mφ ≈ 23.6 ≥ 2L ≈ 19.3` while `P₃ = n⁻¹ e^14000`). Gap and an error in a
constant; the theorem ("there is `K(p)`") holds. The formalization takes
`K = 8φ⁻² + K′(p) + (2L/φ)²`, with `L = .6(1 − 2p + 2p²)/√(p(1 − p)) + .8/p` and the trivial case
when `mφ < 2L` (departure 2).

**E6. Open questions (D:636–638).** "Plugging in the same values for ε₁ and ε₂ with c = 4" refers to
the arXiv version's Theorem 6, which the journal version replaced. The claim `ρ(.5, 4, n) ≥ .77`
follows from Theorem 1.6 for `n ≥ 1546` (the bound is .764 at `n = 1000`, with limit .7802), which
fits the paper's "for n sufficiently large". Typo.

**E7. Lemma 2.1: Claims 2.5 and 2.6 (D:858–1046).**
- Claim 2.5 writes `F₁(n, p, c) = F(n, p, c) + .8√n/p` (D:858); by the definitions it is
  `F + .8/p`, which the Chebyshev step uses. Its proof writes `|R₀| − |B₀| = 2c` (D:880, D:884); in
  general only `≥ 2c` holds, which suffices because `Φ₀` is increasing. Its step
  `.56/√(n − 1) ≤ .6/√n` needs `n ≥ 7.76`, which `F > 0` implies (`n ≥ 15`).
- Claim 2.6 counts the pairs of vertices of the same colour as if `|B₀| = n/2 − c` (D:1040–1042),
  and bounds `1.2544/(n − 2) ≤ 1.4/n`, which needs `n ≥ 19.23`. Lemma 2.1 still holds: it reduces to
  `|B₀| = ⌊n/2 − c⌋` by the monotonicity of majority dynamics, and for `n ≤ 27` with `F > 0` its
  bound `P₁` is at least 1 (minimum 1.069). Gaps; the formalization repairs them this way
  (departures 3, 4). Typos in the same proofs: E27.

**E8. Lemma 3.4, proof (D:1208–1286).** Display (3.2) omits the factor 2 of Hoeffding's
inequality (as printed it is true but weaker; the next display uses the factor). The double union
bound runs over the Blue sets of exactly `n₀` vertices, while the statement allows at most `n₀`;
smaller sets follow by monotonicity. Typo and gap (departure 5).

**E9. Lemma 3.5, proof (D:1303–1319).** The display at D:1319 drops the square on
`(1.6√n/p − 1)`; the case `n/2 − .8√n/p < 0`, where no Blue set qualifies, is left implicit; and
"Therefore can bound … Equation (3)" (D:1315) points to an unnumbered display. Typos and a trivial
gap (departure 6).

**E10. Lemma 3.6, proof (D:1346–1360).** The step `(n − 2n₂ − 1)² ≥ (.2n − 1)²` needs
`.2n − 1 ≥ 0` and fails for `n ∈ {1, 3}`, where the lemma holds trivially (`P₃ > 4.85`); the
equality at D:1360 drops a term `+p³/2` (it should be `≥`). Gap and typo (departure 7).

**E11. Appendix A (D:1525–1537).** "With .56 = .56" is garbled and "20.56/√n" stands for
`2(.56)/√n`; bounding `P(||R₀| − n/2| ≤ c′√n)` needs the strict form of the lower tail, which
Berry–Esseen also gives. Typos and a harmless boundary slip. The appendix proves the delayed version
of Theorem 1.4, as the paper says.

### The sparse paper (arXiv v2)

**E12. Theorem 1.4, proof (S:342–351).** The choice `λ_ε = 10/C_ε` handles only large `n`: the `o(1)`
terms need `λ` large relative to Theorem 1.2's constants (and `p ≤ 1` forces `n ≥ λ²`). The proof
also needs the case `pn > n − 10` (E1). Minor gap; the theorem holds.

**E13. Theorem 1.5 is false as printed (S:389–394).** The theorem claims that a random colouring with
`P(Red) = 1/2 + ω((pn)⁻¹)` leads to Red unanimity with probability `1 − o(1)` whenever
`p ≥ (1 + λ) log n/n`. Its proof says that "with probability 1 − o(1), |R| > |B|" (S:393), which
needs a bias `ω(n^(−1/2))`: the colour counts fluctuate by `Θ(√n)`. Counterexample: `p = 1` (the
complete graph) and `P(Red) = 1/2 + log n/n`. On `Kₙ`, Red wins only if `|R₀| > n/2`, which has
probability `.5692`, `.5106`, `.5014` for `n = 10⁴, 10⁶, 10⁸` (exact binomial computation), and
tends to 1/2. The proof also drops the terms `1/n` and `n^(−λ/2)` of Theorem 1.2 (S:394), which tend
to 0. Error. The corrected statement, with bias `ω(max{(pn)⁻¹, n^(−1/2)})`, follows by the paper's
argument and is proved ([`PowerOfFew.Sparse.theorem1_5`](PowerOfFew/Sparse/RandomColoring.lean#L278)); [`theorem1_5_printed_false`](PowerOfFew/Sparse/RandomColoring.lean#L644) proves that the printed statement is
false. A. N. Zehmakan's remark (ISAAC 2018) that a bias of order `n^(−1/2)` leaves the other colour a
constant chance at `p = 1` already contradicts the printed statement.

**E14. Theorems 1.7 and 4.1 are false as printed (S:431–438, S:1319–1330).** Theorem 1.7 writes
`p p_ac n ≥ (1 + λ) n⁻¹ log n`, a misprint for `p p_ac n ≥ (1 + λ) log n` (Theorem 4.1). Both claim
Red unanimity with probability `1 − o(1)` (Theorem 1.7) or with an explicit bound tending to 1
(Theorem 4.1) for every initial gap with `pΔ` (resp. `p p_up p_ac² Δ`) at least a constant.
Counterexample: `p = 1`, `p_ac = 1/2`, `p_up = 1`, `Δ = ⌊n^(1/4)⌋`. On the first day the difference
between the active Red and Blue vertices is `Δ ± Θ(√n)`, so it is at most `−1` with probability
tending to 1/2, and then every active vertex turns Blue and Blue keeps a linear majority; Red wins
with probability at most `1/2 + o(1)` (simulation: .577, .546, .524 for `n = 10⁴, 10⁵, 10⁶`). Error.
The paper's proof of Proposition 4.2 assumes `p_ac^(1/2) Δ ≥ S_ε n^(1/2)` (S:1358), which the
theorems omit. In arXiv v1 the first-day bound had no such hypothesis: its variance step bounds the
covariances given the active set and leaves out the variance of the conditional means, through
which the colour balance of the active set enters. Version 2 added the hypothesis to Proposition
4.2 but not to the theorems, and B. Tran's 2025 thesis repeats the theorems unchanged (Section 10).
The corrected statements keep that hypothesis with the failure probability `ε` of Proposition 4.2,
and the hypothesis `(1 − p) p_ac n ≥ 10` that the proofs use (Section 6); they are
proved ([`theorem4_1`](PowerOfFew/Sparse/Activation.lean#L217), [`theorem1_7`](PowerOfFew/Sparse/Activation.lean#L334)). [`theorem1_7_printed_false`](PowerOfFew/Sparse/ActivationCounterexample.lean#L882), [`theorem4_1_printed_false`](PowerOfFew/Sparse/ActivationCounterexample.lean#L898) and their
per-sequence forms prove the counterexample. The counterexample also contradicts the paper's claims
that the power of few "is robust" (abstract, S:229) and "remains robust" (S:426) under random
activations, and the suggestion that Conjecture 1.11 "will also be robust in this more general
model" (S:509–510): on
the complete graph the static process needs a lead of one vertex, while with activations a lead of
`n^(1/4)` loses with probability tending to 1/2.

**E15. Proposition 2.2, proof (S:712–878).**
- The variance bound `7n/12` is not proved for `p ≠ 1/2`. The proof quotes Lemma A.3 as
  `P(X = …) ≤ C_BE/√(p(1 − p)(n − 2))` (S:869), but Lemma A.3 gives `2 C_BE (1 − 2σ²)/(σ√(n − 2))`,
  a factor `2(1 − 2σ²)` larger; the argument then gives
  `Var|B₁| ≤ n(1/4 + 1.2544 (1 − 2σ²)² (n − 1)/(n − 2))`, which is at most `7n/12` at `p = 1/2` for
  `n ≥ 18` but tends to `1.504n` as `p → 0` or `1`. Unproved, not refuted (simulations give a much
  smaller variance). Lemma 2.1, Theorem 1.2 and the other results hold with the constant the
  argument gives ([`varConst`](PowerOfFew/Sparse/DayOne.lean#L49)), as the user decided.
- The proof applies Lemma A.3 at points `d ≤ 0`, outside its hypothesis `0 < d < (n₁ + n₂)/2`; the
  lemma's own proof works for every integer `d` (departure 8; Section 5).
- Its last step turns `1/2 − min{D_c, D_c x}` into `1/2 − D_c min{1, x}`, which needs `D_c ≥ 0`; the
  formal statement assumes `D_c > 0`, all that Lemma 2.1 uses. The replacement of the error term
  `C_BE (1 − 2σ²)/(σ√(n − 1))` by `C_BE/(σ√n)` (S:764) is valid because `D_c > 0` forces
  `c > 1.12`.
- Typos in the covariance computation (S:749–878), checked case by case: `ℓ₀(v)` for `ℓ₀(u)` and the
  index set `u ≠ v` (S:749, S:751); `E_u` and `F_u` swapped relative to their definitions, and the
  factors `p`, `1 − p` omitted (S:829–844, harmless by symmetry); `1_{B₀}(v)` for `1_{R₀}(v)` (S:857);
  `≥` for `≤` (S:860); the point of `X` is `(1 − ℓ₀(u))/2` (both printed values, S:863 and S:869,
  are wrong for a Blue `u`); `Σ_{u<v}` for `2Σ_{u<v}` (S:878).

**E16. Lemma 2.3 (S:918–1103).** The function `F` is printed with `2h(x)` (S:922); the proof
(S:1103) and Lemma 2.4 (S:1126) use `2h(b₁)`, the source fraction. The statement allows
`0 ≤ b₂ ≤ b₁ ≤ 1/2 − 7/n` for every `n`, but the proof takes `x ≤ 1/2 − 2/√n` and `n` large
(S:1064–1068); its claim "it suffices that n(1 − 2x)² ≥ 7" should be 98/9 (still at most 16). Its
formula for `T − f(0)` (S:1022) misses a nonnegative term `|S|(xn − ⌊xn⌋)e^t`; `e^{−pn|S| g(t_x)}`
should be `e^{pn|S| g_x(t_x)}` (S:1074); the case of an empty Blue set (`x < 1/n`) is assumed away
(S:1064); and the step from S:1074 to S:1075 needs `1 − x/2 − (3/2) x^(1/3) (1 − x)^(2/3) ≥ 0`, which
is not justified (it follows from Lemma 2.4's inequality, or from the weighted AM–GM inequality).
Misprint, gaps and slips; the lemma holds on the range its proof covers, which the formalization
states (`n ≥ 163`, `0 < b₂ ≤ b₁ ≤ 1/2 − 2/√n`, as the user decided) (departure 9).

**E17. Lemma 2.4 (S:1109–1140).** It inherits Lemma 2.3's range, so it needs `a ≥ 2√p` and
`b ≤ b₁`. Its "routine Taylor expansion around 1/2" proves
`(1 − 2b)²/3 ≤ 1 − b/2 − (3/2) b^(1/3) (1 − b)^(2/3)` only near `b = 1/2`, while `b₁ = 1/2 − a/√(pn)`
need not be near 1/2; the inequality holds on `[0, 1/2]` (with `u = b^(1/3)`, `w = (1 − b)^(1/3)`,
the difference is a product of `(w − u)³ ≥ 0` and a nonnegative factor) and fails just above 1/2.
Gaps (departure 10).

**E18. Lemma 2.6, proof (S:1164–1198).** The proof stops after `T = ⌈log_{pn/A}(bn)⌉` days; when that
logarithm is an integer, its bound gives `|B_T| ≤ 1`, not `< 1`, and one more day is needed. "|B_{t*}|
= ∅" (S:1167) should read `B_{t*} = ∅`. Off-by-one, harmless (departure 11).

**E19. Theorem 1.2, the wrap-up (S:1201–1221).** It assumes `1 − 11/n ≥ p` (the theorem:
`n − 10 ≥ pn`) and claims that `min{√(p(1 − p)n), pΔ} ≥ 10` "for n sufficiently large", which fails for
`p` close to `1 − 10/n`, where `p(1 − p)n` is close to 10; so Lemma 2.1 cannot be applied with
`c = 10`. With `c = 3` the argument goes through (`D₃ = .26554 > D = .21`; `p(1 − p)n ≥ 9` for `n`
large: if `p > .9`, `(1 − p)n ≥ 10` gives it, and otherwise `p(1 − p)n ≥ pn/10 ≥ (1 + λ) log n/10`).
It then applies Lemma 2.4 with "a ≥ 2.2", which should be 2.1 (`0.21 · 10`; still
`ba² = 1.1025 > 3 log 2/2`). Gap and slip; the theorem holds (departure 12).

**E20. Theorem 3.1, proof (S:1258–1296).** A sentence is garbled (S:1264–1265) and "≤ λ/4" should be
"≤ δ/4" (S:1271). The proof applies Lemma A.5 with `δ`, `ε` depending on `n`, which needs the lemma
uniformly in `δ` and `ε` (Section 6), and it needs `|B_t| ≤ n/4` on every day from day 2 on to apply
Lemma 2.5, which it leaves implicit (it follows from the paper's own dichotomy). Typos and gaps; the
theorem holds (departure 14).

**E21. The hypothetical colouring of Section 4 (S:1347, S:1414).** The hypothetical colouring is
defined "if every node is active and updating" (S:1347), but equation (S:1414),
`|B_{t+1}| = |B_t ∖ upd B_t| + |upd hypo B_t|`, holds only if an updating vertex observes its active
neighbours, which is how the proofs use it (S:1421, S:2094). For example, an updating vertex with one
active Blue and two inactive Red neighbours turns Blue, while the printed definition makes it Red.
Error in a definition, harmless; the formalization's [`hypoStep`](PowerOfFew/Model/Lazy.lean#L54) observes the active vertices.

**E22. Proposition 4.2 (S:1354–1369; proof S:2054–2198).** The statement says "for every ε ∈ (0, 1)
and T > 0", a misprint for `K > 0`. The proof sets `c = 10`, which needs `c ≤ √(p(1 − p)m)` for the
`m ≈ p_ac n` active vertices, i.e. `p(1 − p) p_ac n ≳ 100`; near `p = 1` the hypotheses allow
`p(1 − p) m ≈ 10` (departure 15 takes `c = 2`). It uses Lemma 2.1's constant `C(c, D) < 14`, which
rests on the unproved `7n/12` (E15; with the constant the argument gives, `11ε^(−1/2)` becomes about
`17ε^(−1/2)`, harmless since the constant is existential). Its final display needs
`p_up² p_ac n ≥ 121/ε`, true for `n` large but not stated. Its Chernoff band
`C_ε √(p_ac |B₀|)` fails when `p_ac |B₀|` is small (departure 15). Typos: "a universal constant C",
then `C_ε` (S:2055); `Δ′` without the active superscripts (S:2097); `m − p_acΔ/2` for
`m/2 − p_acΔ/2` (S:2101); a spurious factor 1/2 (S:2110); "from Lemma 2.1" for Proposition 2.2's
expectation bound (S:2123); `Var|B₁|` for `Var|B|` (S:2129); `(p^(1/2) p_up p_ac Δ²)²` for
`(p^(1/2) p_up p_ac Δ)²` (S:2179). A leftover paragraph (S:1389–1390) still uses earlier constants.
Gaps and typos; the proposition holds with `(1 − p) p_ac n ≥ 10` (Section 6).

**E23. Proposition 4.3 (S:1398–1511).** The statement's "for every ε > 0" is unused. In the proof,
`e^(−Ω(p_up p_ac n))` should be `e^(−Ω(p_up p_ac |B_t|))` and `B₁ ∖ upd B_t` should be `B_t ∖ upd B_t`
(S:1416–1418), and Lemma A.6, cited there, gives only the upper tail (the lower tail is a standard
Chernoff bound); `M` is defined and `T` used (S:1426–1449); "≤ 1.05|ac hypo B₂|" misses the factor
`p_up` (S:1456); "≤ 1.1 p_ac n" needs `K ≤ .4√(p p_ac n)` (true for `n` large, `K` being fixed); the
range "α_λ(log n)/2 ≥ b ≥ 1/2 − .1 p_up p_ac" is garbled (S:1468); "By Lemma 2.6"
(S:1485) should cite Lemma 2.5 with Lemmas A.7 and A.4, the first half of Lemma 2.6's proof, and its
"1 − O(n⁻¹)" is what those lemmas give with `n^(−a)` and `(p_ac n)^(−λ/2)`; the base of the logarithm
in `t*₁` is `1/(1 − .8 p_up p_ac)` and `t*₁` depends on `|B₂|` (S:1503). Typos and minor gaps; the
proposition holds.

**E24. Proposition 4.4 (S:1514–1533).** The proof applies Lemma A.4 to the active subgraph
`G(V_t^ac) ∼ G(|V_t^ac|, p)` and claims minimum degree `≥ α_λ p p_ac n`; Lemma A.4 gives
`α_λ p |V_t^ac|` and needs `p|V_t^ac| ≥ (1 + λ) log |V_t^ac|`, so a concentration step for `|V_t^ac|`
is missing (for fixed `p_ac` it holds except with probability `n^(−ω(1))`); what the argument needs is
only degree `> α_λ log n`. "More Red neighbors than twice … Blue" holds only for `λ > 1/2`; what holds
and suffices is degree `> 2|B_t|`. Typos: `t*` for `t*₁`, "dat" for "day" (S:1521–1527). Gap;
the proposition holds (departure 16).

**E25. Lemma A.5 (S:1694–1806).** The statement's probability `1 − n^(−δ n^(λ+δ)/2)` does not match
the last line of the proof, `n^(−δ n^λ/2)` (S:1696, S:1805). The proof bounds `P(X ≤ ε E X)` with
`E X = pk(n − 1)`, while an average degree below `εpn` is the event `X < εpnk = εEX + εpk`; it treats
only sets of exactly `⌈n^(λ+δ)⌉` vertices, larger sets following by averaging; its `O(·)` terms need
`n` large; it has a sign error (S:1744); and it calls the bad event "average degree at least εpn"
(S:1757), where the lemma is about an average degree less than `εpn`.
Typos, slips and gaps; the lemma holds (departure 17).

**E26. Lemma A.7 (S:1920–1986).** With `t = 2√(apn)` the tail is `n^(−ac)`, weaker than the claimed
`n^(−a)` when `c < 1` (Theorem 3.1 uses `c = 1 − λ`); `t = 2√(a log n)` gives it. Theorem 3.2 of
Benaych-Georges–Bordenave–Knowles is quoted with `d = p(1 − p)(n − 1)` and `η` with `n^0.1`, while
the theorem has `d = p(n − 1)` and `q = √d ∧ n^(1/10) κ^(−1/9)`; the bound "η ≤ c^(−1/2)" ignores the
second branch of `q`, and with the paper's own `d = p(1 − p)(n − 1)` it fails near `p = 1`; and the
theorem needs `q ≥ 1`, which fails for small `n`. Gaps, harmless: the
conclusion holds with a different constant (departure 18).

**E27. Typos and minor slips.**
- Dense paper: `F²(p, n, c)` for `F(n, p, c)²` (D:494); `c` for `cₙ` (D:570); Theorem 2.2 omits
  "independent" (D:742); `(1 − 2p − 2p²)` for `1 − 2p + 2p²` (D:811); `σ√(n1)` (D:885); `(1 − p)b₂b₂`
  for `(1 − p)b₁b₂` (D:957; the identity at D:958 fails as printed); "Equations (2.2) and (2.1) together
  yield" points to the wrong equations (D:1046); "art one" for "Part one" (D:1078); `supp(X)` for
  `supp(Xᵢ)` in Theorem 3.1 (D:1102); "of size" for "of at most" (D:1153); "S is a sum" for "δ(S) is
  a sum" (D:1238); a stray parenthesis (D:1249); an unescaped `{0, 1}` (D:1254); "to size m − 1" for
  "at most m − 1" (D:1304, D:1339).
- Sparse paper: "Therem" (S:349); Theorem A.1 and Corollary A.2 omit "independent", Theorem A.1
  writes "variances σ₁, …, σₙ" for `σᵢ²` and uses `σ_X` undefined (S:1561–1586); `(1 ± O(p²))` should
  be `(1 ± O(p + np²))` (S:1237, harmless); in Lemma A.6, "X₁ ∼ Bin(Y₁, p), independently of Y" should
  be "conditionally on Y, independently of X′" (S:1893).

## 4. Missing hypotheses

| Where | Missing hypothesis | Counterexample without it | In the formalization |
| --- | --- | --- | --- |
| sparse Theorem 1.5 | bias `ω(n^(−1/2))` as well as `ω((pn)⁻¹)` | `p = 1`, `P(Red) = 1/2 + log n/n`: Red wins with probability → 1/2 (E13) | [`PowerOfFew.Sparse.theorem1_5`](PowerOfFew/Sparse/RandomColoring.lean#L278) assumes `(q − 1/2) min{pn, √n} → ∞`; [`theorem1_5_printed_false`](PowerOfFew/Sparse/RandomColoring.lean#L644) |
| sparse Theorems 1.7 and 4.1 | `p_ac^(1/2) Δ ≥ S_ε n^(1/2)`, with a failure probability `ε` | `p = 1`, `p_ac = 1/2`, `p_up = 1`, `Δ = ⌊n^(1/4)⌋`: Red wins with probability at most `1/2 + o(1)` (E14) | [`theorem1_7`](PowerOfFew/Sparse/Activation.lean#L334), [`theorem4_1`](PowerOfFew/Sparse/Activation.lean#L217) assume it; [`theorem1_7_printed_false`](PowerOfFew/Sparse/ActivationCounterexample.lean#L882), [`theorem4_1_printed_false`](PowerOfFew/Sparse/ActivationCounterexample.lean#L898) and their `_seq` forms |

The corrected Theorems 1.7 and 4.1 also assume `(1 − p) p_ac n ≥ 10`, which the proofs use (they
apply Lemmas 2.1 and 2.4 to the active subgraph, as the proof of Theorem 1.2 uses `n − 10 ≥ pn`); no
counterexample without it is known (Section 6 lists it among the corrections).

## 5. Redundant hypotheses

| Result | Hypothesis that is not needed | Lean |
| --- | --- | --- |
| dense Lemma 2.3 | `n₁ > n₂` (only `n₁ + n₂ ≥ 1` is needed) | kept, as printed |
| dense Lemma 2.4 | `d` an integer (any real `d` works) | kept, as printed |
| dense Theorem 1.5 | `ε ≤ 1` | dropped ([`PowerOfFew.Dense.theorem1_5`](PowerOfFew/Dense/Appendix.lean#L42)) |
| dense Theorem 1.6 | `c > 0`: it follows from `F(n, p, c) > 0`, since `F(n, p, 0) < 0` | dropped ([`theorem1_6`](PowerOfFew/Dense/Main.lean#L44)); the Challenge keeps it |
| dense Claim 2.6 | `c > 0` | dropped ([`claim2_6`](PowerOfFew/Dense/DayOne.lean#L748)) |
| sparse Lemma A.3 | `d` a positive integer below `(n₁ + n₂)/2` (the proof works for every integer `d`) | kept in [`lemmaA_3`](PowerOfFew/Sparse/BerryEsseen.lean#L140); the general form is [`sparseAux_pointProb_le`](PowerOfFew/Sparse/BerryEsseen.lean#L62) |

## 6. How the formalization reads the papers

Representation:

- The random graph `G(n, p)` is Mathlib's `SimpleGraph.binomialRandom (Fin n) p`; probabilities of
  events are [`gnpProb`](Challenge.lean#L86). A colouring is its Blue set `B`; Red is the complement. `majorityStep G B` is
  the next day's Blue set: a vertex is Blue if it has more Blue than Red neighbours, or as many and is
  Blue already; [`blueAfter`](Challenge.lean#L104) iterates it. A random colouring ([`coloredProb`](Challenge.lean#L117)) is independent of the
  graph. In the activation model ([`lazyStep`](Challenge.lean#L127), [`lazyLaw`](Challenge.lean#L149)), day `t + 1` uses fresh activation and
  update coins, independent of each other, of the graph and of the other days; an updating vertex
  takes the majority among its active neighbours (E21). `Φ` is the standard normal distribution
  function; [`PowerOfFew.Φ_eq_cdf_gaussianReal`](PowerOfFew/Model/Normal.lean#L39) identifies it with Mathlib's Gaussian law.
- `Δ = n/2 − |B₀|` is a real number. "Red starts with `n/2 + c`" is read as "at least"; "Red wins" as
  "Blue is empty on some day" (once empty, Blue stays empty); for random colourings, a tie counts as a
  failure.
- Constants hidden in `O(·)` and "n sufficiently large" are made explicit: the constants may depend
  on the parameters the papers fix (`λ` in the sparse Theorems 1.2 and 3.1; `λ`, `ε`, `p_ac`, `p_up`
  in Section 4), and "for `n` large" becomes a threshold `N` or a constant that absorbs small `n`.
  The order of the quantifiers is the proofs': for instance, in Theorem 4.1, `c₂` is chosen after
  `λ` and `K` and before `p_ac`, `p_up`.
- Dense Theorem 1.6, Parts 2–4, are stated as their proofs give them (E3): with probability at least
  `1 − Pₜ`, the graph shrinks every Blue set below the next threshold.
- Dense Lemma 2.4 assumes `n₁ + n₂ ≥ 1` (its bound is undefined otherwise).
- The Berry–Esseen inequality and the sparse Corollary A.2 are read with independent summands
  (E27).
- Sparse Lemma 2.6 is stated as its proof gives it: with the stated probability, the graph empties
  every Blue set of at most `bn` vertices within `K log n/log(pn)` days.
- Sparse Lemma A.5 is stated uniformly in `δ` and `ε` (one threshold `N(λ)` for all of them), as the
  proof of Theorem 3.1 uses it with `δ`, `ε` depending on `n` (E20), and with the conditions its proof
  uses: `n ≥ N(λ)`, `δ ≤ (1 − λ)/2` and `δ log n ≥ 8`.
- Sparse Lemma A.6: `Bin(m, p)` with real `m` is read with `⌊m⌋`, and `X ∼ Bin(Y, p)` as a sum of
  independent coins `ξ₁, ξ₂, …` up to `Y`. The formal statement does not require `Y` to be
  independent of the coins: the proof's coupling is pointwise.
- Sparse Propositions 4.3 and 4.4 ("under the assumption …, with probability …") are stated as their
  proofs give them: the probability that the assumption holds and the conclusion fails is small.
  Proposition 4.4's random day `t*₁` is read as "some day `t₀ ≤ A₁ log n/(p_up p_ac)`".

Corrections of statements (Section 3 has the reasons):

- Dense Theorem 1.6 and Lemma 3.5 use `P₂` with the coefficient 1.83 (E2).
- Dense Claim 2.6 is stated for `|B₀| = ⌊n/2 − c⌋` and `n ≥ 20`, the case Lemma 2.1's proof uses
  (E7); Lemma 2.1 is as printed.
- Sparse Lemma 2.1 and Proposition 2.2 use the variance constant `varConst n p` that the argument
  gives, in place of `7/12` (E15); Proposition 2.2 also assumes `D_c > 0`.
- Sparse Lemma 2.3 is stated for `n ≥ 163` and `0 < b₂ ≤ b₁ ≤ 1/2 − 2/√n`, the range its proof covers,
  with `2h(b₁)` (E16); Lemma 2.4 assumes `2√p ≤ a` and `b ≤ 1/2 − a/√(pn)`, the hypotheses of Lemma
  2.3 as its proof uses them (E17). These were decisions of the user.
- Sparse Theorem 1.5 is corrected (E13); sparse Theorems 1.7 and 4.1 are corrected (E14), with the
  misprint `n⁻¹ log n` read as `log n`. Theorems 1.7, 4.1 and Propositions 4.2, 4.3 assume
  `(1 − p) p_ac n ≥ 10`, which their proofs use (E22, E23). Proposition 4.2's "T > 0" is read as
  `K > 0`.

## 7. Departures from the papers' proofs

Every proof follows its paper's argument. These nineteen results depart from it at one or more
steps, each to repair a step that is wrong or has a gap that the paper's lines cannot close as
written; the docstring of each (for Lemma 2.4, of the inequality it uses) says "Departure from the
paper".

| # | Result | The paper's argument | The formalization's | Why it is necessary | E |
| --- | --- | --- | --- | --- | --- |
| 1 | dense Theorem 1.2 | `P₁ ≤ .0902` | `P₁ ≤ .0965` (via `Φ₀(a) ≥ (a − a³/6)/√(2π)`) | the paper's value is wrong | E4 |
| 2 | dense Theorem 1.3 | `K = 4φ⁻² + 1`, for `n`, `cₙ` large | `K = 8φ⁻² + K′(p) + (2L/φ)²`; the trivial case when `mφ < 2L` | the factor is 8; small `n`, `cₙ` and `n ≲ 80/p³` are not covered | E5 |
| 3 | dense Lemma 2.1 | Chebyshev with Claims 2.5, 2.6 | the trivial case `P₁ ≥ 1` (all `n < 20`); `B₀` enlarged to `⌊n/2 − c⌋` vertices, by monotonicity | Claim 2.6 assumes `\|B₀\| = n/2 − c` and `n ≥ 20` | E7 |
| 4 | dense Claim 2.5 | `\|R₀\| − \|B₀\| = 2c` | `≥ 2c`, with `Φ₀` increasing | the equality does not hold in general | E7 |
| 5 | dense Lemma 3.4 | union bound over Blue sets of exactly `n₀` vertices | smaller sets by monotonicity | the statement allows at most `n₀` | E8 |
| 6 | dense Lemma 3.5 | — | the case `n/2 − .8√n/p < 0` | left implicit | E9 |
| 7 | dense Lemma 3.6 | `(n − 2n₂ − 1)² ≥ (.2n − 1)²` | `n ≤ 4` by `P₃ ≥ 1` | the step fails for `n ∈ {1, 3}` | E10 |
| 8 | sparse Proposition 2.2 | Lemma A.3 at `d ≤ 0` | Lemma A.3 for every integer `d` ([`sparseAux_pointProb_le`](PowerOfFew/Sparse/BerryEsseen.lean#L62)), by A.3's proof | Lemma A.3 assumes `d > 0` | E15 |
| 9 | sparse Lemma 2.3 | as printed | the missing term of `T − f(0)`; the bound 98/9 for `x ≥ 1/9`; the case of an empty Blue set; the nonnegativity at S:1075 | slips and gaps | E16 |
| 10 | sparse Lemma 2.4 | a Taylor expansion around `b = 1/2` | an exact factorization on `[0, 1/2]` ([`Real.one_sub_two_mul_sq_div_three_le`](Basic/Analysis/SpecialFunctions/CubeRoot.lean#L48)) | the expansion covers only `b` near 1/2 | E17 |
| 11 | sparse Lemma 2.6 | `⌈log_{pn/A}(bn)⌉` days | `⌊log_{pn/A}(bn)⌋ + 1` days | off by one | E18 |
| 12 | sparse Theorem 1.2 | Lemma 2.1 with `c = 10` | `c = 3` | `c = 10` is not admissible for `p` near `1 − 10/n` | E19 |
| 13 | sparse Theorems 1.4, 1.5 | Theorem 1.2 for every `p` | the case `pn > n − 10` by a two-day argument ([`colorAux_nearComplete`](PowerOfFew/Sparse/ColoringAux.lean#L465)) | Theorem 1.2 assumes `pn ≤ n − 10` | E1, E12 |
| 14 | sparse Theorem 3.1 | — | `\|B_t\| ≤ n/4` for every `t ≥ 2`, from the paper's dichotomy | left implicit; needed for Lemma 2.5 | E20 |
| 15 | sparse Proposition 4.2 | `c = 10`; the band `C_ε√(p_ac\|B₀\|)` by Chernoff | `c = 2`; the band `C_ε√(max{p_ac\|B₀\|, C_ε²})` | `c = 10` is not admissible for `p` near 1; Chernoff does not give the band for small `\|B₀\|` | E22 |
| 16 | sparse Proposition 4.4 | Lemma A.4 on the active subgraph, degree `≥ α_λ p p_ac n` | Lemma A.4 after a concentration step for `\|V_t^ac\|`; degree `> α_λ log n` | Lemma A.4 needs its hypothesis on `\|V_t^ac\|` | E24 |
| 17 | sparse Lemma A.5 | `P(X ≤ ε E X)`; sets of exactly `⌈n^(λ+δ)⌉` vertices | the threshold `εpnk`; larger sets by removing vertices of maximal degree | the event is `X < εpnk`; larger sets were not treated | E25 |
| 18 | sparse Lemma A.7 | `t = 2√(apn)`; `η ≤ c^(−1/2)` | `t = 2√(a log n)`; `η ≤ √(2/c) + 5`; small `n` by the Frobenius norm | the tail is `n^(−ac)`; a branch of `q`; `q < 1` for small `n` | E26 |

Two further choices are not departures. The proof of the sparse Proposition 4.3 cites "Lemma 2.6"
for a bound that is the first half of Lemma 2.6's proof; the formal proof uses Lemmas 2.5, A.7 and
A.4, as that proof does (E23). The proof of the sparse Proposition 4.2 reuses Proposition 2.2's
variance bound where the paper reuses its covariance bound, the same argument packaged. The dense
Theorem 1.5 has no proof in its paper; its formal proof derives it from the sparse Theorem 1.2 and the
two-day argument of departure 13.

## 8. What each result depends on

Generated by [`scripts/Audit.lean`](scripts/Audit.lean) (the results from prior work that each proof reaches; every
result uses only the standard axioms):

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| D Thm 1.2 | [`PowerOfFew.Dense.theorem1_2`](PowerOfFew/Dense/Main.lean#L290) | Berry–Esseen (assumed), Hoeffding, central binomial bound (Matoušek–Nešetřil) |
| D Thm 1.3 | [`PowerOfFew.Dense.theorem1_3`](PowerOfFew/Dense/Main.lean#L488) | Berry–Esseen (assumed), Hoeffding, central binomial bound (Matoušek–Nešetřil) |
| D Thm 1.5 | [`PowerOfFew.Dense.theorem1_5`](PowerOfFew/Dense/Appendix.lean#L42) | Berry–Esseen (assumed), BBK Thm 3.2 (assumed), BLM Thm 6.10 (assumed), Chernoff, entropy bound for C(n, k) |
| D Thm 1.6 | [`PowerOfFew.Dense.theorem1_6`](PowerOfFew/Dense/Main.lean#L44) | Berry–Esseen (assumed), Hoeffding, central binomial bound (Matoušek–Nešetřil) |
| D Lemma 2.1 | [`PowerOfFew.Dense.lemma2_1`](PowerOfFew/Dense/DayOne.lean#L873) | Berry–Esseen (assumed) |
| D Thm 2.2 (Berry–Esseen) | [`PowerOfFew.ShevtsovaBerryEsseen`](Challenge.lean#L207) | – |
| D Lemma 2.3 | [`PowerOfFew.Dense.lemma2_3`](PowerOfFew/Dense/BinomialDifference.lean#L81) | Berry–Esseen (assumed) |
| D Lemma 2.4 | [`PowerOfFew.Dense.lemma2_4`](PowerOfFew/Dense/BinomialDifference.lean#L122) | Berry–Esseen (assumed) |
| D Claim 2.5 | [`PowerOfFew.Dense.claim2_5`](PowerOfFew/Dense/DayOne.lean#L317) | Berry–Esseen (assumed) |
| D Claim 2.6 | [`PowerOfFew.Dense.claim2_6`](PowerOfFew/Dense/DayOne.lean#L748) | Berry–Esseen (assumed) |
| D Thm 3.1 (Hoeffding) | [`ProbabilityTheory.measureReal_sum_ge_add_le_exp`](Basic/Probability/Concentration.lean#L60) | – |
| D Lemma 3.2 | [`PowerOfFew.Dense.lemma3_2`](PowerOfFew/Dense/Shrinking.lean#L32) | central binomial bound (Matoušek–Nešetřil) |
| D Lemma 3.3 | [`PowerOfFew.Dense.lemma3_3`](PowerOfFew/Dense/Shrinking.lean#L135) | Hoeffding |
| D Lemma 3.4 | [`PowerOfFew.Dense.lemma3_4`](PowerOfFew/Dense/Shrinking.lean#L464) | Hoeffding, central binomial bound (Matoušek–Nešetřil) |
| D Lemma 3.5 | [`PowerOfFew.Dense.lemma3_5`](PowerOfFew/Dense/Shrinking.lean#L557) | Hoeffding, central binomial bound (Matoušek–Nešetřil) |
| D Lemma 3.6 | [`PowerOfFew.Dense.lemma3_6`](PowerOfFew/Dense/Shrinking.lean#L684) | Hoeffding, central binomial bound (Matoušek–Nešetřil) |
| D App. A | [`PowerOfFew.Dense.appendixA`](PowerOfFew/Dense/Appendix.lean#L154) | Berry–Esseen (assumed), BBK Thm 3.2 (assumed), BLM Thm 6.10 (assumed), Chernoff, entropy bound for C(n, k) |
| S Thm 1.2 | [`PowerOfFew.Sparse.theorem1_2`](PowerOfFew/Sparse/Main.lean#L232) | Berry–Esseen (assumed), BBK Thm 3.2 (assumed), BLM Thm 6.10 (assumed), Chernoff, entropy bound for C(n, k) |
| S Thm 1.4 | [`PowerOfFew.Sparse.theorem1_4`](PowerOfFew/Sparse/RandomColoring.lean#L85) | Berry–Esseen (assumed), BBK Thm 3.2 (assumed), BLM Thm 6.10 (assumed), Chernoff, entropy bound for C(n, k) |
| S Thm 1.5 | [`PowerOfFew.Sparse.theorem1_5`](PowerOfFew/Sparse/RandomColoring.lean#L278) | Berry–Esseen (assumed), BBK Thm 3.2 (assumed), BLM Thm 6.10 (assumed), Chernoff, entropy bound for C(n, k) |
| S Thm 1.7 | [`PowerOfFew.Sparse.theorem1_7`](PowerOfFew/Sparse/Activation.lean#L334) | Berry–Esseen (assumed), BBK Thm 3.2 (assumed), BLM Thm 6.10 (assumed), Chernoff, entropy bound for C(n, k) |
| S Lemma 2.1 | [`PowerOfFew.Sparse.lemma2_1`](PowerOfFew/Sparse/DayOne.lean#L607) | Berry–Esseen (assumed) |
| S Prop 2.2 | [`PowerOfFew.Sparse.proposition2_2`](PowerOfFew/Sparse/DayOne.lean#L469) | Berry–Esseen (assumed) |
| S Lemma 2.3 | [`PowerOfFew.Sparse.lemma2_3`](PowerOfFew/Sparse/DayTwo.lean#L652) | entropy bound for C(n, k) |
| S Lemma 2.4 | [`PowerOfFew.Sparse.lemma2_4`](PowerOfFew/Sparse/DayTwo.lean#L814) | entropy bound for C(n, k) |
| S Lemma 2.5 | [`PowerOfFew.Sparse.lemma2_5`](PowerOfFew/Sparse/DayThree.lean#L98) | – |
| S Lemma 2.6 | [`PowerOfFew.Sparse.lemma2_6`](PowerOfFew/Sparse/DayThree.lean#L395) | BBK Thm 3.2 (assumed), BLM Thm 6.10 (assumed), Chernoff |
| S Thm 3.1 | [`PowerOfFew.Sparse.theorem3_1`](PowerOfFew/Sparse/Subconnectivity.lean#L641) | Berry–Esseen (assumed), BBK Thm 3.2 (assumed), BLM Thm 6.10 (assumed), entropy bound for C(n, k), period two (Goles–Olivos) |
| S Thm 4.1 | [`PowerOfFew.Sparse.theorem4_1`](PowerOfFew/Sparse/Activation.lean#L217) | Berry–Esseen (assumed), BBK Thm 3.2 (assumed), BLM Thm 6.10 (assumed), Chernoff, entropy bound for C(n, k) |
| S Prop 4.2 | [`PowerOfFew.Sparse.proposition4_2`](PowerOfFew/Sparse/ActivationDayOne.lean#L855) | Berry–Esseen (assumed), Chernoff |
| S Prop 4.3 | [`PowerOfFew.Sparse.proposition4_3`](PowerOfFew/Sparse/ActivationShrinking.lean#L1829) | BBK Thm 3.2 (assumed), BLM Thm 6.10 (assumed), Chernoff, entropy bound for C(n, k) |
| S Prop 4.4 | [`PowerOfFew.Sparse.proposition4_4`](PowerOfFew/Sparse/ActivationLastDays.lean#L832) | Chernoff |
| S Thm A.1 (Berry–Esseen) | [`PowerOfFew.ShevtsovaBerryEsseen`](Challenge.lean#L207) | – |
| S Cor A.2 | [`PowerOfFew.Sparse.corollaryA_2`](PowerOfFew/Sparse/BerryEsseen.lean#L41) | Berry–Esseen (assumed) |
| S Lemma A.3 | [`PowerOfFew.Sparse.lemmaA_3`](PowerOfFew/Sparse/BerryEsseen.lean#L140) | Berry–Esseen (assumed) |
| S Lemma A.4 | [`PowerOfFew.Sparse.lemmaA_4`](PowerOfFew/Sparse/Degrees.lean#L124) | Chernoff |
| S Lemma A.5 | [`PowerOfFew.Sparse.lemmaA_5`](PowerOfFew/Sparse/Degrees.lean#L676) | entropy bound for C(n, k) |
| S Lemma A.6 | [`PowerOfFew.Sparse.lemmaA_6`](PowerOfFew/Sparse/Chernoff.lean#L47) | Chernoff |
| S Lemma A.7 | [`PowerOfFew.Sparse.lemmaA_7`](PowerOfFew/Sparse/MatrixNorm.lean#L373) | BBK Thm 3.2 (assumed), BLM Thm 6.10 (assumed) |

The route check (`python3 scripts/route_check.py check docs/paper_routes.tsv --accept
docs/route_differences.tsv`) compares the numbered results each formal proof uses with those its
paper's proof cites ([`docs/paper_routes.tsv`](docs/paper_routes.tsv), extracted from the TeX sources). Every proof uses them,
with four differences recorded in [`docs/route_differences.tsv`](docs/route_differences.tsv). One is departure 8: the sparse
Proposition 2.2 uses Lemma A.3's general form. The other three are not departures: dense Lemma 2.4
reuses Lemma 2.3's computation rather than its statement; the sparse Proposition 4.2 takes only Lemma
2.1's constants; the sparse Proposition 4.3 uses the lemmas inside Lemma 2.6's proof.

## 9. Not formalized

- The dense paper's Theorem 1.4 (the theorem of Fountoulakis, Kang and Makai), which the papers
  restate for context and re-derive in a delayed form (dense Appendix A, sparse Theorem 1.4); the
  delayed forms are formalized.
- The conjectures: dense Conjectures 1.7 and 1.8; sparse Question 1.9 and Conjectures 1.11, 1.13
  and 1.15.
- The numerical experiments: the dense paper's table of simulations, and the sparse Experiments 1.10,
  1.12 and 1.14.
- The sparse Remark 1.3 (equivalent models of the initial colouring), Remark 1.8 (Theorem 1.7 does
  not imply Theorem 1.2), Remark 3.2 (flowers), and the remark after Proposition 4.4 on the
  optimality of the time bound.

## 10. The papers in the literature

Searched on 2026-10-17: the arXiv API (titles and abstracts: "majority dynamics", "unanimity",
"power of few", and the authors), Crossref (metadata, reference lists and its filter for
corrections), the citation lists of OpenAlex and Semantic Scholar, zbMATH Open, DROPS/LIPIcs,
theoryofcomputing.org, the authors' pages, GitHub, the Reservoir index, Mathlib, the Isabelle AFP,
Google Scholar (until it blocked scripted access), MathOverflow (through the Stack Exchange API), the
Internet Archive and a general web search. Every summary below was checked against its source by a
second reader, where the source could be opened: not the papers of Goles–Olivos and Poljak–Sůra.
Claims that something does not exist were only corroborated. Wiley, ScienceDirect, SpringerLink,
Project Euclid and the Yale thesis server refused scripted access, so a few published texts were read
in their arXiv versions, and B. Tran's thesis in a capture of the Internet Archive's Wayback Machine;
this is said where it matters. Δ is the larger camp's excess over n/2. Preprints are reported as
claims.

### Before the papers

- **Period two.** E. Goles and J. Olivos, *Discrete Math.* 30 (1980) 187–189 and *Discrete Appl.
  Math.* 3 (1981) 93–105, and independently S. Poljak and M. Sůra, *Combinatorica* 3 (1983)
  119–121: majority dynamics on a finite graph is eventually periodic, with period at most two. The
  sparse paper uses only this fact (proof of Theorem 3.1), and calls the two works "independently
  proven". It is proved in `External/GolesOlivos/` ([`blueAfter_eventually_period_two`](PowerOfFew/External/GolesOlivos/GolesOlivos.lean#L127)).
- **Majority dynamics as opinion exchange.** E. Mossel, J. Neeman and O. Tamuz, *Auton. Agents
  Multi-Agent Syst.* 28 (2014) (arXiv:1207.0893): on expanders, a sufficiently biased initial state
  leads to unanimity; the
  survey of E. Mossel and O. Tamuz, *Probab. Surveys* 14 (2017), is the papers' general reference.
- **The conjecture both papers address.** I. Benjamini, S.-O. Chan, R. O'Donnell, O. Tamuz and
  L.-Y. Tan, *Stoch. Proc. Appl.* 126 (2016) (arXiv:1405.2486): on G(n, p) with p ≥ c n^(−1/2) and
  independent uniform initial opinions, the majority wins at time 4 with probability at least 0.4.
  Both papers quote this result. The dense paper (D:424), like Fountoulakis, Kang and Makai, says that
  Benjamini et al. conjecture that the probability tends to 1; their arXiv text states only the
  nearby Conjecture 1.5, which is the one the sparse paper quotes (S:503–505).
- **Biased colourings.** A. N. Zehmakan, ISAAC 2018 (LIPIcs 123, art. 4) and *Discrete Appl. Math.*
  277 (2020) (arXiv:1805.12172): an initial Blue density 1/2 − ω(1/√(np)) above the connectivity
  threshold leads to all-Red in a constant number of rounds, and the paper remarks that this is
  tight: at p = 1, a bias of order c/√n leaves Blue a constant chance. The sparse paper cites it as
  the baseline that its Theorem 1.5 improves; the tightness remark already contradicts Theorem 1.5
  as printed at p = 1 (E13).
- B. Gärtner and A. N. Zehmakan, LATIN 2018 (arXiv:1711.07423), treat random regular graphs; neither
  paper cites them.

### Concurrent work

- **Fountoulakis, Kang and Makai (FKM)**, *Random Struct. Algorithms* 57 (2020) 1134–1156
  (arXiv:1910.05820, 2019-10-13, six weeks before the dense paper's first version): for every
  ε ∈ (0, 1] there are λ and n₀ such that for n > n₀ and p ≥ λ n^(−1/2), a uniformly random initial
  colouring leads to unanimity after four rounds with probability at least 1 − ε, which proves the
  conjecture above. The dense paper's first arXiv version does not cite it; its journal version
  restates it as Theorem 1.4 (Theorem 4 in arXiv v2; without the qualifier n > n₀), and both papers
  re-derive a
  delayed version (dense Appendix A, sparse Theorem 1.4) from their own theorems. Neither side calls
  the other independent; J. H. Kim and B. Tran later write that "Tran and Vu independently defined the
  fixed advantage coloring scheme".
- **R. Berkowitz and P. Devlin**, *Stoch. Proc. Appl.* 146 (2022) (arXiv:2010.08172): a central limit
  theorem for |R₁|, and on G(n, 1/2) a lead of three vertices suffices for winning probability at
  least 51%. Same question as the dense paper, by another method; the dense paper never cites it,
  the sparse paper does.
- **A. Sah and M. Sawhney**, *Israel J. Math.* 267 (2025) (arXiv:2105.13301, 2021): for
  (log n)^(−1/16) ≤ p ≤ 1 − (log n)^(−1/16) and an initial lead D ≤ (log n)^(1/4), the colour ahead
  wins with probability Φ(pD√2/√(πp(1 − p))) + O(n^(−c)), which proves the dense paper's Conjectures
  1.7 ("the power of one") and 1.8, stated for constant p; the journal version of the dense paper adds
  footnotes saying so.
- **D. Chakraborti, J. H. Kim, J. Lee and T. Tran**, *Random Struct. Algorithms* 63 (2023)
  (arXiv:2105.12709, 2021): unanimity after six days for λ′n^(−3/5) log n ≤ p ≤ λ n^(−1/2), and a bias
  condition below n^(−1/2). They cite the sparse theorem, then only announced in the dense paper's
  second version, as proved; its proof appeared in the sparse paper in 2023, under the hypotheses
  (1 + λ) log n ≤ pn ≤ n − 10 and pΔ ≥ 10.
- Different models: D. Mohan and P. Prałat, *ACM TEAC* 13 (2025) (arXiv:2309.04691), asynchronous
  single-node updates with private signals; J. Chellig and N. Fountoulakis, *Stoch. Proc. Appl.* 189
  (2025) (arXiv:2311.09078), three or more opinions. The dense paper promised a multi-opinion
  extension "in a later paper"; the sparse paper does not contain one (a 2024 UPC bachelor's thesis
  by A. Majó Rudé claims, in its abstract, the dense result in three days and an extension to a
  third opinion).

### Since the papers

- **J. H. Kim and B. Tran**, arXiv:2503.07447 (2025; dated June 2022 but revised after the sparse
  paper's publication), preprint: claims that Δ ≥ C_ε p^(−3/2) n^(−1/2) log n suffices for
  C n^(−1) log² n ≤ p ≤ n^(−1/2) log^(1/4) n, improving the sparse Theorem 1.2 there, and unanimity for
  random balanced colourings once p ≥ C_ε n^(−2/3) log^(2/3) n. Its abstract credits the condition
  "pΔ ≥ 100" to "L. Tran and Vu (2019)"; its body and both arXiv versions of the sparse paper have
  10.
- **S. Jaffe**, arXiv:2503.14401 (2025), preprint: claims Δ ≥ max{p^(−1/2) e^(A√log(1/p)),
  B p^(−3/2) n^(−1/2)} for (1 + λ) log n/n ≤ p ≤ 1 − 10/n, unanimity for random balanced colourings at
  p ≥ λ n^(−2/3), and (its Theorem 3.2) an extension of the sparse Theorem 1.5. That theorem rests
  on the same step as the sparse proof ("By the Berry-Esseen Theorem, with probability 1 − o(1),
  |C₁| > |C₂|"), and as stated it fails for the same reason (E13): its bias condition allows a bias
  of order ω(1)/n at constant p, and at p = 1/2 with bias log n/n Blue leads by δ√n with probability
  tending to Φ(−2δ), after which it wins by the dense Theorem 1.3.
- **G. Goel and A. Sah**, arXiv:2609.14957 (2026), preprint: claims the conjecture of Benjamini et al.
  whenever pN ≥ N^ε, unanimity in O(1/ε) days; it quotes the sparse theorem correctly.
- I. Dumitriu, M. Ju and H.-X. Wang, arXiv:2607.24652 and arXiv:2608.06159 (2026), preprints:
  stochastic block models, and graphs resampled every round; the second restates the sparse paper's
  Conjecture 1.11 as open.
- Y. Shang, *Results Math.* 76 (2021): unanimity for biased random colourings of inhomogeneous random
  graphs.
- **H. B. L. Tran's Yale PhD thesis** (2025; read in a Wayback Machine capture of the EliScholar
  PDF): it presents the sparse theorem (its Theorem 1.12), the Kim–Tran theorem, robustness when
  voters "do not reliably change sides" and the regime below connectivity. Its Theorems 1.17 and 6.1
  restate the sparse Theorems 1.7 and 4.1 as in arXiv v2, misprint included, and its Proposition 6.2
  keeps the hypothesis `p_ac^(1/2) Δ ≥ S_ε n^(1/2)`, so the error of E14 stands there too. It has
  no counterpart of the sparse Theorem 1.5.
- **Corrections.** We found no erratum, comment or paper that reports an error in either paper
  (Crossref registers no update for the ToC, LIPIcs or RSA versions). No later work discusses the
  random-activation model of the sparse paper's Section 4, apart from the thesis, which restates it
  unchanged. The three statements found false here (sparse Theorems 1.5, 1.7, 4.1) have not been
  flagged before; as noted above, Zehmakan's remark of 2018 already contradicts Theorem 1.5 at
  p = 1, and Jaffe's Theorem 3.2 repeats the error of Theorem 1.5.

### Versions

- The dense paper: arXiv v1 (2019-11-22) claims 90% for `n/2 + 5` and `n ≥ 550`; arXiv v2 (2020-05-18)
  93% for `n/2 + 6` and `n ≥ 550`; the APPROX/RANDOM 2020 version (LIPIcs 176) 90% for `n/2 + 6` and
  `n ≥ 300`; the journal version (2023), formalized here, 90% for `n/2 + 5` and `n ≥ 1000`, with a new
  Theorem 1.6. The arXiv v2 claim does not follow from its own argument: at its parameters its bound
  for the third day exceeds 1 (it is about 10^325). The journal version's claim does (E4).
- The sparse paper: arXiv v1 (2023-02-11), the published version (online 2024-09-14) and arXiv v2
  (2024-11-23), the accepted manuscript after two rounds of review. Between v1 and v2 the first-day
  bound of Section 4 changed: v1 derives it from a lemma without the hypothesis
  `p_ac^(1/2) Δ ≥ S_ε n^(1/2)`, whose proof leaves out the fluctuation of the active set (E14), and
  v2 states Proposition 4.2 with that hypothesis (the old statement remains in v2's source as a
  comment). Theorems 1.7 and 4.1 did not gain it: Theorem 1.7 is the same in both versions up to
  notation, and Theorem 4.1 only changed its condition `p_up p_ac² p Δ ≥ 10` to `≥ M` for a
  constant `M` and corrected the misprint that Theorem 1.7 keeps. The spectral bound of Lemma A.7
  moved from a result of Bandeira and van Handel to Theorem 3.2 of Benaych-Georges, Bordenave and
  Knowles; Theorems 1.2 and 1.5 are unchanged. No erratum of either paper was found.

### Formalizations

- **These papers:** none found in any system before this one.
- **Majority dynamics on G(n, p):**
  [gopalkgoel/sparse-majority-dynamics-lean](https://github.com/gopalkgoel/sparse-majority-dynamics-lean)
  (Lean 4, 2026), the formalization of Goel–Sah's theorem, also proves Fountoulakis–Kang–Makai's
  Theorem 1.1 (four rounds), stated over its own product weight on the edge and colour bits, with an
  adapter to Mathlib's `SimpleGraph.binomialRandom`. That theorem is the one the papers re-derive in
  delayed form (dense Appendix A, sparse Theorem 1.4); this formalization proves the delayed version
  by the papers' arguments and was made without consulting that repository.
- **The cited results:** Mathlib has the central limit theorem but no Berry–Esseen bound.
  [Polarnova/ProbabilityApproximation](https://github.com/Polarnova/ProbabilityApproximation)
  (Lean 4, 2026) proves a Berry–Esseen bound for independent, not necessarily identically
  distributed summands with constant 30 (0.56 does not appear), and
  [UCLA-Trustworthy-AI-Lab/BerryEsseenLean](https://github.com/UCLA-Trustworthy-AI-Lab/BerryEsseenLean)
  assumes Shevtsova's non-i.i.d. constant 0.5583 as an external input, as this project assumes 0.56.
  No formalization of the sharp bound `‖A − EA‖ = O(√(pn))` for sparse random matrices, or of
  Talagrand's inequality in the form of Boucheron–Lugosi–Massart's Theorem 6.10, was found in any
  system; [dududuguo/HighDimProb](https://github.com/dududuguo/HighDimProb) (Lean 4, 2026) proves the
  matrix Bernstein inequality, which gives only `O(√(pn log n))`. Mathlib has Hoeffding's inequality;
  McDiarmid's is in the Lean libraries lean-rademacher and atlas-lean and in the Isabelle AFP
  (*Concentration_Inequalities*, 2023). The
  Goles–Olivos period-two theorem was not found in any system. Mathlib's binomial random graph
  (`SimpleGraph.binomialRandom`, PR #31364, merged 2026-02-17) is the law used here.

## 11. What's next

Plans for follow-up papers are in [`NEXT.md`](NEXT.md).

### Open directions

- **The threshold for random activations.** The corrected Theorems 1.7 and 4.1 need an initial gap
  of order `√(n/p_ac)`, and the counterexample shows that a gap `o(√n)` does not suffice at `p = 1`.
  The natural question is the exact threshold: for which `Δ` does Red win with probability tending to
  1, and what is the limiting winning probability when `Δ` is of order `√(n/p_ac)`?
- **Biased random colourings.** The corrected Theorem 1.5 asks for a bias `ω(max{(pn)⁻¹, n^(−1/2)})`.
  When `p√n → ∞`, the argument of Theorem 1.4 (with Theorem 1.2 and the near-complete case of E1)
  shows that at bias `c n^(−1/2)` Red wins with probability tending to `Φ(2c)`, so the condition is
  sharp there; for `pn ≥ n^ε` the same would follow from Goel and Sah's claimed theorem. What remains
  open is the range `pn = n^(o(1))`, which lies inside the conjecture of Benjamini et al.
- **The papers' conjectures.** The sparse Conjecture 1.11 (the optimal power of few for
  `p ≥ (1 + λ) log n/n`) is proved by Sah and Sawhney only for `p ≥ (log n)^(−1/16)`. Question 1.9
  asks for the optimal gap, conjectured to be of order `p^(−1/2)`; Kim and Tran, and Jaffe, claim
  bounds closer to it in parts of the range (Section 10). Conjectures 1.13 and 1.15, on the regime
  near and below the connectivity threshold, are open. The dense Conjectures 1.7 and 1.8, stated for
  constant `p`, are proved by Sah and Sawhney.
- **Remarks on the conjectures** (on paper; elementary). (i) For `pn = c log n` with `c ≤ 1/2`, the
  graph has about `(c/2) n^(1−2c) log n → ∞` isolated edges, and a balanced colouring makes one of
  them bichromatic with probability tending to 1; that edge swaps its colours every day, so the
  function `f` of Conjecture 1.13 vanishes on `(0, 1/2]`, and there the conjecture's last part
  asserts that the balanced start ends near balance. (ii) If Conjecture 1.11 covers `Δ = 0`, it
  forces `f = 1` on `(1, ∞)` in Conjecture 1.13: for `c > 1` the second part of Conjecture 1.13
  makes a stable end a unanimity with high probability, so at `Δ = 0` Red wins with probability
  `f(c)/2 − o(1)`, while Conjecture 1.11 makes this limit independent of `c`. The paper's own
  experiment sees period two above `pn = log n` at `n = 10⁴`. (iii) The two parts of the conjecture
  of Benjamini et al. that the sparse paper quotes (their Conjecture 1.5: near balance for bounded
  `d_n`, near unanimity for every `d_n → ∞`) cannot both hold: if the first holds for every constant
  `d`, then for some `d_n → ∞` that grows slowly enough the process still ends near balance with
  high probability. The question is the growth rate of `d_n` at which near unanimity sets in.
- **The variance constant.** Proposition 2.2's `7n/12` is unproved for `p ≠ 1/2` (E15); simulations
  suggest a much smaller variance, and a sharper covariance bound would restore it.
- **Removing hypotheses.** The papers need `p` bounded away from 1 (`pn ≤ n − 10`;
  `(1 − p) p_ac n ≥ 10` in Section 4) only for their method; the near-complete case of E1 is handled
  by a separate argument, and the same may work for the activation model.

### Simpler proofs

- **`C(n, k) ≤ e^(n H(k/n))`** (the sparse Lemma 2.3's "routine Stirling bound") follows from the
  binomial theorem, `1 = (x + (1 − x))ⁿ ≥ C(n, k) xᵏ (1 − x)^(n−k)` with `x = k/n`, without Stirling.
  On paper.
- **Lemma A.6** needs neither the independence of `Y` from the coins nor anything about `Y` beyond
  `Y ≤ m`: `∑_{i<Y} ξᵢ ≤ ∑_{i<⌊m⌋} ξᵢ` pointwise, so it is Chernoff's bound for `Bin(⌊m⌋, p)`. The
  formal proof is this argument. In the proof of Proposition 4.3, every set to which Lemma A.6 is
  applied is fixed once the graph, the past and the activations are, so the plain Chernoff bound
  suffices there.
- **Lemma 2.3's bracket** `1 − x/2 − (3/2) x^(1/3) (1 − x)^(2/3) ≥ 0` follows from the weighted AM–GM
  inequality `x^(1/3) (1 − x)^(2/3) ≤ (2 − x)/3`. On paper.
- **Proposition 4.4:** the number of active neighbours of a vertex is `Bin(n − 1, p p_ac)`, so the
  argument of Lemma A.4 applied to these counts gives the degree bound without conditioning on the
  active set or concentrating its size. Checked in Lean during the work (that proof is not in the
  project, which follows the paper's route).
- **Dense Theorem 1.2:** the bound `Φ₀(a) ≥ (a − a³/6)/√(2π)` gives
  `√n Φ₀(11/√n) ≥ (11 − 1331/(6n))/√(2π)` for every `n ≥ 1000` directly, without the monotonicity of
  `F` in `n`. On paper.

### The formalization

- The three assumed results (Section 2): a Berry–Esseen bound with Shevtsova's constant is out of
  reach; a general Berry–Esseen bound with a larger constant exists outside Mathlib, but with it the
  arguments need larger thresholds (with constant 30, `D_c > 0` needs `c > 60`, so `pΔ > 60` and a
  near-complete case up to `(1 − p)n ≈ 3600`), and the dense paper's explicit 90% at `n ≥ 1000` is
  lost. The
  spectral bound of Lemma A.7 could come from the Feige–Ofek argument (discrepancy and ε-nets), which
  needs no concentration inequality beyond Chernoff's and would make the sparse paper depend on
  Berry–Esseen only.
- [`Basic/`](Basic) holds general results that could go to Mathlib: Chernoff's bounds in relative-entropy form,
  Bernoulli families and the binomial law of their sums, the upper bound for the central binomial
  coefficient and the entropy bound for binomial coefficients ([`Basic/README.md`](Basic/README.md) says where each could
  go).
- The activation model ([`PowerOfFew/Model/Lazy.lean`](PowerOfFew/Model/Lazy.lean): induced subgraphs of `G(n, p)`, independence of
  the days) and the edge-conditioning tools ([`PowerOfFew/Model/EdgeConditioning.lean`](PowerOfFew/Model/EdgeConditioning.lean)) are general
  tools for random-graph processes.
