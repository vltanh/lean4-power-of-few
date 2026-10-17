# The power of few: a Lean formalization of two papers on majority dynamics

A Lean 4 / Mathlib formalization of two papers on majority dynamics on the Erdős–Rényi random graph
`G(n, p)`, where every vertex adopts the colour of the majority of its neighbours, day after day:

- Linh Tran and Van Vu, *Reaching a consensus on random networks: the power of few*, Theory of
  Computing 19 (2023), article 6 (arXiv:1911.10279), the **dense paper**: for constant `p`, a camp
  with a constant advantage of `c` vertices wins within four days with probability
  `1 − O(max{1/n, 1/c²})`; on `G(n, 1/2)` with `n ≥ 1000`, five extra vertices win with probability at
  least 90%;
- BaoLinh Tran and Van Vu, *The "Power of Few" phenomenon: the sparse case*, Random Structures &
  Algorithms 66 (2025) e21260 (arXiv:2302.05605v2), the **sparse paper**: above the connectivity
  threshold, an advantage `Δ` with `pΔ ≥ 10` and `pΔ² → ∞` wins in `O(log n/log(pn))` days, with
  consequences for random colourings, the regime below connectivity, and a model with random
  activations and updates.

**The formalization is conditional** on three cited results that Lean does not have, assumed as
hypotheses named after their sources and stated in every theorem that uses them: the Berry–Esseen
inequality with Shevtsova's constant 0.56 ([`ShevtsovaBerryEsseen`](Challenge.lean#L207)), Theorem 3.2 of
Benaych-Georges, Bordenave and Knowles on the spectral norm of sparse random matrices
([`BBKTheorem3_2`](Challenge.lean#L228)), and Theorem 6.10 of Boucheron, Lugosi and Massart (Talagrand's inequality,
[`BLMTheorem6_10`](Challenge.lean#L244)). **Three theorems of the sparse paper are false as printed** (Theorems 1.5, 1.7,
4.1); the formalization proves that they are false and proves corrected versions.

## What is proved

- Every result that the papers prove, by the papers' own arguments: the dense paper's Theorems 1.2,
  1.3, 1.5, 1.6, Lemmas 2.1–3.6 and Appendix A; the sparse paper's Theorems 1.2, 1.4, 1.5, 1.7, 3.1,
  4.1, its lemmas and propositions of Sections 2–4 and Appendix A. The corrected statements are
  explained in [REPORT.md](REPORT.md), Sections 4 and 6.
- The cited results they use, except the three above: Hoeffding's and Chernoff's inequalities, the
  bound `C(2m, m) < 4^m/√(2m)`, the entropy bound for binomial coefficients, and the theorem of Goles
  and Olivos that majority dynamics is eventually periodic with period at most two
  ([REPORT.md](REPORT.md), Section 2).
- `lake build` succeeds; the only `sorry`s are the statements of record in
  [`Challenge.lean`](Challenge.lean), and there is no `axiom`. `lake env lean scripts/Audit.lean`
  checks that every declaration of the library uses only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and
  [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound), and prints which cited results each paper result uses.

## The main results

The statements of record are in [`Challenge.lean`](Challenge.lean), in Mathlib's vocabulary with the
definitions they need ([`gnpProb`](Challenge.lean#L86) is the probability under Mathlib's `SimpleGraph.binomialRandom`;
`blueAfter G B₀ t` is the Blue set after `t` days; `Φ` is the standard normal distribution function,
identified with Mathlib's Gaussian law by [`Challenge.Φ_eq_cdf_gaussianReal`](Challenge.lean#L405)):

- [`Challenge.dense_theorem1_6`](Challenge.lean#L267): the explicit four-day bound of the dense paper, with failure
  probabilities `P₁, …, P₄`;
- [`Challenge.dense_theorem1_2`](Challenge.lean#L283): on `G(n, 1/2)` with `n ≥ 1000`, if Red has at least `n/2 + 5`
  vertices, Red wins after four days with probability at least 0.9;
- [`Challenge.dense_theorem1_3`](Challenge.lean#L289): for constant `p`, a lead of `c` wins after four days with probability
  at least `1 − K(p) max{1/n, 1/c²}`;
- [`Challenge.sparse_theorem1_2`](Challenge.lean#L295): if `n − 10 ≥ pn ≥ (1 + λ) log n` and `pΔ ≥ 10`, Red wins within
  `O(log n/log(pn))` days with probability at least `1 − O(1/min{n, pΔ²} + n^(−λ/2))`;
- [`Challenge.sparse_theorem1_4`](Challenge.lean#L307): with a uniformly random colouring and `p ≥ λ n^(−1/2)`, the larger
  side wins within `O(1)` days with probability at least `1 − ε` (a delayed form of the theorem of
  Fountoulakis, Kang and Makai);
- [`Challenge.sparse_theorem1_5`](Challenge.lean#L316): with a random colouring biased towards Red by
  `ω(max{(pn)⁻¹, n^(−1/2)})`, Red wins with probability `1 − o(1)`; the printed bias `ω((pn)⁻¹)` does
  not suffice ([`Challenge.sparse_theorem1_5_printed_false`](Challenge.lean#L326));
- [`Challenge.sparse_theorem3_1`](Challenge.lean#L335): below the connectivity threshold, `p = (1 − λ) log n/n`, the process
  ends in period at most two with few Blue vertices, of small average degree;
- [`Challenge.sparse_theorem1_7`](Challenge.lean#L352), [`Challenge.sparse_theorem4_1`](Challenge.lean#L364): with random activations and updates,
  Red wins provided its lead is at least of order `√(n/p_ac)`; without that hypothesis the printed
  theorems are false ([`Challenge.sparse_theorem1_7_printed_false_seq`](Challenge.lean#L378),
  [`Challenge.sparse_theorem4_1_printed_false_seq`](Challenge.lean#L390)).

## Palomar

The project is packaged for the [Palomar](https://palomar-registry.org) registry:
[`Challenge.lean`](Challenge.lean) holds the statements of record, [`Solution.lean`](Solution.lean)
restates them word for word and proves them from the library, and [`comparator.json`](comparator.json)
configures Comparator, which checks that the solution proves exactly the challenge with the standard
axioms:

```sh
lake build
lake env lake comparator --config=comparator.json   # needs bubblewrap; prints "Your solution is okay!"
```

The metadata is in [`formalization.yaml`](formalization.yaml).

## Audit summary

[REPORT.md](REPORT.md) audits both papers against the formalization; every finding was checked against
the TeX sources by a second reader.

- **Errors.** The sparse paper's Theorem 1.5 needs a bias `ω(n^(−1/2))` (E13); its Theorems 1.7 and 4.1
  need an initial gap of order `√(n/p_ac)`, which their proof assumes, so the power of few is not
  robust under random activations, contrary to the abstract (E14). The dense paper's proof of Theorem
  1.2 has `P₁ ≤ .0902` where the value is .0962 (the theorem holds, E4), its proof of Theorem 1.3 has a
  factor 4 for 8 (E5), and its Lemma 3.5 states a bound that its proof gives only for `n ≥ 1288` (E2).
  The sparse paper's variance bound `7n/12` (Proposition 2.2) is not proved for `p ≠ 1/2` (E15).
- **Gaps.** The near-complete case `p > 1 − 10/n` is missing from the deductions from the sparse
  Theorem 1.2 (E1); further gaps in E3–E26 are repaired along the papers' lines.
- **Missing hypotheses:** the corrected sparse Theorems 1.5, 1.7, 4.1. **Redundant hypotheses:** six,
  in the report's Section 5.
- **Cited results.** The sparse paper quotes its Lemma A.3 with a bound too small by a factor
  `2(1 − 2σ²)`, which leaves `7n/12` unproved (E15); its other loose citations (Lemma A.3 outside its
  hypotheses, Lemma 2.6 for part of its proof, Lemma A.4 without a concentration step,
  Benaych-Georges–Bordenave–Knowles with a different normalization; E15, E23, E24, E26) do not affect
  the results.
- **Proofs.** Every proof follows its paper's argument; nineteen depart from it at one or more steps
  (eighteen departures), each to repair a step that is wrong or has a gap (the report's Section 7). The route check
  ([`scripts/route_check.py`](scripts/route_check.py)) confirms that each proof uses the results its paper's proof cites.

## Credits

- Formalized with Claude Code (model Claude Opus 5.5), at the request of The-Anh Vu-Le, following the
  [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure: statements first,
  reviewed by an independent agent; proofs by parallel sub-agents, each comparing its proof with the
  paper; independent reviews of the proofs, of the findings and of the literature.
- No person has reviewed the proofs.
- Made on 2026-10-17 in 6.2 hours, with 34 sub-agents (at most 17 at once).
  [CREDITS.md](CREDITS.md) has the procedure, the agents and the figures.

## Related work

- The question goes back to Benjamini, Chan, O'Donnell, Tamuz and Tan, whose conjecture
  Fountoulakis, Kang and Makai proved (2019); Berkowitz–Devlin and Sah–Sawhney sharpened the dense
  results, and Kim–Tran, Jaffe and Goel–Sah (preprints) extend the sparse ones
  ([REPORT.md](REPORT.md), Section 10).
- No erratum of either paper, and no earlier report of the three false statements, was found;
  B. Tran's 2025 thesis restates the sparse Theorems 1.7 and 4.1 unchanged, and Jaffe's 2025
  preprint repeats the error of the sparse Theorem 1.5 in its Theorem 3.2.
- No earlier formalization of these papers exists. The Lean formalization of Goel and Sah's
  theorem ([gopalkgoel/sparse-majority-dynamics-lean](https://github.com/gopalkgoel/sparse-majority-dynamics-lean))
  also proves the theorem of Fountoulakis, Kang and Makai, which these papers re-derive in delayed form;
  this project did not consult it.

## What's next

With random activations, the natural question is the exact threshold for the initial gap, which the
corrected theorems put at order `√(n/p_ac)`; the papers' own conjectures on the optimal advantage and
on the regime below connectivity remain open. The three assumed results are the formalization's own
next step: the spectral bound could come from the Feige–Ofek argument. See [REPORT.md](REPORT.md),
Section 11, and, for papers that could follow, [`NEXT.md`](NEXT.md).

## Building

```sh
lake exe cache get        # Mathlib's compiled files
lake build                # the library, the Challenge and the Solution
lake env lean scripts/Audit.lean                       # axioms and dependencies of every result
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
```

The toolchain is `leanprover/lean4:v4.36.0-rc1` with Mathlib `v4.36.0-rc1`. [`Challenge.lean`](Challenge.lean) carries
a copy of the shared definitions of [`PowerOfFew/Defs.lean`](PowerOfFew/Defs.lean); after editing them,
run `python3 scripts/sync_challenge_defs.py` (CI runs it with `--check`). After `lake build`,
`python3 scripts/linkify_docs.py` updates the documents' links to the code.

## Layout

| Module | Contents |
| --- | --- |
| [`PowerOfFew/Defs.lean`](PowerOfFew/Defs.lean) | the shared definitions: `G(n, p)`, majority dynamics, random colourings, the activation model, `Φ`, the dense paper's `F`, `P₁, …, P₄`, and the three assumed results |
| [`PowerOfFew/Model/`](PowerOfFew/Model) | `G(n, p)` as independent edge variables and its probability rules (`Gnp`), conditioning on one edge (`EdgeConditioning`), majority dynamics (`Majority`), `Φ` (`Normal`), Berry–Esseen for signed Bernoulli sums (`BerryEsseen`), the activation model (`Lazy`) |
| [`PowerOfFew/Dense/`](PowerOfFew/Dense) | `BinomialDifference` (Lemmas 2.3, 2.4), `DayOne` (Claims 2.5, 2.6, Lemma 2.1), `Shrinking` (Lemmas 3.2–3.6), `Main` (Theorems 1.6, 1.2, 1.3), `Appendix` (Theorem 1.5, Appendix A) |
| [`PowerOfFew/Sparse/`](PowerOfFew/Sparse) | `BerryEsseen` (Corollary A.2, Lemma A.3), `DayOne` (Proposition 2.2, Lemma 2.1), `DayTwo` (Lemmas 2.3, 2.4), `DayThree` (Lemmas 2.5, 2.6), `Main` (Theorem 1.2), `Degrees` (Lemmas A.4, A.5), `Chernoff` (Lemma A.6), `MatrixNorm` (Lemma A.7), `Subconnectivity` (Theorem 3.1), `ColoringAux` and `RandomColoring` (Theorems 1.4, 1.5), `ActivationDayOne`, `ActivationShrinking`, `ActivationLastDays` (Propositions 4.2–4.4), `Activation` (Theorems 4.1, 1.7), `ActivationCounterexample` (the printed Theorems 1.7, 4.1 are false) |
| [`PowerOfFew/External/`](PowerOfFew/External) | one directory per cited result, with a README: `BerryEsseen`, `RandomMatrix` (assumed); `Hoeffding`, `Chernoff`, `Invitation`, `GolesOlivos` (proved) |
| [`Basic/`](Basic) | general mathematics, importing only Mathlib: Bernoulli families, Chebyshev, Hoeffding and Chernoff bounds, binomial coefficients, two elementary inequalities ([`Basic/README.md`](Basic/README.md)) |
| [`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean), [`comparator.json`](comparator.json) | the statements of record and their proofs, for Comparator |
| [`scripts/`](scripts) | `Audit.lean`, the route check, the copy of the shared definitions, the documents' links and tables |
| [`docs/`](docs) | `paper_routes.tsv` (the results each paper proof cites), `route_differences.tsv` (the recorded differences) |

## GitHub configuration

[`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml) builds the project on
every push and pull request, checks that the audit imports every module, runs the audit and the route
check, and checks the Challenge's copy of the shared definitions, the documents' links and the
Markdown tables. It needs no settings.

## License

[Apache-2.0](LICENSE).
