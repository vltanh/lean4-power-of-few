# Follow-up papers to L. Tran and V. Vu, *Reaching a consensus on random networks: the power of few*, and B. Tran and V. Vu, *The "power of few" phenomenon: the sparse case*

Directions for papers that could follow the formalization, explored far enough to judge whether
each is worth pursuing. Written 2026-10-17; literature searched 2026-10-17, twice and independently.
The working files cited below, in `notes/next/` (research notes, simulations, scratch Lean files,
downloads), are not published.

DENSE = Theory of Computing 19 (2023) art. 6; SPARSE = arXiv:2302.05605v2 = RSA 66 (2025) e21260.
Numbering is SPARSE's arXiv v2 numbering (the balanced-start conjecture is **Conjecture 1.13**, the
giant-component conjecture **Conjecture 1.15**; the research notes call them 1.12 and 1.13).

**Labels.** **[P✓]** proved on paper and checked line by line by a second reader. **[P✓ + fix]**
the same, after the routine repair stated. **[P, sketch]** proved in outline only. **[Lean,
scratch]** checked in a scratch Lean file in `notes/next/lean/` (outside the library; standard axioms
only). **[N: …]** checked numerically, with what and how far. **[H]** heuristic. **[C]** conjectured.

## Summary

1. **A. Random activations destroy the power of few — pursue with changes.** In SPARSE's model with
   random activations (§1.5, §4), for a fixed activation rate `p_ac < 1`, the winner is decided by
   the random colour balance of the vertices active on the first day, not by the initial lead: the
   target is `P(Red wins) → Φ(2Δ√(p_ac/((1 − p_ac)n)))` uniformly in `Δ`, so a lead of order `√n`
   is necessary and sufficient, whereas random *updates* alone are harmless. It settles the
   optimality of the corrected Theorems 1.7/4.1, which the formalization found false as printed
   (REPORT E14). For `p√n → ∞` this is proved on paper from SPARSE's own machinery (a conditioned
   first day, then Propositions 4.3/4.4, now proved in Lean) and checked by a second reader, so
   that part is a corrigendum or a short note, not a paper. The paper is the regime `p ≪ n^(−1/2)`,
   where SPARSE's union bound cannot start; the concrete target is a Kim–Tran/Jaffe-type
   second-day analysis of the activation dynamics (`p ≥ n^(−2/3+o(1))`), for which nobody has an
   argument yet. Simulations agree with the limit law within 1–2 standard errors in the proved
   range. Novelty is clear (B. Tran's 2025 thesis restates the false theorems). Main risk: the
   second-day method comes from Kim–Tran and Jaffe, who are well placed to extend it.
2. **B. Who survives below the connectivity threshold — pursue (a short paper).** For `pn = d`
   constant and a minority fraction `b < 1/2`, the minority surviving in the giant component is of
   order `d³e^(−2d)n` for `d ≥ d₀(b)`, which answers SPARSE Conjecture 1.15 with `a = 2` in its
   non-uniform form; at `pn = (1 − λ) log n` the survivors are the initially minority isolated
   vertices up to `n^(2λ−1+o(1))`, which removes the `(log n)^(O(√log n))` loss of SPARSE
   Theorem 3.1. The new ingredient — the final colour classes are self-supporting, and a
   first-moment count of small self-supporting sets — is proved on paper, checked by a second
   reader after two repairs, and its two structural lemmas are checked in Lean. Simulations at
   `n = 10⁶` (two independent simulators) show `|survivors|/(d³e^(−2d)·|initial|)` flat for
   `d = 6–10`. Limits: the proven range `d ≥ d₀(b) ≈ 4/(1 − 2b)` (≈ 18 at `b = 0.3`) is far above
   the simulated one, and the conjecture's uniformity in the minority fraction is out of reach and
   probably false. A modest short paper (EJC/CPC, or an RSA note).

Set aside: **E** (where consensus starts; no theorem in sight — its elementary remarks went to the
report's Section 11, its numerics stay here), **C** (`k ≥ 3` opinions; the theorem in reach is
routine, the limit law needs enumeration machinery), **D** (Conjecture 1.11 in
`N^(−1+ε) ≤ p ≤ (log N)^(−1/16)`; the most valuable target, out of reach here), and fourteen smaller
ideas (last section).

## 1. Random activations destroy the power of few: the √n threshold

**Target.** SPARSE's model: on day `t + 1` each vertex is active with probability `p_ac`, active
vertices observe their active neighbours, each active vertex updates with probability `p_up`, and
an updating vertex adopts the majority it observes (ties keep its colour). Fix `p_ac ∈ (0, 1)`,
`p_up ∈ (0, 1]`, `λ > 0`, `δ ∈ (0, 1)`; let `p ≤ 1 − δ` with `p p_ac n ≥ (1 + λ) log n` and
`|R₀| = n/2 + Δ`.

- **Theorem A.** Uniformly over `Δ ∈ ℤ`, `P(Red unanimity within A log n days) =
  Φ(2Δ√(p_ac/((1 − p_ac)n))) + o(1)`, and the same for Blue with `−Δ`, `A = A(p_ac, p_up, λ)`.
  Proved on paper for `p√n → ∞` [P✓]. The paper's target: the same for `p ≥ n^(−2/3+o(1))`.
- **Theorem A′ (updates only).** For `p_ac = 1` the printed Theorem 1.7 holds (with
  `(1 − p)n ≥ 10`): a lead `pΔ ≥ C` suffices [P✓ + fix, in the for-every-ε form].
- **Theorem A″ (crossover).** For `p_ac = 1 − η`, `η = η(n) → 0` with `p√(ηn) → ∞`:
  `P(Red wins) = Φ(2Δ/√(ηn)) + o(1)`, uniformly in `Δ` [P, sketch + a uniformity gap]. So for
  constant `p` any number `ηn → ∞` of inactive vertices per day destroys the power of few.
- **Conjecture A [C].** Theorem A for every `p` with `p p_ac n ≥ (1 + λ) log n`; in the dense case
  with `ηn = O(1)`, `P(Red wins) → Φ(2κΔ/√(1 + κ²ηn))`, `κ = √(2p/(π(1 − p)))` (at `η = 0` the
  Sah–Sawhney limit).
- **Fallback (a note).** Theorem A for `p√n → ∞`, A′, A″, the failure of the printed theorems for
  every `p` with `p√n → ∞`, and the numerics. This is corrigendum-level: it could also go into the
  formalization's report, or to the paper's authors as a corrigendum.
- **Ambitious.** A Goel–Sah-type analysis for `p ≥ n^(−1+ε)`.

**Why it matters.** SPARSE's abstract and §1.5 claim that the power of few "is robust" under random
activations and suggest (S:509–510) that Conjecture 1.11 "will also be robust in this more general
model". The formalization disproved the theorems at `p = 1` (REPORT E14); Theorem A shows that they
fail for every `p` with `p√n → ∞`, gives the exact law, and so shows that the corrected theorems'
lead `√(n/p_ac)` is optimal there. It also isolates a clean dichotomy: update noise is independent
across vertices and adds only `O(√n)` to the first-day count, while activation noise shifts the
count seen by every updating vertex by the same amount (the active set's colour balance, `Δ ± √n`),
and the first day multiplies this common shift by about `√(pn)` [H]. Readers: random graphs and
opinion dynamics (RSA, CPC). It does not answer a question posed by Dumitriu–Ju–Wang: their §5
(arXiv:2608.06159) is a general invitation to study other interaction mechanisms.

**Novelty.** Searched 2026-10-17 by the explorer and again, with other sources and phrasings, by the
second reader: arXiv API (≈ 35 queries: random activation, partial participation, majority vote on
random graphs, `abs:"power of few"`, author searches), OpenAlex and Semantic Scholar citation lists
of both papers (SPARSE is cited by Mossel arXiv:2609.04468, Dumitriu–Ju–Wang arXiv:2608.06159,
Benjamini–Zakharov–Zhukovskii arXiv:2507.04714, Kim–Tran arXiv:2503.07447, Mohan–Prałat
arXiv:2309.04691), Google Scholar (blocked after a few pages), about 30 web searches (activation,
lazy, sleeping or abstaining voters; an erratum of Theorem 1.7), MathOverflow through the Stack
Exchange API (15 queries). Nothing states Theorem A or reports the error. B. Tran's Yale thesis
(2025), obtained through a Wayback Machine capture: its Theorems 1.17 and 6.1 restate SPARSE 1.7 and
4.1 unchanged, and its Proposition 6.2 keeps the hypothesis `p_ac^(1/2)Δ ≥ S_ε n^(1/2)`. History:
arXiv v1's first-day lemma had no `√n` hypothesis (its variance step drops the variance of the
conditional means given the active set); v2 added the hypothesis to Proposition 4.2 only. Near
misses: Dumitriu–Ju–Wang (a Gaussian winner law from resampling the graph every round, not from
activations), Tamir–Livshits–Shadmi arXiv:2104.04996 (complete graph, independent message loss,
which behaves like updates), Mohan–Prałat (asynchronous updates). Residual risk: no full-text search
succeeded, and the typeset RSA version could not be read (v2 carries the referee-response edits, so
it is very likely the accepted text). The formalization's report (E14 and Section 11) and this file
make the error and the question public.

**Where the paper's method stops.** SPARSE §4, like the proof of Theorem A, is a first-day approach.
After day 1 the lead is about `n√p·|D_A|/√n ≈ n√p` (`D_A` = colour sum of the day-1 active set).
Proposition 4.3 (Case 1) then applies Lemma 2.4 to `G[A₂]`, a union bound over all `2^|A₂|`
colourings, which needs `|B₁ ∩ A₂| ≤ |A₂|/2 − 2√(|A₂|/p)`: a Chernoff exponent `≈ (2/3)pL²` against
an entropy `2n log 2` needs a lead `L ≳ 1.4√(n/p)`, and `n√p ≥ √(n/p)` iff `p√n ≥ 1`. In the Lean
library this is the hypothesis of [`proposition4_3`] that the day-1 Blue set satisfies
`|B₁| ≤ n/2 − K√(n/(p p_ac))`. Below `n^(−1/2)` the state after day 1 is where the static model from a
random balanced colouring is after its day 1 (lead `≍ n√p`), except that the colouring is correlated
with `G[A₁]` rather than with `G` [H]; the static literature crossed this barrier only with
typical-colouring analyses (Kim–Tran: `p ≫ n^(−2/3) log^(2/3) n`; Jaffe: `p ≥ λn^(−2/3)`; Goel–Sah:
`p ≥ n^(−1+ε)`).

**Ideas to get past it.**
- *A second-day approach for the activation dynamics* (Chakraborti–Kim–Lee–Tran, Kim–Tran):
  condition on the day-1 and day-2 coins `(A₁, U₁, A₂, U₂)` and analyse day 2 directly. The day-2
  lead should be about `(day-1 lead)·q√(p p_ac n) ≈ n p√n` (`q = p_up p_ac`), and Lemma 2.4 can
  start on day 3 once `n p√n ≥ C√(n/p)`, i.e. `p ≥ Cn^(−2/3)`: **target `p ≥ Cn^(−2/3)(log n)^(O(1))`**
  [H]. A third-day approach (Kim–Tran's two typical days) would reach `p ≥ n^(−3/4+ε)` [H]. First
  check: which independence Kim–Tran use on day 2 (they condition on the first-day colours of a
  vertex set and on a subgraph); here day 1 changes the colours of `U₁` only.
- *Fresh activation randomness.* On day 2 an updating vertex sees only `A₂ ∩ N(v)`; the day-1
  colours of `A₂ ∖ U₁` are day-0 colours, independent of `G`, and the graph-dependent part enters
  only through edges inside `A₁`. A two-round exposure (first the edges at `U₁`) might give a clean
  second-day Chebyshev bound [H].
- *Small `p_ac`.* As `p_ac → 0` with `p p_ac n` fixed, the active subgraphs of different days
  overlap little and the process approaches the resampled-graph model of Dumitriu–Ju–Wang, where the
  Gaussian law is proved; a coupling might prove Conjecture A for small `p_ac` [H].
- None of these has been tried beyond the arithmetic. What makes them non-routine: the static
  proofs expose `G` day by day for synchronous updates on one graph, while here each day uses a
  fresh active set on the same `G`, and non-updating vertices keep stale colours.

**What was done here.**
- *Lemma A.1 (conditioned first day)* [P✓]: given the active set with `D_A ≥ η√n`, SPARSE Lemma 2.1
  on `G[A₁] ~ G(m, p)` and Chebyshev for the update coins give
  `|B₁| ≤ n/2 − γ·min{n, ηn√p}` with probability `1 − O(1/(pη²n)) − O(n^(−1/4))`, explicit
  `γ(p_ac, p_up)`. Written out in `notes/next/ideas.md`, Appendix P1. Remark: the `N` beyond which it
  holds is astronomical for small `η` (≈ `10^19` at `η = 0.1`); Hoeffding for the coin sums cuts the
  slack to `√(n log n)`.
- *Theorem A from Lemma A.1* [P✓] (Appendix P2): Berry–Esseen for `D_A`, the colour symmetry of the
  model, monotonicity in `B₀` (Lean `lazyBlueAfter_mono`), and the library's
  [`proposition4_3`]/[`proposition4_4`], whose statements do not involve `Δ` and so apply to a `B₁`
  that depends on `G`. Uses SPARSE Lemma 2.1 with the variance constant its argument gives
  (`varConst ≈ 1.50`, not `7/12`), and through Propositions 4.3/4.4 the assumed BBK/BLM results.
- *Theorem A′* [P✓ + fix] (Appendix P3), three slips repaired: use Hoeffding for the update coins
  (Chebyshev with `ω = (pΔ²)^(1/4)` costs `(pΔ²)^(−1/2)`); use `c = 2` in Lemma 2.1, as the library's
  Proposition 2.2 does (`c = 3` needs `p(1 − p)n ≥ 9`); the printed explicit error term needs
  Proposition 4.3 with `K ≍ pΔ` growing, which the paper's proof allows (`K ≤ 0.4√(p p_ac n)`) but the
  Lean statement does not (it fixes `K` first), so from the Lean statements only the for-every-ε form
  follows.
- *Theorem A″* [P, sketch]: `D_A = 2Δ − D_I` with `D_I` the inactive colour sum; the gap is
  uniformity as `p_ac → 1` (Lemma A.1 and the Lean Propositions 4.3/4.4 fix `p_ac` before `N`; their
  constants are monotone in `p_ac`, so routine, but not covered by the statements). Proved
  threshold: at least `√(ηn)` when `p√(ηn) → ∞`, at most `C·max{√(ηn), 1/p}`.
- *The printed Theorems 1.7/4.1 fail for every `p` with `p√n → ∞`* [P✓, given Theorem A]: take
  `C/p ≤ Δ ≪ √n` with `pΔ² → ∞`. [C] If Conjecture A holds, the printed error term also fails a
  little below `n^(−1/2)`.
- *Numerics* [N]. Explorer, ≈ 50 parameter points, 300–400 runs each (Python and C simulators,
  cross-validated): dense (`n = 4000`, `p = 1/2`) every point within 0.031 of the limit;
  `n = 2·10⁴`, `p = 0.02` (`p√n = 2.83`) within 0.045. Second reader, fresh seeds, `n = 2·10⁴`,
  `p = 0.05` (`p√n = 7.07`), `p_ac = 1/2`, 200 runs: 0.575, 0.720, 0.840 for `Δ = 20, 40, 70` against
  the limits 0.611, 0.714, 0.839 (within 1.1 s.e.; here `pΔ = 1, 2, 3.5`, so the win probability
  follows `Δ/√n`, not `pΔ`). Updates only (`p_ac = 1`, `p_up = 1/2`): Red won 98, 100, 100 of 100 runs
  at `pΔ = 0.5, 1, 2`. Below Theorem A's range (`p√n = 0.42` down to 0.06, `n` up to `2·10⁶`) the
  data lie between the limit and a one-day prediction; convergence cannot be seen at these sizes (the
  correction is `O((pn)^(−1/2))` [H]). Dense crossover (`n = 4000`, `p = 1/2`, `j = ηn` inactive
  vertices per day, 300 runs): a one-vertex lead wins with frequency 0.943 at `j = 0` (Sah–Sawhney
  limit 0.945) and 0.887, 0.800, 0.700, 0.633 at `j = 1, 4, 16, 64`; Conjecture A's crossover law fits
  within 0.035 for `j ≤ 64` and 0.054 (2 s.e.) at `j = 256`.
- *Files:* `notes/next/ideas.md` §3A, Appendix P1–P3, tables T1, T1b, T1c, T2;
  `notes/next/check.md` §2; `notes/next/sims/md_lazy.c`, `exp_activation.py`, `exp_lazy_fast.py`,
  `act_stats.py`; `notes/next/check/run_a.py`, `run_a1.sh` and `check/out/a_n2e4_p0.05.txt`,
  `a1_updates_only.txt`; raw logs `notes/next/out/activation_*`, `lazyfast_*`. No Lean statement of
  Theorem A yet.

**Risks and first milestone.**
- *Bar:* without the regime `p ≪ n^(−1/2)` it is a corrigendum; a referee will read the `p√n → ∞`
  part as "the proof of SPARSE §4 with a conditioned first day".
- *Competition:* the authors of the static second-day analyses (Kim–Tran, Jaffe) are well placed
  to adapt them.
- *Mathematics:* the second-day analysis may fail on the stale colours and fresh active sets.
- *First milestone:* the day-2 estimate — given `(A₁, U₁, A₂, U₂)`, a second-moment bound showing
  that the lead after day 2 is `≳ n p√n` with probability `1 − o(1)` when
  `p ≥ n^(−2/3)(log n)^C`. With it, Lemma 2.4 and the Lean Propositions 4.3/4.4 finish from day 3.
- *Cheap and useful first:* a scratch Lean file in `notes/next/` stating Lemma A.1 through
  `lazyProb`/`lazyBlueAfter` and proving Theorem A for `p√n → ∞` on top of the library, whose
  Lemma 2.1 and Propositions 4.3/4.4 are proved.

**Scale.** The `p√n → ∞` part: a note (≈ 10 pages; Electron. Commun. Probab., Statist. Probab.
Lett.) or a corrigendum. With `p ≥ n^(−2/3+o(1))`: a paper (RSA, CPC). With `p ≥ n^(−1+ε)`: a strong
RSA paper.

**Draft abstract.** *Tran and Vu showed that majority dynamics on G(n, p) reaches unanimity from an
initial lead of order 1/p, and stated that this "power of few" survives random activations and
updates. We show that random activations destroy it: if every vertex is active with a fixed
probability p_ac < 1 and observes only its active neighbours, then for p ≥ n^(−2/3+o(1)) [proved so
far for p√n → ∞] Red wins with probability Φ(2Δ√(p_ac/((1 − p_ac)n))) + o(1), uniformly in the
initial lead Δ, so a lead of order √n is necessary and sufficient. Random updates alone do not hurt,
and an inactivity rate η → 0 with p√(ηn) → ∞ moves the threshold to order √(ηn). Below n^(−1/2) the
proof is a second-day analysis of the dynamics, in which fresh active sets and stale colours replace
the synchronous updates of the static case.*

## 2. Who survives below the connectivity threshold: majority dynamics on G(n, d/n)

**Target.** `G ~ G(n, p)`, a fixed colouring with `|B₀| = ⌊bn⌋` (equivalently a uniformly random
one), `G*` the giant component, `t*` the first day with `B_(t*) = B_(t*−2)`.

- **Theorem B1 (SPARSE Conjecture 1.15 with `a = 2`, non-uniform).** For every `b ∈ (0, 1/2)` there
  is `d₀(b)` such that for every fixed `d ≥ d₀(b)` and `pn = d`, with high probability
  `(1 − o_d(1))·b²(1 + 2b(1 − b))·d³e^(−2d)n ≤ |B_(t*) ∩ G*| ≤ (1 + o_d(1))·d³e^(−2d)n`.
  Lower bound [P✓]; upper bound [P✓ + fix] with the crude polynomial `d⁹`, and the sharp `d³` from
  an exact count of two-vertex sets [P, sketch]. In the conjecture's ratio form:
  `|B_(t*) ∩ G*|/|B₀ ∩ G*|` is between `≈ b(1 + 2b(1 − b))d³e^(−2d)` (0.426·`d³e^(−2d)` at `b = 0.3`)
  and `≈ b⁻¹d³e^(−2d)`.
- **Theorem B2 (SPARSE Theorem 3.1, sharp).** For `p = (1 − λ) log n/n`, `λ ∈ (0, 1)`, and
  `pΔ ≥ 10`: with probability `1 − O(1/min{n, pΔ²}) − o(1)`,
  `|B_(t*) △ (B₀ ∩ Iso(G))| ≤ n^(2λ−1)(log n)^C`, where `Iso(G)` is the set of isolated vertices; for
  `λ < 1/2`, `B_(t*) = B₀ ∩ Iso(G)` [P✓, sketch]. Theorem 3.1 has `(log n)^(O(√log n)) n^λ`, and
  SPARSE's remark calls it optimal up to that factor.
- **Fallback.** B2 alone; or B1 with the crude polynomial.
- **Not targeted.** The uniform version (`a` and `P` independent of `ε` and `d`, as the conjecture
  asks): it fails if, at every `d`, the dynamics freezes near balance for a small enough bias
  [P, given that premise], which the numerics suggest but cannot establish [C].

**Why it matters.** It answers a conjecture posed in print (SPARSE Conjecture 1.15), with the
exponent and the polynomial, and closes the gap that SPARSE's remark after Theorem 3.1 leaves. The
self-supporting viewpoint connects majority dynamics below connectivity with zero-temperature
Glauber dynamics and defensive alliances.

**Novelty.** Searched 2026-10-17 by both agents (web, arXiv API, citation lists, MathOverflow):
final minority in the giant of `G(n, d/n)`, stable sets, pendant structures, defensive alliances and
internal partitions of sparse random graphs, majority bootstrap percolation, zero-temperature
Glauber dynamics on sparse graphs, `e^(−2c)`, degree-2 pairs, Galton–Watson thresholds. Nothing
addresses Conjecture 1.15 or small self-supporting sets of `G(n, c/n)`. Precedents for the method,
which a referee will cite: O. Häggström, Physica A 310 (2002) (zero-temperature Glauber dynamics on
`G(N, γ/N)`: first-moment counts of isolated frozen gadgets, residual energy `≥ γ⁵e^(−6γ)/256`);
Kanoria–Montanari's stable structures; Stefánsson–Vallier (majority bootstrap percolation on
`G(n, c/n)`); work on alliances and internal partitions (Harutyunyan; arXiv:1708.04162;
arXiv:2307.06453) treats large sets or dense graphs. B. Tran's thesis: Theorem 1.19 is SPARSE 3.1
with the same loss, and Conjecture 1.25 is SPARSE 1.15.

**Where the paper's method stops.** For `pn = d` constant nothing spectral survives:
`‖A − EA‖ ≍ √(log n/log log n) ≫ √d` (high-degree vertices) and the minimum degree is 0, so Lemma 2.6
is empty; Lemma 2.3 (the union bound) still works but stops at Blue density about `e^(−d/2)`, where
the entropy `2H(x)` of the choice of the Blue set matches the Chernoff gain `d·y`. For Theorem 3.1,
Lemma A.5 (average degree `≥ ε pn` on sets of size `≥ n^(λ+δ)`) fails for smaller sets, so the
halving stops at `n^(λ+δ)`, and the last step bounds only the average degree of `B_(t*)`, which
cannot separate isolated vertices from other low-degree ones. Deleting high-degree vertices restores
`‖A′ − EA′‖ = O(√d)`, but the shrinking inequality still stalls on sets of low-degree vertices,
which is where the survivors live [H].

**Ideas to get past it** (these worked):
- *Lemma B.1* [P✓; Lean, scratch]: if `(B, B′)` is the final 2-cycle (`B′ = M(B)`, `B = M(B′)`, `M`
  the majority map with ties kept), then `U = B ∪ B′` is self-supporting: `d_U(v) ≥ d(v)/2` for
  every `v ∈ U`. Each component of `G[U]` meeting `G*` has at least two vertices.
- *Lemma B.2* [P✓; Lean, scratch]: if `vw` is an edge with `d(v), d(w) ≤ 2` and both are Blue on
  some day, they stay Blue forever.
- *Lemma B.3 (first moment)* [P✓ + fix]: count connected sets `C` of `k` vertices with `k − 1 + j`
  internal edges (spanning trees times extra edges); self-support forces at most `2(k − 1 + j)` edges
  to the outside, an independent `Bin(k(n − k), d/n)`. So the vertices `W` in self-supporting sets
  of size `2 ≤ k ≤ e^(−d/4)n` number at most `C′nd⁹e^(−2d)` for `d ≥ d₀`. Repairs (second reader):
  for the terms `j > k` use the Poisson rate function, valid for `d ≥ d₁ ≈ 15`; for concentration let
  the cut-off `K = K(n) → ∞` slowly (second moment for `k ≤ K`, Markov beyond). Sharp polynomial
  [P, sketch]: the two-vertex self-supporting sets are exactly the edges with both degrees `≤ 2`, so
  `|W| ≤ (1 + o_d(1))nd³e^(−2d)`; the `k ≥ 3` sets contribute a relative `O(d¹¹e^(−d))` by the crude
  count.
- *Bulk step* [P✓ + fix]: from density `b` to `e^(−d/3)` by the exact day-1 Poisson density and
  SPARSE Lemma 2.3 iterated. It needs `d ≥ d₀(b)`: by the second reader's iteration [N]
  `d₀(b) = 18, 27, 47, 105, 202, 388` for `b = 0.3, 0.4, 0.45, 0.48, 0.49, 0.495`, i.e.
  `d₀(b) ≈ 4/(1 − 2b)`.
- *Conclusion*: at `t*`, `U` is self-supporting with `|U| ≤ 2e^(−d/3)n`, so `U ∩ G* ⊂ W` (upper
  bound); edges with both degrees 2 whose ends are Blue after day 1 survive (lower bound; the
  probability is `b²(1 + 2b(1 − b))`: both Blue on day 0, or one Blue and both outer neighbours
  Blue).
- *Not achieved:* any `d < d₀(b)`, or `d₀(b) ≍ log(1/(1 − 2b))` as the numerics suggest; that is
  the freezing question of E.

**What was done here.**
- Lemmas B.1, B.2 in `notes/next/lean/SelfSupport.lean` (`selfSupporting_of_two_cycle`,
  `edge_stays_blue`, `degree_le_two_mul_of_mem_majorityStep`, `mem_majorityStep_of_low_degree`;
  imports the library's `PowerOfFew.Model.Majority`), checked with `lake env lean`, standard axioms.
- Lemma B.3, the bulk step, the bounds and B2 on paper (`notes/next/ideas.md` §3B and Appendix P5;
  repairs and recomputations in `notes/next/check.md` §3). The second reader's corrections: the
  Chernoff day-1 bound `e^(−d(√(1−b)−√b)²)` is useless at moderate `d` (0.43 at `b = 0.3`, `d = 10`;
  use the exact Poisson mean, 0.090); reaching `e^(−d/3)` takes a number of days growing linearly in
  `d` (48, 21, 13 at `d = 18, 20, 30`), not `O(log d)`, which is harmless; the invariance of
  `e^(−d/3)` needs `d ≳ 17–20`; the leading constant is `b(1 + 2b(1 − b))`, twice the value in the
  research notes.
- Numerics [N], `n = 10⁶`, `b = 0.3`: `ratio/(d³e^(−2d)) = 0.77, 0.60, 0.64, 0.54, 0.65` for
  `d = 6, …, 10` (explorer, 10 runs per `d`) and `0.775, 0.672, 0.605, 0.661` for `d = 6, …, 9`
  (second reader's independent simulator, fresh seeds, 20 runs), flat while `e^(−2d)` falls by `e^(−8)`;
  1.3–1.8 times the leading term, explained by edges with degrees (1, 2) and a slower bulk at
  moderate `d`. 79–100% of the survivors lie on edges with both degrees `≤ 2`, in components of size
  2 (77–100%) or 3. At `d = 8` the ratio varies by a factor 1.9 between `b = 0.3` and `b = 0.49` (the
  leading constants predict 1.73). Freezing near balance: `b = 0.49` freezes at `d = 5` and not at
  `d = 6`; at `n = 10⁵` the ratio is 0.92–0.96 at `d = 4` for `b = 0.49–0.495`.
- *Files:* `notes/next/ideas.md` §3B, Appendix P4–P5, table T4; `notes/next/check.md` §3;
  `notes/next/sims/exp_static.py` (E5), `sims/md.py`; `notes/next/check/md_b.c`, `run_b.py`,
  `recompute.py`, `d0_scan.py`, `p5_jrange.py` and `check/out/`; raw logs `notes/next/out/e5_*`.

**Risks and first milestone.**
- *Bar:* the new ingredient is a one-line lemma plus standard first-moment counting, and a referee
  may call it folklore (each colour class of a stable configuration is a defensive alliance; the
  2-cycle version is a one-liner). The contribution is the answer to Conjecture 1.15 and the sharp
  Theorem 3.1.
- *Range:* `d₀(b) ≈ 4/(1 − 2b)` (≈ 18 at `b = 0.3`) lies far above the experiments (`d ≤ 10`); say so
  in the abstract.
- *Uniformity:* the conjecture asks for constants independent of `ε` and `d`; B1 is non-uniform and
  must say so.
- *First milestone:* Lemma B.3 written out in full with the sharp polynomial (the exact count of
  self-supporting pairs, the geometric bound for `k ≥ 3`, the rate-function bound for `j > k`, the
  `K(n)` concentration). Then B2, which is short, and the bulk step with an explicit `d₀(b)`.

**Scale.** A short paper (15–20 pages): Electron. J. Combin., Combin. Probab. Comput., or an RSA
note.

**Draft abstract.** *Below the connectivity threshold majority dynamics on G(n, p) cannot reach
unanimity, and Tran and Vu conjectured that for pn = d constant the minority surviving in the giant
component decays like e^(−ad) with a > 1. We prove this with a = 2 and the sharp polynomial factor:
for every minority fraction b < 1/2 and d ≥ d₀(b) the surviving minority in the giant has between
c_b d³e^(−2d)n and (1 + o_d(1)) d³e^(−2d)n vertices with high probability, and for
pn = (1 − λ) log n the survivors are, up to n^(2λ−1+o(1)) vertices, the initially minority isolated
vertices, which removes the (log n)^(O(√log n)) loss in their Theorem 3.1. The key observation is
that the final colour classes are self-supporting, and a first-moment count shows that the
self-supporting sets meeting the giant are, to leading order, edges whose endpoints have degree at
most two. Our constants depend on b, and we show that the conjectured uniform bound fails if the
dynamics freezes near balance at every d for a small enough bias, as simulations suggest.*

## Considered and set aside

- **E. Where consensus starts** (BCOTT Conjecture 1.5 against SPARSE Conjectures 1.11 and 1.13).
  Out of reach as a theorem: both directions need control over `≍ log n` days from a lead of order
  `√n`, which neither the union bound nor the spectral step gives. Its three elementary remarks
  (BCOTT's two parts are incompatible [P✓; Lean, scratch: `notes/next/lean/Diagonal.lean`]; `f = 0`
  on `(0, 1/2]` in Conjecture 1.13 [P✓]; Conjecture 1.11 forces `f = 1` on `(1, ∞)` [P✓]) are now in
  the report's Section 11. Recorded here: the numerics up to `n = 10⁷` (from an exactly balanced
  start the frequency of a near-balanced 2-cycle is nearly independent of `n` at fixed `pn/log n`,
  with its 50% point at `c ≈ 0.81–0.86`; planted-bias thresholds `θ*(d) ≈ 0.39e^(−0.63d)` for
  `d = 6–10`, with `θ*(d*(n))√n ≈ 0.3`; second reader's spot checks with fresh seeds agree), and
  Conjecture E [C]: a Poisson-tree threshold `θ*(d)` with `log(1/θ*(d)) ~ κd` and a transition at
  `pn = (1/(2κ)) log n ≈ 0.79 log n`. The claimed contradiction between the third part of Conjecture
  1.13 and BCOTT's second part is heuristic only (the two start from different colourings). Near
  miss: Pournaki–Olbrich–Banisch–Klemm, PRE 107 (2023) 054112 (asynchronous zero-temperature dynamics
  on `G(N, p)`, a critical degree growing like `log N`). A numerical note would need `n ≈ 10⁸` or a
  dynamic-cavity computation. Files: `ideas.md` §3E, P6–P7, tables T3, T5, T7, T10, T12;
  `check.md` §4.
- **C. Power of few with `k ≥ 3` opinions** (asked by Chellig–Fountoulakis, SPA 189 (2025) §5;
  promised by DENSE). The Tran–Vu-level theorem looks routine [H]: the first-day covariances keep
  the product form (Appendix P8 [P]). The Sah–Sawhney-level limit law (a Gaussian arg-max) would be
  the paper and needs the enumeration machinery. [N: `G(3000, 1/2)`, sizes (1001, 1000, 999): the
  largest wins 0.785 of 400 runs against a predicted 0.800.] Not checked by a second reader. Files:
  `ideas.md` §3C, P8, T6.
- **D. Conjecture 1.11 for `N^(−1+ε) ≤ p ≤ (log N)^(−1/16)`.** The most valuable target and out of
  reach here: it needs a local limit theorem for the day-1 state and Goel–Sah's faithfulness
  induction started from a Gaussian-perturbed state (they say so themselves); strong competition.
  [N: at `pn = 1.5 log n` the conjectured law fits within 0.035 for `n = 10⁴–10⁶`.] Files:
  `ideas.md` §3D, T8.
- **Incremental** (in the report's Section 11 where they bear on the papers): biased colourings (the
  exact threshold `n^(−1/2)` follows from Theorem 1.2 when `p√n → ∞`; below that it is the BCOTT
  problem); the time to unanimity; random regular graphs (the same proof with Friedman's bound);
  certified constants for the dense paper; the day-1 central limit theorem alone; the local gadgets of
  Conjecture 1.13 alone.
- **No question in print, or a different question:** inhomogeneous (Chung–Lu) graphs; static
  stochastic block models; asynchronous updates; zealots; noise sensitivity of the winner; random
  geometric graphs; adversarial placement (dynamic monopolies, a known line of work).
- **A paper about the formalization** (ITP/CPP): only if a reusable technique is wanted (the
  conditional treatment of cited results, the activation-model API); not developed.

## Where everything is

The working files, in `notes/next/`, are not published: `ideas.md` (the exploration, with
Appendix P of proofs and Appendix T of tables), `check.md` (the second reading), `sims/` and `out/`
(simulators and raw results), `check/` (the second reader's scripts and outputs), `lean/` (scratch
Lean files), `dl/` (downloads, one directory each, including B. Tran's thesis).

[`proposition4_3`]: PowerOfFew/Sparse/ActivationShrinking.lean
[`proposition4_4`]: PowerOfFew/Sparse/ActivationLastDays.lean
