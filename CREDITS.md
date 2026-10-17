# Credits

How this formalization was made, from the run log and the session transcripts.

## Who

- **Author and maintainer:** The-Anh Vu-Le, who asked for the formalization and chose its scope:
  the journal version of the dense paper; corrected versions of the three false theorems of the
  sparse paper, with Lean counterexamples to the printed ones; and the constants and hypotheses that
  the sparse paper's arguments give, where its printed ones are not proved (Lemma 2.1, Proposition
  2.2, Lemma 2.3). In a second round the author asked for Feige and Ofek's argument in place of two
  assumed results, for the publication, and for the layout of the skill's version 3.0.0.
- **Formalization:** Claude Code (VS Code extension; versions 2.1.283 at the start and 2.1.301 in the
  transcripts) with the model Claude Opus 5.5 (`claude-opus-5-5`), in one coordinating session with
  sub-agents. There was no earlier draft.
- **Procedure:** the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill
  (installed with `npx skills`; version `d82a98e1` at the start, updated during the first round to
  `04e714c7` at 08:09 CDT, which adds the list of follow-up papers, and to `e339f644` (version 3.0.0)
  at 10:43 CDT, which also makes [`External`](External) a library of its own; the first round kept the earlier
  layout, and the second round reorganized the project to version 3.0.0's).
- **Review:** no person has reviewed the proofs. Independent agents, which did not write what they
  checked, reviewed the statements against the TeX sources before any proof was written; compared
  every formal proof with the papers' proofs (three reviews); verified every finding of the audit
  against the TeX; verified the literature notes against their sources; checked the report; and, in
  the second round, compared the proof of Feige and Ofek's bound with the write-ups it follows.

## First formalization (2026-10-17)

How it was made:

- **Inventory and setup** (coordinator): the TeX sources of all versions of both papers, the
  journal version of the dense paper, the routes of the papers' proofs
  ([`docs/paper_routes.tsv`](docs/paper_routes.tsv)), the project on Lean and Mathlib `v4.36.0-rc1`, and three decisions of
  the user on the scope.
- **Statements** (coordinator): every definition and numbered result of both papers, the Challenge,
  then the independent review; the statements were fixed in the baseline commit `f8d2a90`.
- **Proofs:** prover sub-agents in two waves, each owning disjoint files and following the papers'
  proofs, the later ones in private copies of the project; each reported its departures from the
  paper, which the coordinator checked against the baseline statements and the TeX. Two provers
  were resumed after the reviews, to follow the paper more closely (the Chernoff step of the sparse
  Proposition 4.2, and the route of Proposition 4.4 through Lemma A.4).
- **Integration and checks** (coordinator): the statement diffs, the axiom audit, the route check,
  [`Solution.lean`](Solution.lean) and Comparator, and three cleanup rounds.
- **Audit:** the findings, verified by an independent agent against the TeX; the literature search
  and its independent verification; the report and its independent check.
- **Follow-up papers:** a research agent and a second reader ([`NEXT.md`](NEXT.md)). The second
  reader also obtained B. Tran's thesis; the coordinator checked it, and the sparse paper's arXiv v1,
  against the report and corrected its literature section (commit `b0d1f95`).

Figures, from 2026-10-17 07:09:52 CDT (UTC−05:00) to the commit that completes [`REPORT.md`](REPORT.md):

- **Elapsed time:** 6.2 hours (07:09:52 to 13:21:14 CDT on 2026-10-17), to commit `b0d1f95`.
- **Sub-agents:** 34 (26 launched by the coordinating session, 8 by sub-agents), at most 17
  running at once; their total working time was 20.4 hours. Two finished sub-agents were resumed.
- **Tool calls and tokens:** sub-agents 3,561 tool calls, 6.59M output tokens, 17.19M input tokens
  (uncached input and cache writes) and 848M cache reads; the coordinating session 586 tool calls,
  1.14M output tokens, 2.12M input tokens and 264M cache reads.
- **Model calls:** `claude-opus-5-5`, 539 by the coordinating session and 3,344 by sub-agents.

The figures come from the Claude Code transcripts of the session and its sub-agents
(`session_stats.py` of the skill, with `--until` at that commit). They include the sub-agents that
agents launched themselves, and the follow-up search. The user's three decisions at the start took
a few minutes; there were no other pauses. Spending in money was not tracked.

## Second round: Feige–Ofek, publication and the three libraries (2026-10-17)

At the author's request: the repository was published (GitHub, CI, Palomar's preflight) and later
renamed, [`NEXT.md`](NEXT.md) was made public, the sparse paper's Lemma A.7 was proved by Feige and Ofek's
argument, which removes two of the three assumed results, and the project was reorganized into
version 3.0.0's three libraries ([`Basic`](Basic), [`External`](External), [`PowerOfFew`](PowerOfFew)).

How it was made:

- **Statements** (coordinator): the interface theorems of Feige and Ofek's argument, with `sorry`
  proofs, and the removal of the two hypotheses from every statement (commit `611a33f`); then the
  results of [`External`](External) in their sources' terms, the edge-variable model in [`Basic`](Basic) and the bridges
  in the papers' library (commit `3b1f715`).
- **Proofs:** seven prover sub-agents for Feige and Ofek's argument and three for the
  reorganization, each in a private copy of the project and owning disjoint files.
- **Review:** an independent agent compared the formal proof of Feige and Ofek's bound with Chin,
  Rao and Vu's and Hoffman, Kahle and Paquette's write-ups. It found no mathematical problem; its
  documentation fixes were applied.
- **Integration and checks** (coordinator): the statement diffs, the build, the axiom audit, the
  route check, Comparator, and the report.

Figures, from 15:04:23 CDT (the author's go-ahead) to commit `a86a23a` (16:32:43 CDT), which
completes the round's [`REPORT.md`](REPORT.md):

- **Elapsed time:** 1.5 hours. Between the two rounds the session waited 1.6 hours for the author
  (13:25 to 15:04 CDT).
- **Sub-agents:** 11, all launched by the coordinating session, at most 7 running at once; their
  total working time was 2.3 hours. None was resumed.
- **Tool calls and tokens:** sub-agents 515 tool calls, 0.85M output tokens, 1.92M input tokens and
  60M cache reads; the coordinating session 213 tool calls, 0.36M output tokens, 0.90M input tokens
  and 134M cache reads.
- **Model calls:** `claude-opus-5-5`, 203 by the coordinating session and 449 by sub-agents.

The figures come from the same transcripts (`session_stats.py` with `--since` and `--until` at the
round's start and end).
