# The central binomial coefficient (proved)

**Source.** J. Matoušek, J. Nešetřil, *Invitation to Discrete Mathematics*, 2nd ed., Oxford (2009),
Proposition 2.6.2: `C(2m, m) ≤ 2^(2m) / √(2m)` for `m ≥ 1`. The dense paper cites it (as
`[invitation, 2.6.2 Proposition]`) for the even case of its Lemma 3.2.

**In the formalization.** `Nat.centralBinom_lt_four_pow_div_sqrt`
(`Basic/Combinatorics/Choose.lean`), with strict inequality, which is what Lemma 3.2 states.
