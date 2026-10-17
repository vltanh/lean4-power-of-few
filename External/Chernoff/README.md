# Chernoff bounds for binomial variables (proved)

**Sources.** The sparse paper uses "a Chernoff bound" without citation: the lower tail in
relative-entropy form `P(Bin(m, p) ≤ am) ≤ exp(−m D(a ‖ p))` (proof of Lemma A.4, and in the proof
of Lemma A.5), and the bounds `P(Z ≥ T) ≤ exp(−(T − pm)²/(2T))` for `T > pm` and
`P(Z ≤ T) ≤ exp(−(pm − T)²/(2pm))` for `T < pm` (proof of Lemma A.6, equations (29) and (30)).

**In the formalization.** `Basic/Probability/Chernoff.lean`:
`ProbabilityTheory.IsBernoulliFamily.measureReal_sum_le_le_exp_klBern`,
`…measureReal_sum_ge_le_exp` and `…measureReal_sum_le_le_exp`, for sums of a Bernoulli family.
The same file proves `P(Z ≥ k) ≤ (e p m / k)^k` (`…measureReal_sum_ge_le_exp_mul_log`), which Feige
and Ofek's argument uses ([`../FeigeOfek/`](../FeigeOfek/README.md)).
