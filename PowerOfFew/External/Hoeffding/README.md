# Hoeffding's inequality (proved)

**Source.** W. Hoeffding, *Probability inequalities for sums of bounded random variables*, JASA 58
(1963); cited by the dense paper as its Theorem 3.1 (with R. Vershynin's *High-Dimensional
Probability*, 2018).

**In the formalization.** `ProbabilityTheory.measureReal_sum_ge_add_le_exp` and
`ProbabilityTheory.measureReal_sum_le_sub_le_exp` (`Basic/Probability/Concentration.lean`), in the
paper's form `P(X ≥ E X + t), P(X ≤ E X − t) ≤ exp(−2t² / ∑ (bᵢ − aᵢ)²)`, derived from Mathlib's
sub-Gaussian Hoeffding inequality (`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`) and
Hoeffding's lemma (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`).
