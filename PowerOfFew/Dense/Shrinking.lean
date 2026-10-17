module

public import PowerOfFew.Model.Gnp
public import PowerOfFew.Model.Majority
public import Basic.Probability.Concentration
public import Basic.Combinatorics.Choose

/-!
# Dense paper, Section 3: Day Two and after

Lemmas 3.2–3.6 of the dense paper (journal version). With high probability the graph shrinks
every Blue set below a threshold, whichever vertices are Blue ("shrinking arguments"), by
Hoeffding's inequality (the paper's Theorem 3.1, `ProbabilityTheory.measureReal_sum_ge_add_le_exp`
and `measureReal_sum_le_sub_le_exp`) and a union bound over all colourings.

Lemmas 3.3, 3.5 and 3.6 are Parts 4, 2 and 3 of Theorem 1.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Dense

/-- **Lemma 3.2** (`D:lem:binom-bound`). For integers `n ≥ 1` and `0 ≤ k ≤ n`,
`C(n, k) < 2ⁿ / √n`. -/
theorem lemma3_2 {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    (n.choose k : ℝ) < 2 ^ n / Real.sqrt n := by
  sorry

/-- **Lemma 3.3** (`D:prop:uni-large-linear-advantage`; Part 4 of Theorem 1.6). For `p ∈ (0, 1)`
and `n > 1`, with probability at least `1 − n exp(−(2/9) p² (n − 1)) = 1 − P₄(n, p)`, every vertex
of `G` has more than `(2/3) p (n − 1)` neighbours, so every Blue set of at most `(1/3) p (n − 1)`
vertices vanishes the next day. -/
theorem lemma3_3 {n : ℕ} (hn : 1 < n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    1 - denseP4 n p ≤ gnpProb n p (fun G => (∀ v, 2 / 3 * p * ((n : ℝ) - 1) < degree G v) ∧
      ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3 → majorityStep G B = ∅) := by
  sorry

/-- **Lemma 3.4** (`D:lem:uni-bad-set-bound`). Let `p ∈ (0, 1)` and `n, n₀ ∈ ℕ` with `n₀ < n/2`.
For every `m ≤ n`, with probability at least
`1 − (4ⁿ / n) exp(−2p² (n − 2n₀ − 1)² m / (n + m − 2))`, every Blue set of at most `n₀` vertices
has fewer than `m` Blue vertices the next day. -/
theorem lemma3_4 {n n₀ : ℕ} (hn₀ : (n₀ : ℝ) < n / 2) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {m : ℕ}
    (hm : m ≤ n) :
    1 - 4 ^ n / n * Real.exp (-(2 * p ^ 2 * ((n : ℝ) - 2 * n₀ - 1) ^ 2 * m / (n + m - 2))) ≤
      gnpProb n p (fun G => ∀ B : Set (Fin n), B.ncard ≤ n₀ → (majorityStep G B).ncard < m) := by
  sorry

/-- **Lemma 3.5** (`D:prop:uni-sqrt-advantage-ex`; Part 2 of Theorem 1.6). With probability at
least `1 − P₂(n)`, every Blue set of at most `n/2 − (0.8/p) √n` vertices has at most `0.4 n` Blue
vertices the next day.

Reading: the lemma prints the bound as `1 − n⁻¹ exp(−0.025 n) = 1 − P₂(n)`, and Theorem 1.6 prints
`P₂(n) = n⁻¹ exp(−(0.076 n − 1.38 √n))`; the proof computes `0.076 n − 1.83 √n`, which is
`denseP2`. The printed `0.025 n` bound follows for `n ≥ 1288` (`lemma3_5_printed`). -/
theorem lemma3_5 {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    1 - denseP2 n ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
      (B.ncard : ℝ) ≤ n / 2 - 0.8 / p * Real.sqrt n → ((majorityStep G B).ncard : ℝ) ≤ 0.4 * n) := by
  sorry

/-- The bound of Lemma 3.5 as printed in the lemma, `1 − n⁻¹ exp(−0.025 n)`, for `n ≥ 1288`, where
`0.025 n ≤ 0.076 n − 1.83 √n`. -/
theorem lemma3_5_printed {n : ℕ} (hn : 1288 ≤ n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    1 - (n : ℝ)⁻¹ * Real.exp (-(0.025 * n)) ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
      (B.ncard : ℝ) ≤ n / 2 - 0.8 / p * Real.sqrt n → ((majorityStep G B).ncard : ℝ) ≤ 0.4 * n) := by
  sorry

/-- **Lemma 3.6** (`D:prop:uni-linear-advantage`; Part 3 of Theorem 1.6). With probability at
least `1 − n⁻¹ exp(−0.02 n (p³ n − 80)) = 1 − P₃(n, p)`, every Blue set of at most `0.4 n` vertices
has at most `(1/3) p (n − 1)` Blue vertices the next day. -/
theorem lemma3_6 {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    1 - denseP3 n p ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
      (B.ncard : ℝ) ≤ 0.4 * n → ((majorityStep G B).ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3) := by
  sorry

end PowerOfFew.Dense

end
