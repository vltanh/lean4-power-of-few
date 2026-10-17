module

public import PowerOfFew.External.FeigeOfek.Defs
public import PowerOfFew.Model.Gnp
public import Basic.Probability.Chernoff
public import Basic.Combinatorics.Choose

/-!
# Bounded degrees and discrepancy of `G(n, p)`

For `pn ≥ c log n`, with probability at least `1 − n^(−a)`, every degree of `G(n, p)` is at most
`c₁ pn` and the discrepancy property holds (Feige–Ofek 2005, Section 2.2; Chin–Rao–Vu 2015, their
lemma on the degree and discrepancy properties):

* a degree is `Bin(n − 1, p)`, and `P(Bin(n − 1, p) ≥ c₁ pn) ≤ (e / c₁)^(c₁ pn) ≤ n^(−c₁ c log(c₁/e))`
  (`IsBernoulliFamily.measureReal_sum_ge_le_exp_mul_log`), then a union bound over the vertices;
* for sets `S, T` with `m = max(|S|, |T|) > n/e`, bounded degrees give
  `e(S, T) ≤ c₁ d min(|S|, |T|) ≤ c₁ e μ(S, T)`;
* for `m ≤ n/e`, `e(S, T)` is at most twice a `Bin(N, p)` variable with `N ≤ |S| |T|` (the edges
  with one end in `S` and the other in `T`), so `P(e(S, T) ≥ λ μ) ≤ (2e/λ)^(λμ/2)`; with `λ` the
  least value that violates both alternatives this is at most `exp(−(c₃/4) m log(n/m))`, while the
  number of pairs of sets of sizes `s, t ≤ m` is at most `(en/m)^(2m) ≤ exp(4 m log(n/m))`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.FeigeOfek

/-- **Bounded degrees and discrepancy.** For all `c, a > 0` there are constants `c₁ ≥ 0`, `c₂ ≥ e`
and `c₃ ≥ 0` such that for `n ≥ 2` and `pn ≥ c log n`, with probability at least `1 − n^(−a)`,
every degree of `G(n, p)` is at most `c₁ pn` and `G(n, p)` has the discrepancy property with
constants `c₂, c₃` and expected degree `pn`. -/
theorem exists_degreeBound_discrepancy {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ∃ c₁ c₂ c₃ : ℝ, 0 ≤ c₁ ∧ Real.exp 1 ≤ c₂ ∧ 0 ≤ c₃ ∧
      ∀ (n : ℕ) (p : ℝ), 2 ≤ n → 0 < p → p ≤ 1 → c * Real.log n ≤ p * n →
        gnpProb n p (fun G => ¬ (DegreeBound G (p * n) c₁ ∧ Discrepancy G (p * n) c₂ c₃)) ≤
          (n : ℝ) ^ (-a) := by
  sorry

end PowerOfFew.FeigeOfek
