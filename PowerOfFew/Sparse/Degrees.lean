module

public import PowerOfFew.Model.Gnp
public import PowerOfFew.Model.Majority
public import Basic.Probability.Chernoff

/-!
# Sparse paper, Appendix A: degrees of `G(n, p)`

* Lemma A.4: above the connectivity threshold, the minimum degree is a constant fraction of `pn`.
* Lemma A.5: below it, every large set of vertices has a large average degree.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- **Lemma A.4** (`S:lem:degree-lower-bound`). Let `ε > 0`, `N_ε = 4/ε + 4` and
`α_ε = exp(−(8/ε + 7))`. With probability at least `1 − n^(−ε/2)`, a `G(n, p)` random graph with
`n ≥ N_ε` and `pn ≥ (1 + ε) log n` has minimum degree at least `α_ε p n`. -/
theorem lemmaA_4 {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 4 / ε + 4 ≤ n) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) (hpn : (1 + ε) * Real.log n ≤ p * n) :
    1 - (n : ℝ) ^ (-(ε / 2)) ≤
      gnpProb n p (fun G => ∀ v, Real.exp (-(8 / ε + 7)) * p * n ≤ degree G v) := by
  sorry

/-- **Lemma A.5** (`S:lem:subcon-avg-deg`). Consider `G(n, p)` with `p = (1 − λ) n⁻¹ log n`. For
`0 < δ < 1 − λ` and `0 < ε < 1` with `ε log(e/ε) ≤ δ/4`, with probability at least
`1 − n^(−δ n^(λ+δ) / 2)`, every set `U` of at least `n^(λ+δ)` vertices has average degree at least
`ε p n`.

Deviation (hypotheses the paper's proof uses): the proof neglects `O(·)` terms that are small only
for `n` large, and Theorem 3.1 applies the lemma with `δ` and `ε` depending on `n`. The statement
therefore holds for `n ≥ N(λ)`, uniformly in `δ ≤ (1 − λ)/2` and `ε`, provided `δ log n ≥ 8` (the
proof's last step needs `δ log n` bounded below). -/
theorem lemmaA_5 {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ δ ε : ℝ, 0 < δ → δ ≤ (1 - lam) / 2 → 8 ≤ δ * Real.log n → 0 < ε →
      ε < 1 → ε * Real.log (Real.exp 1 / ε) ≤ δ / 4 →
      1 - (n : ℝ) ^ (-(δ * (n : ℝ) ^ (lam + δ) / 2)) ≤
        gnpProb n ((1 - lam) * Real.log n / n) (fun G => ∀ U : Set (Fin n),
          (n : ℝ) ^ (lam + δ) ≤ U.ncard →
            ε * ((1 - lam) * Real.log n / n) * n * U.ncard ≤ ∑ᶠ u ∈ U, (degree G u : ℝ)) := by
  sorry

end PowerOfFew.Sparse

end
