module

public import PowerOfFew.Dense.BinomialDifference
public import PowerOfFew.Model.Gnp
public import PowerOfFew.Model.Majority

/-!
# Dense paper, Section 2: Day One

Lemma 2.1 and Claims 2.5 and 2.6 of the dense paper (journal version): after the first day, the
Red camp has gained about `√n` vertices, by Chebyshev's inequality applied to `|R₁|`.

Notation: `σ = √(p(1 − p))`, so that `1 − 2σ² = 1 − 2p + 2p²`; `R₁ = (blueAfter G B₀ 1)ᶜ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Dense

/-- **Claim 2.5** (`D:claim:day-1-expection`). Under the hypotheses of Lemma 2.1,
`E|R₁| ≥ n/2 + F₁(n, p, c) √n`, where
`F₁(n, p, c) = √n Φ₀((2pc + min{p, 1 − p}) / (σ √n)) − 0.6 (1 − 2σ²) / σ`.

Reading: the paper also writes `F₁ = F(n, p, c) + 0.8 √n / p`; by the definitions,
`F₁ = F(n, p, c) + 0.8 / p`, which is what its Chebyshev step uses. -/
theorem claim2_5 (hBE : ShevtsovaBerryEsseen) {n c : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hF : 0 < denseF n p c) {B₀ : Set (Fin n)} (hB₀ : (B₀.ncard : ℝ) ≤ n / 2 - c) :
    (n : ℝ) / 2 + (Real.sqrt n * Φ₀ ((2 * p * c + min p (1 - p)) / Real.sqrt (p * (1 - p) * n)) -
        0.6 * (1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p))) * Real.sqrt n ≤
      gnpExp n p (fun G => ((blueAfter G B₀ 1)ᶜ.ncard : ℝ)) := by
  sorry

/-- **Claim 2.6** (`D:claim:day-1-covariance`).
`Var|R₁| ≤ 0.25 n + 0.7 (1 − 2σ²)² (n + 4c² / n)`.

Deviation (hypotheses the paper's computation uses, as for the sparse paper's Lemma 2.1): the
paper counts the pairs of vertices of the same initial colour as if `|R₀| = n/2 + c` and
`|B₀| = n/2 − c`, and bounds `1.2544/(n − 2) ≤ 1.4/n`, which needs `n ≥ 20`. The statement assumes
`|B₀| = ⌊n/2 − c⌋` (which also covers odd `n`) and `n ≥ 20`. Lemma 2.1, for every
`|B₀| ≤ n/2 − c`, reduces to this case by the monotonicity of majority dynamics. -/
theorem claim2_6 (hBE : ShevtsovaBerryEsseen) {n c : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 20 ≤ n) (hc : 0 < c) {B₀ : Set (Fin n)} (hB₀ : B₀.ncard = ⌊(n : ℝ) / 2 - c⌋₊) :
    gnpVar n p (fun G => ((blueAfter G B₀ 1)ᶜ.ncard : ℝ)) ≤
      0.25 * n + 0.7 * (1 - 2 * p + 2 * p ^ 2) ^ 2 * (n + 4 * (c : ℝ) ^ 2 / n) := by
  sorry

/-- **Lemma 2.1** (`D:lem:const-advantage-day-1`). Let `p ∈ (0, 1)` and `n, c ∈ ℕ` with
`F(n, p, c) > 0`. If `|B₀| ≤ n/2 − c`, then `P(|B₁| > n/2 − 0.8 √n / p) ≤ P₁(n, p, c)`. -/
theorem lemma2_1 (hBE : ShevtsovaBerryEsseen) {n c : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hF : 0 < denseF n p c) {B₀ : Set (Fin n)} (hB₀ : (B₀.ncard : ℝ) ≤ n / 2 - c) :
    gnpProb n p (fun G => (n : ℝ) / 2 - 0.8 * Real.sqrt n / p < (blueAfter G B₀ 1).ncard) ≤
      denseP1 n p c := by
  sorry

end PowerOfFew.Dense

end
