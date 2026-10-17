module

public import PowerOfFew.Sparse.BerryEsseen
public import PowerOfFew.Model.Gnp
public import PowerOfFew.Model.Majority

/-!
# Sparse paper, Section 2.2: Step 1, the first day

Lemma 2.1 and Proposition 2.2 of the sparse paper, with the variance constant that the paper's
argument gives (a decision recorded in `REPORT.md`):

The proof of Proposition 2.2 quotes Lemma A.3 as `P(X = …) ≤ C_BE / √(p(1 − p)(n − 2))`, but
Lemma A.3 gives `2 C_BE (1 − 2σ²) / (σ √(n − 2))`. With that bound, the covariance of two
indicators is at most `4 C_BE² (1 − 2σ²)² / (n − 2)`, and
`Var|B₁| ≤ n (1/4 + 4 C_BE² (1 − 2σ²)² (n − 1)/(n − 2))` instead of `7n/12`; the two agree in
form at `p = 1/2`. `varConst n p` is this coefficient, and Lemma 2.1's constant
`C(c, D) = 7 / (12 (D_c − D)²)` becomes `varConst n p / (D_c − D)²`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- `D_c = Φ₀(2 − 1/c) − C_BE / c`, with `C_BE = 0.56` (sparse paper, equation (2)). -/
def Dc (c : ℝ) : ℝ := Φ₀ (2 - 1 / c) - 0.56 / c

/-- The variance coefficient that the argument of Proposition 2.2 gives:
`1/4 + 4 C_BE² (1 − 2σ²)² (n − 1)/(n − 2)`, `σ² = p(1 − p)`, `C_BE = 0.56`. -/
def varConst (n : ℕ) (p : ℝ) : ℝ :=
  1 / 4 + 4 * 0.56 ^ 2 * (1 - 2 * (p * (1 - p))) ^ 2 * (((n : ℝ) - 1) / ((n : ℝ) - 2))

/-- **Proposition 2.2** (`S:prop:day1-exp-var`), with the variance bound that its proof gives. For
`0 < c ≤ min{pΔ, √(p(1 − p)n)}` and `|B₀| ≤ n/2 − Δ`,
`E|B₁| ≤ n/2 − D_c min{n, Δ √(pn)}` and `Var|B₁| ≤ varConst n p · n` (printed: `7n/12`).

Deviation (hypothesis the proof uses): the proof sets `y = 2 − 1/c` and needs `y > 0`, so
`c > 1/2`; Lemma 2.1 only uses `c` with `D_c > 0`, which forces `c > 1/2`. -/
theorem proposition2_2 (hBE : ShevtsovaBerryEsseen) {n : ℕ} {p Δ c : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hc : 1 / 2 < c) (hcΔ : c ≤ p * Δ) (hcn : c ≤ Real.sqrt (p * (1 - p) * n))
    {B₀ : Set (Fin n)} (hB₀ : (B₀.ncard : ℝ) ≤ n / 2 - Δ) :
    gnpExp n p (fun G => ((blueAfter G B₀ 1).ncard : ℝ)) ≤
        n / 2 - Dc c * min (n : ℝ) (Δ * Real.sqrt (p * n)) ∧
      gnpVar n p (fun G => ((blueAfter G B₀ 1).ncard : ℝ)) ≤ varConst n p * n := by
  sorry

/-- **Lemma 2.1** (`S:lem:day1`), with the constant that its proof gives. For
`0 < c ≤ min{pΔ, √(p(1 − p)n)}` and `0 < D < D_c`, if `|B₀| ≤ n/2 − Δ` then
`P(|B₁| ≤ n/2 − D min{n, Δ √(pn)}) ≥ 1 − C'(c, D) / min{n, pΔ²}` with
`C'(c, D) = varConst n p / (D_c − D)²` (printed: `C(c, D) = 7 / (12 (D_c − D)²)`). -/
theorem lemma2_1 (hBE : ShevtsovaBerryEsseen) {n : ℕ} {p Δ c D : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hc : 0 < c) (hcΔ : c ≤ p * Δ) (hcn : c ≤ Real.sqrt (p * (1 - p) * n)) (hD : 0 < D)
    (hDc : D < Dc c) {B₀ : Set (Fin n)} (hB₀ : (B₀.ncard : ℝ) ≤ n / 2 - Δ) :
    1 - varConst n p / ((Dc c - D) ^ 2 * min (n : ℝ) (p * Δ ^ 2)) ≤
      gnpProb n p (fun G =>
        ((blueAfter G B₀ 1).ncard : ℝ) ≤ n / 2 - D * min (n : ℝ) (Δ * Real.sqrt (p * n))) := by
  sorry

end PowerOfFew.Sparse

end
