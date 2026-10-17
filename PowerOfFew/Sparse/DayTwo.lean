module

public import PowerOfFew.Model.Gnp
public import PowerOfFew.Model.Majority
public import Basic.Combinatorics.Choose
public import Basic.Analysis.SpecialFunctions.CubeRoot

/-!
# Sparse paper, Section 2.3: Step 2, the second day

Lemmas 2.3 and 2.4 of the sparse paper.

Corrections and deviations (recorded in `REPORT.md`):

* The paper defines `F(d, x, y) = dx(1 − y/2 − (3/2) y^(1/3)(1 − y)^(2/3)) + 2h(x)`, but its proof
  of Lemma 2.3 ends with `2h` of the *source* fraction (the second argument), and Lemma 2.4
  expands `F(pn, b, b₁)` with `2h(b₁)`. The definition here, `F d x y = … + 2 h y`, is that
  reading (an obvious misprint).
* Lemma 2.3 assumes `b₁ ≤ 1/2 − 7/n`, but its proof uses `b₁ ≤ 1/2 − 2/√n` ("by hypothesis") and
  `n` large enough (`n ≥ 163` makes its case `x < 1/9` work). The statement takes those
  hypotheses; Lemma 2.4 inherits them as `2√p ≤ a` and `b ≤ b₁` (decision of the user: state the
  hypotheses the paper's argument uses).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- `h(x) = x log x + (1 − x) log(1 − x)` (sparse paper, equation (5)). -/
def h (x : ℝ) : ℝ := x * Real.log x + (1 - x) * Real.log (1 - x)

/-- `F(d, x, y) = d x (1 − y/2 − (3/2) y^(1/3) (1 − y)^(2/3)) + 2 h(y)`: the paper's equation (6),
with `2h(y)` (the source fraction) in place of the printed `2h(x)`, as its proof and Lemma 2.4
use. -/
def F (d x y : ℝ) : ℝ :=
  d * x * (1 - y / 2 - 3 / 2 * y ^ (1 / 3 : ℝ) * (1 - y) ^ (2 / 3 : ℝ)) + 2 * h y

/-- **Lemma 2.3** (`S:lem:hypo-blue-bound`). For `0 < b₂ ≤ b₁ ≤ 1/2 − 2/√n` and `n ≥ 163`,
`G ∼ G(n, p)` is such that for every colouring with at most `b₁ n` Blue vertices, at most `b₂ n`
vertices are Blue the next day, except with probability at most `b₂⁻¹ exp(−n F(pn, b₂, b₁))`.

Deviation: the printed hypothesis is `0 ≤ b₂ ≤ b₁ ≤ 1/2 − 7/n` with no condition on `n`; see the
module docstring. `b₂ > 0` because the bound divides by `b₂`. -/
theorem lemma2_3 {n : ℕ} (hn : 163 ≤ n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {b₁ b₂ : ℝ}
    (hb₂ : 0 < b₂) (hb : b₂ ≤ b₁) (hb₁ : b₁ ≤ 1 / 2 - 2 / Real.sqrt n) :
    1 - b₂⁻¹ * Real.exp (-(n * F (p * n) b₂ b₁)) ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
      (B.ncard : ℝ) ≤ b₁ * n → ((majorityStep G B).ncard : ℝ) ≤ b₂ * n) := by
  sorry

/-- **Lemma 2.4** (`S:lem:step2`). For `a > 0` and `b ∈ (0, 1/2)` with `b a² > 3 (log 2) / 2`: if
`|B₁| ≤ n/2 − a n / √(pn)`, then `|B₂| ≤ b n` with probability at least `1 − e^(−Ω(n))`, whichever
vertices are Blue on day 1.

Reading: `e^(−Ω(n))` is `exp(−κ n)` for some `κ > 0` depending on `a` and `b`, for `n` large.
Deviation (hypotheses of Lemma 2.3 as its proof uses them): `2√p ≤ a`, so that
`b₁ = 1/2 − a/√(pn) ≤ 1/2 − 2/√n`, and `b ≤ b₁`. -/
theorem lemma2_4 {a b : ℝ} (ha : 0 < a) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hab : 3 * Real.log 2 / 2 < b * a ^ 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ p : ℝ, 0 < p → p < 1 → 2 * Real.sqrt p ≤ a →
      b ≤ 1 / 2 - a / Real.sqrt (p * n) →
      1 - Real.exp (-(κ * n)) ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
        (B.ncard : ℝ) ≤ n / 2 - a * n / Real.sqrt (p * n) →
          ((majorityStep G B).ncard : ℝ) ≤ b * n) := by
  sorry

end PowerOfFew.Sparse

end
