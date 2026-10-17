module

public import PowerOfFew.External.FeigeOfek.Defs
public import PowerOfFew.Model.Gnp
public import Basic.Probability.WeightedBernoulli
public import Basic.Analysis.GridNet

/-!
# Feige and Ofek's bound for the light pairs

For `x, y` in the grid net, the light part of `xᵀ (A − E A) y` (the pairs `u ≠ v` with
`|xᵤ y_v| ≤ √d / n`, `d = pn`) is a weighted sum `∑ a_{uv} (X_{uv} − p)`, over the unordered
pairs `{u, v}`, of the independent edge indicators `X_{uv}`, with
`a_{uv} = xᵤ y_v [(u, v) light] + x_v yᵤ [(v, u) light]`, so
`|a_{uv}| ≤ 2√d / n` and `∑ a_{uv}² ≤ 2`. The exponential-moment bound with `θ = n / (2√d)`
(`IsBernoulliFamily.integral_exp_mul_sum_le`) gives `P(|light| > 21 √d) ≤ 2 e^(−10 n)`, and the net
has at most `(33 e)ⁿ ≤ e^(4.5 n)` points, so a union bound over the pairs of points gives the
bound below (Feige–Ofek 2005, Section 2.2; Chin–Rao–Vu 2015, the light pairs).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.FeigeOfek

/-- **Feige–Ofek, the light pairs.** With probability at least `1 − 2e^(−n)`, every pair `x, y` of
points of the grid net satisfies `|lightSum G p (pn) x y| ≤ 21 √(pn)`. -/
theorem lightSum_le {n : ℕ} {p : ℝ} (hn : 1 ≤ n) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    gnpProb n p (fun G => ∃ x ∈ gridNet n, ∃ y ∈ gridNet n,
      21 * Real.sqrt (p * n) < |lightSum G p (p * n) x y|) ≤ 2 * Real.exp (-n) := by
  sorry

end PowerOfFew.FeigeOfek
