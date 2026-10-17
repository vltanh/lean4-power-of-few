module

public import PowerOfFew.Dense.DayOne
public import PowerOfFew.Dense.Shrinking
public import PowerOfFew.Model.Normal

/-!
# Dense paper: the main theorem and its corollaries

* `theorem1_6`: the main theorem, with the explicit bounds `P₁, …, P₄` (`denseP1`, …, `denseP4`).
* `theorem1_2`: the power of few: on `G(n, 1/2)` with `n ≥ 1000`, five extra Red vertices win
  after four days with probability at least `0.9`.
* `theorem1_3`: the asymptotic bound `1 − K(p) max{1/n, 1/c²}`.

Reading of Theorem 1.6, Parts 2–4: the paper writes them as conditional probabilities, for
example `P(|B₂| ≤ 0.4n | |B₁| ≤ n/2 − 0.8√n/p) ≥ 1 − P₂`, and proves them as Lemmas 3.5, 3.6 and
3.3, which it calls Parts 2, 3 and 4 of Theorem 1.6: with probability at least `1 − Pₜ`, the
graph shrinks every Blue set below the threshold, whichever vertices are Blue. The statement
formalizes Parts 2–4 in that form, which is what the union bound of the final part uses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Dense

/-- **Theorem 1.6** (`D:thm:const-advantage`). Let `p ∈ (0, 1)` and `n, c` positive integers with
`F(n, p, c) > 0`, and consider majority dynamics on `G ∼ G(n, p)` with `|B₀| ≤ n/2 − c`. Then:
1. `P(|B₁| ≤ n/2 − 0.8 √n / p) ≥ 1 − P₁(n, p, c)`;
2. with probability at least `1 − P₂(n)`, every Blue set of at most `n/2 − 0.8 √n / p` vertices
   has at most `0.4 n` Blue vertices the next day;
3. with probability at least `1 − P₃(n, p)`, every Blue set of at most `0.4 n` vertices has at
   most `p(n − 1)/3` Blue vertices the next day;
4. with probability at least `1 − P₄(n, p)`, every Blue set of at most `p(n − 1)/3` vertices
   vanishes the next day;

and consequently `R₄ = V(G)` with probability at least `1 − (P₁ + P₂ + P₃ + P₄)`. -/
theorem theorem1_6 (hBE : ShevtsovaBerryEsseen) {n c : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 0 < n) (hc : 0 < c) (hF : 0 < denseF n p c) {B₀ : Set (Fin n)}
    (hB₀ : (B₀.ncard : ℝ) ≤ n / 2 - c) :
    1 - denseP1 n p c ≤
        gnpProb n p (fun G => ((blueAfter G B₀ 1).ncard : ℝ) ≤ n / 2 - 0.8 * Real.sqrt n / p) ∧
      1 - denseP2 n ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
        (B.ncard : ℝ) ≤ n / 2 - 0.8 * Real.sqrt n / p → ((majorityStep G B).ncard : ℝ) ≤ 0.4 * n) ∧
      1 - denseP3 n p ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
        (B.ncard : ℝ) ≤ 0.4 * n → ((majorityStep G B).ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3) ∧
      1 - denseP4 n p ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
        (B.ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3 → majorityStep G B = ∅) ∧
      1 - (denseP1 n p c + denseP2 n + denseP3 n p + denseP4 n p) ≤
        gnpProb n p (fun G => blueAfter G B₀ 4 = ∅) := by
  sorry

/-- **Theorem 1.2** (`D:thm:const-advantage-ex`, the power of few). Consider majority dynamics on
`G(n, 1/2)` with `n ≥ 1000`, where the Red camp has at least `n/2 + 5` vertices on day 0. Then Red
wins after the fourth day with probability at least `0.9`. -/
theorem theorem1_2 (hBE : ShevtsovaBerryEsseen) {n : ℕ} (hn : 1000 ≤ n) {B₀ : Set (Fin n)}
    (hB₀ : (B₀.ncard : ℝ) ≤ n / 2 - 5) :
    0.9 ≤ gnpProb n (1 / 2) (fun G => blueAfter G B₀ 4 = ∅) := by
  sorry

/-- **Theorem 1.3** (`D:thm:unbounded-advantage`, asymptotic bound). Let `p ∈ (0, 1)` be a
constant. There is `K(p)` such that, whenever the Red camp has at least `n/2 + cₙ` vertices on
day 0 (`cₙ` a positive integer that may depend on `n`), Red wins after four days with probability
at least `1 − K(p) max{n⁻¹, cₙ⁻²}`.

Reading: "Red has `n/2 + cₙ`" is read as "at least `n/2 + cₙ`", as in Theorem 1.6 and the
abstract. -/
theorem theorem1_3 (hBE : ShevtsovaBerryEsseen) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ K : ℝ, ∀ (n c : ℕ), 0 < c → ∀ B₀ : Set (Fin n), (B₀.ncard : ℝ) ≤ n / 2 - c →
      1 - K * max ((n : ℝ)⁻¹) (((c : ℝ) ^ 2)⁻¹) ≤ gnpProb n p (fun G => blueAfter G B₀ 4 = ∅) := by
  sorry

end PowerOfFew.Dense

end
