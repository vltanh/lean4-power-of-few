module

public import Basic.Analysis.SpecialFunctions.CubeRoot
public import Basic.Combinatorics.Choose
public import Basic.Probability.BernoulliFamily
public import Basic.Probability.Chernoff
public import Basic.Probability.Concentration
public import PowerOfFew.Defs
public import PowerOfFew.Dense.Appendix
public import PowerOfFew.Dense.BinomialDifference
public import PowerOfFew.Dense.DayOne
public import PowerOfFew.Dense.Main
public import PowerOfFew.Dense.Shrinking
public import PowerOfFew.External.GolesOlivos.GolesOlivos
public import PowerOfFew.Model.BerryEsseen
public import PowerOfFew.Model.EdgeConditioning
public import PowerOfFew.Model.Gnp
public import PowerOfFew.Model.Lazy
public import PowerOfFew.Model.Majority
public import PowerOfFew.Model.Normal
public import PowerOfFew.Sparse.Activation
public import PowerOfFew.Sparse.ActivationCounterexample
public import PowerOfFew.Sparse.ActivationDayOne
public import PowerOfFew.Sparse.ActivationLastDays
public import PowerOfFew.Sparse.ActivationShrinking
public import PowerOfFew.Sparse.BerryEsseen
public import PowerOfFew.Sparse.Chernoff
public import PowerOfFew.Sparse.ColoringAux
public import PowerOfFew.Sparse.DayOne
public import PowerOfFew.Sparse.DayThree
public import PowerOfFew.Sparse.DayTwo
public import PowerOfFew.Sparse.Degrees
public import PowerOfFew.Sparse.Main
public import PowerOfFew.Sparse.MatrixNorm
public import PowerOfFew.Sparse.RandomColoring
public import PowerOfFew.Sparse.Subconnectivity

/-!
# Solution

The entry point of the library, and the solution that Palomar's Comparator checks against
`Challenge.lean`: every theorem of the Challenge, restated word for word in the namespace
`Challenge`, proved from the library. The definitions the statements use are the library's
(`PowerOfFew/Defs.lean`), of which `Challenge.lean` carries a verbatim copy
(`scripts/sync_challenge_defs.py`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology PowerOfFew

namespace Challenge

/-- Dense paper, **Theorem 1.6**. -/
theorem dense_theorem1_6 (hBE : ShevtsovaBerryEsseen) {n c : ℕ} {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hn : 0 < n) (hc : 0 < c) (hF : 0 < denseF n p c) {B₀ : Set (Fin n)}
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
        gnpProb n p (fun G => blueAfter G B₀ 4 = ∅) :=
  PowerOfFew.Dense.theorem1_6 hBE hp0 hp1 hn hc hF hB₀

/-- Dense paper, **Theorem 1.2** (the power of few). -/
theorem dense_theorem1_2 (hBE : ShevtsovaBerryEsseen) {n : ℕ} (hn : 1000 ≤ n)
    {B₀ : Set (Fin n)} (hB₀ : (B₀.ncard : ℝ) ≤ n / 2 - 5) :
    0.9 ≤ gnpProb n (1 / 2) (fun G => blueAfter G B₀ 4 = ∅) :=
  PowerOfFew.Dense.theorem1_2 hBE hn hB₀

/-- Dense paper, **Theorem 1.3** (asymptotic bound). -/
theorem dense_theorem1_3 (hBE : ShevtsovaBerryEsseen) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ K : ℝ, ∀ (n c : ℕ), 0 < c → ∀ B₀ : Set (Fin n), (B₀.ncard : ℝ) ≤ n / 2 - c →
      1 - K * max ((n : ℝ)⁻¹) (((c : ℝ) ^ 2)⁻¹) ≤ gnpProb n p (fun G => blueAfter G B₀ 4 = ∅) :=
  PowerOfFew.Dense.theorem1_3 hBE hp0 hp1

/-- Sparse paper, **Theorem 1.2** (the power of few for sparse graphs). -/
theorem sparse_theorem1_2 (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2)
    (hBLM : BLMTheorem6_10) {lam : ℝ} (hlam : 0 < lam) :
    ∃ C K : ℝ, ∀ (n : ℕ) (p : ℝ) (B₀ : Set (Fin n)), 0 < p →
      p * n ≤ (n : ℝ) - 10 → (1 + lam) * Real.log n ≤ p * n →
      10 ≤ p * ((n : ℝ) / 2 - B₀.ncard) →
      1 - C * (1 / min (n : ℝ) (p * ((n : ℝ) / 2 - B₀.ncard) ^ 2) + (n : ℝ) ^ (-(lam / 2))) ≤
        gnpProb n p (fun G => ∃ t : ℕ,
          (t : ℝ) ≤ K * (Real.log n / Real.log (p * n)) ∧ blueAfter G B₀ t = ∅) :=
  PowerOfFew.Sparse.theorem1_2 hBE hBBK hBLM hlam

/-- Sparse paper, **Theorem 1.4** (a delayed version of the theorem of Fountoulakis, Kang and
Makai). -/
theorem sparse_theorem1_4 (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2)
    (hBLM : BLMTheorem6_10) {ε : ℝ} (hε : 0 < ε) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ T : ℕ, ∀ (n : ℕ) (p : ℝ), lam ≤ p * Real.sqrt n → p ≤ 1 →
      1 - ε ≤ coloredProb n p (1 / 2) (fun G B₀ =>
        ((B₀.ncard : ℝ) < n / 2 ∧ blueAfter G B₀ T = ∅) ∨
          ((n : ℝ) / 2 < B₀.ncard ∧ blueAfter G B₀ T = Set.univ)) :=
  PowerOfFew.Sparse.theorem1_4 hBE hBBK hBLM hε

/-- Sparse paper, **Theorem 1.5**, corrected (bias `ω(max{(pn)⁻¹, n^(−1/2)})`). -/
theorem sparse_theorem1_5 (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2)
    (hBLM : BLMTheorem6_10) {lam : ℝ} (hlam : 0 < lam) {p q : ℕ → ℝ} (hp0 : ∀ n, 0 < p n)
    (hp1 : ∀ n, p n ≤ 1) (hlog : ∀ᶠ n : ℕ in atTop, (1 + lam) * Real.log n / n ≤ p n)
    (hq : ∀ n, q n ≤ 1)
    (hbias : Tendsto (fun n : ℕ => (q n - 1 / 2) * min (p n * n) (Real.sqrt n)) atTop atTop) :
    Tendsto (fun n : ℕ =>
      coloredProb n (p n) (q n) (fun G B₀ => ∃ t, blueAfter G B₀ t = ∅)) atTop (𝓝 1) :=
  PowerOfFew.Sparse.theorem1_5 hBE hBBK hBLM hlam hp0 hp1 hlog hq hbias

/-- Sparse paper, **Theorem 1.5** as printed (bias `ω((pn)⁻¹)`) is false. -/
theorem sparse_theorem1_5_printed_false :
    ¬ ∀ (lam : ℝ), 0 < lam → ∀ (p q : ℕ → ℝ), (∀ n, 0 < p n) → (∀ n, p n ≤ 1) →
      (∀ n : ℕ, (1 + lam) * Real.log n / n ≤ p n) → (∀ n, q n ≤ 1) →
      Tendsto (fun n : ℕ => (q n - 1 / 2) * (p n * n)) atTop atTop →
      Tendsto (fun n : ℕ =>
        coloredProb n (p n) (q n) (fun G B₀ => ∃ t, blueAfter G B₀ t = ∅)) atTop (𝓝 1) :=
  PowerOfFew.Sparse.theorem1_5_printed_false

/-- Sparse paper, **Theorem 3.1** (below the connectivity threshold). -/
theorem sparse_theorem3_1 (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2)
    (hBLM : BLMTheorem6_10) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ C K : ℝ, ∀ (n : ℕ) (B₀ : Set (Fin n)),
      10 ≤ (1 - lam) * Real.log n / n * ((n : ℝ) / 2 - B₀.ncard) →
      1 - C * (1 / min (n : ℝ) ((1 - lam) * Real.log n / n * ((n : ℝ) / 2 - B₀.ncard) ^ 2) +
          (n : ℝ) ^ (-(1 - lam))) ≤
        gnpProb n ((1 - lam) * Real.log n / n) (fun G => ∃ t₀ : ℕ,
          (∀ t ≥ t₀, blueAfter G B₀ t = blueAfter G B₀ t₀ ∨
            blueAfter G B₀ t = blueAfter G B₀ (t₀ + 1)) ∧
          (blueAfter G B₀ (t₀ + 1)).ncard ≤ (blueAfter G B₀ t₀).ncard ∧
          ((blueAfter G B₀ t₀).ncard : ℝ) ≤
            Real.log n ^ (K * Real.sqrt (Real.log n)) * (n : ℝ) ^ lam ∧
          ∑ᶠ v ∈ blueAfter G B₀ t₀, (degree G v : ℝ) ≤
            K * Real.sqrt ((1 - lam) * Real.log n) * (blueAfter G B₀ t₀).ncard) :=
  PowerOfFew.Sparse.theorem3_1 hBE hBBK hBLM hlam0 hlam1

/-- Sparse paper, **Theorem 1.7**, corrected (random activations and updates). -/
theorem sparse_theorem1_7 (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10)
    {pac pup : ℝ} (hpac0 : 0 < pac) (hpac1 : pac ≤ 1) (hpup0 : 0 < pup) (hpup1 : pup ≤ 1)
    {lam : ℝ} (hlam : 0 < lam) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C S A C' c : ℝ, 0 < c ∧ ∀ (n : ℕ) (p : ℝ) (B₀ : Set (Fin n)), 0 < p →
      (1 + lam) * Real.log n ≤ p * pac * n → 10 ≤ (1 - p) * pac * n →
      C ≤ p * ((n : ℝ) / 2 - B₀.ncard) → S * Real.sqrt n ≤ (n : ℝ) / 2 - B₀.ncard →
      1 - ε - C' * (n : ℝ) ^ (-(lam / 4)) - (n : ℝ) ^ (-c) ≤
        lazyProb n p pac pup (fun G c' => ∃ t : ℕ,
          (t : ℝ) ≤ A * Real.log n ∧ lazyBlueAfter G c' B₀ t = ∅) :=
  PowerOfFew.Sparse.theorem1_7 hBE hBBK hBLM hpac0 hpac1 hpup0 hpup1 hlam hε0 hε1

/-- Sparse paper, **Theorem 4.1**, corrected. -/
theorem sparse_theorem4_1 (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10) :
    ∃ (M S : ℝ → ℝ) (A c₁ : ℝ), 0 < c₁ ∧ ∀ ε K lam : ℝ, 0 < ε → ε < 1 → 8 ≤ K → 0 < lam →
      ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ pac pup : ℝ, 0 < pac → pac ≤ 1 → 0 < pup → pup ≤ 1 →
      ∃ C : ℝ, ∀ (n : ℕ) (p : ℝ) (B₀ : Set (Fin n)), 0 < p →
        (1 + lam) * Real.log n ≤ p * pac * n → 10 ≤ (1 - p) * pac * n →
        S ε * Real.sqrt n ≤ Real.sqrt pac * ((n : ℝ) / 2 - B₀.ncard) →
        M K ≤ p * pup * pac ^ 2 * ((n : ℝ) / 2 - B₀.ncard) →
        1 - ε - Real.exp (-(c₁ * K ^ 2 / p)) - C * (n : ℝ) ^ (-(lam / 4)) -
            (n : ℝ) ^ (-(c₂ * pup * pac)) ≤
          lazyProb n p pac pup (fun G c => ∃ t : ℕ,
            (t : ℝ) ≤ A * Real.log n / (pup * pac) ∧ lazyBlueAfter G c B₀ t = ∅) :=
  PowerOfFew.Sparse.theorem4_1 hBE hBBK hBLM

/-- Sparse paper, **Theorem 1.7** as printed fails along one sequence. -/
theorem sparse_theorem1_7_printed_false_seq :
    ∃ B : (n : ℕ) → Set (Fin n),
      (∀ C₀ : ℝ, ∀ᶠ n : ℕ in atTop, (1 + 1 / 2) * Real.log n ≤ 1 * (1 / 2) * n ∧
        C₀ ≤ 1 * ((n : ℝ) / 2 - (B n).ncard)) ∧
      ¬ ∃ A C₁ C₂ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
          1 - C₁ / min (n : ℝ) (1 * ((n : ℝ) / 2 - (B n).ncard) ^ 2) -
              C₂ * (n : ℝ) ^ (-((1 / 2 : ℝ) / 4)) - (n : ℝ) ^ (-c) ≤
            lazyProb n 1 (1 / 2) 1 (fun G c' => ∃ t : ℕ,
              (t : ℝ) ≤ A * Real.log n ∧ lazyBlueAfter G c' (B n) t = ∅) :=
  PowerOfFew.Sparse.theorem1_7_printed_false_seq

/-- Sparse paper, **Theorem 4.1** as printed fails along one sequence. -/
theorem sparse_theorem4_1_printed_false_seq :
    ∃ B : (n : ℕ) → Set (Fin n),
      (∀ M : ℝ, ∀ᶠ n : ℕ in atTop, (1 + 1 / 2) * Real.log n ≤ 1 * (1 / 2) * n ∧
        M ≤ 1 * 1 * (1 / 2) ^ 2 * ((n : ℝ) / 2 - (B n).ncard)) ∧
      ¬ ∃ A C₁ c₁ C₂ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ n : ℕ in atTop,
          1 - C₁ / (1 ^ 2 * (1 / 2) ^ 2 *
                min (n : ℝ) (1 * (1 / 2) * ((n : ℝ) / 2 - (B n).ncard) ^ 2)) -
              Real.exp (-(c₁ * 1 ^ 2 * (1 / 2) ^ 4 * 1 * ((n : ℝ) / 2 - (B n).ncard) ^ 2)) -
              C₂ * (n : ℝ) ^ (-((1 / 2 : ℝ) / 4)) - (n : ℝ) ^ (-(c₂ * 1 * (1 / 2))) ≤
            lazyProb n 1 (1 / 2) 1 (fun G c => ∃ t : ℕ,
              (t : ℝ) ≤ A * Real.log n / (1 * (1 / 2)) ∧ lazyBlueAfter G c (B n) t = ∅) :=
  PowerOfFew.Sparse.theorem4_1_printed_false_seq

/-- `Φ` is the distribution function of the standard Gaussian law (a compared theorem: it
identifies the Challenge's `Φ` with Mathlib's `gaussianReal 0 1`). -/
theorem Φ_eq_cdf_gaussianReal (a : ℝ) : Φ a = cdf (gaussianReal 0 1) a :=
  PowerOfFew.Φ_eq_cdf_gaussianReal a

end Challenge
