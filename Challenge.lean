module

public import Mathlib

/-!
# The power of few: statements of record

The main results of two papers on majority dynamics on the Erdős–Rényi random graph `G(n, p)`:

* L. Tran and V. Vu, *Reaching a consensus on random networks: the power of few*, Theory of
  Computing 19 (2023), article 6 (the "dense paper"; arXiv:1911.10279);
* B. Tran and V. Vu, *The "Power of Few" phenomenon: the sparse case*, Random Structures &
  Algorithms 66 (2025), e21260 (the "sparse paper"; arXiv:2302.05605v2).

**The formalization is conditional.** The papers' explicit constants rest on the Berry–Esseen
inequality with Shevtsova's constant `0.56`. It is assumed, as the hypothesis
`ShevtsovaBerryEsseen` (Shevtsova 2010), by each theorem below that uses it. The sparse paper's
spectral bound (its Lemma A.7) is proved, by Feige and Ofek's argument.

## Conventions

* Vertices are `Fin n`. A colouring is given by its Blue set `B`; Red is the complement.
* `majorityStep G B` is the next day's Blue set: a vertex becomes (or stays) Blue iff it has more
  Blue than Red neighbours, or as many and is Blue already. `blueAfter G B₀ t` iterates it `t`
  times. "Red wins (by day `t`)" means `blueAfter G B₀ t = ∅`.
* `gnpProb n p P` is the probability that `G ∼ G(n, p)` (Mathlib's
  `SimpleGraph.binomialRandom`) has property `P`. `coloredProb n p q P` adds an independent random
  colouring, each vertex Red with probability `q`.
* `Φ` is the standard normal distribution function (`Φ(a) = 1/2 + Φ₀(a)`,
  `Φ₀(a) = (2π)^(-1/2) ∫₀^a e^(-x²/2) dx`).
* `Δ = n/2 − |B₀|`, so that the Red camp has `n/2 + Δ` vertices.

## The statements

* `Challenge.dense_theorem1_6`: the dense paper's main theorem, with the explicit bounds
  `P₁, …, P₄` (`denseP1`, …). Parts 2–4 are read as the paper proves them (its Lemmas 3.5, 3.6,
  3.3): with probability `1 − Pₜ`, the graph shrinks every Blue set below the next threshold.
  `P₂` uses the coefficient `1.83` of the paper's proof; Theorem 1.6 prints `1.38`.
* `Challenge.dense_theorem1_2`: on `G(n, 1/2)` with `n ≥ 1000`, if Red has at least `n/2 + 5`
  vertices, Red wins after four days with probability at least `0.9`.
* `Challenge.dense_theorem1_3`: for constant `p`, Red with at least `n/2 + c` vertices wins after
  four days with probability at least `1 − K(p) max{1/n, 1/c²}`.
* `Challenge.sparse_theorem1_2`: if `n − 10 ≥ pn ≥ (1 + λ) log n` and `pΔ ≥ 10`, Red wins within
  `O(log n / log(pn))` days with probability at least `1 − O(1/min{n, pΔ²} + n^(−λ/2))` (the
  constants may depend on `λ`).
* `Challenge.sparse_theorem1_4`: with a random balanced colouring and `p ≥ λ n^(−1/2)`, the larger
  side wins in `O(1)` days with probability at least `1 − ε`.
* `Challenge.sparse_theorem1_5`: with a random colouring biased towards Red by
  `ω(max{(pn)⁻¹, n^(−1/2)})` and `p ≥ (1 + λ) log n / n` (for large `n`), Red wins with
  probability `1 − o(1)`.
  The paper asks only for a bias `ω((pn)⁻¹)`; `Challenge.sparse_theorem1_5_printed_false` shows
  that the printed statement is false (take `p = 1` and bias `(log n)/n`).
* `Challenge.sparse_theorem3_1`: for `p = (1 − λ) log n / n` and `pΔ ≥ 10`, with probability at
  least `1 − O(1/min{n, pΔ²} + n^(−(1−λ)))` the process becomes periodic with period at most 2,
  and ends with at most `(log n)^(O(√(log n))) n^λ` Blue vertices, of average degree `O(√(pn))`.
* `Challenge.sparse_theorem1_7` and `Challenge.sparse_theorem4_1`: majority dynamics with random
  activations (rate `p_ac`) and updates (rate `p_up`), corrected. As printed both theorems are
  false: with `p = 1`, `p_ac = 1/2`, `p_up = 1` and `Δ = ⌊n^(1/4)⌋`, Red wins with probability at
  most `1/2 + o(1)` (`Challenge.sparse_theorem1_7_printed_false_seq`,
  `Challenge.sparse_theorem4_1_printed_false_seq`, which refute the printed bounds along that
  sequence). The corrected statements add the hypothesis `Δ ≥ S_ε √(n/p_ac)` with a failure
  probability `ε` for the first day, as in the paper's Proposition 4.2, and `(1 − p) p_ac n ≥ 10`,
  the analogue of Theorem 1.2's `n − 10 ≥ pn` that the paper's proofs use.
-/

@[expose] public section

-- BEGIN SHARED DEFINITIONS

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew

/-! ## The random graph `G(n, p)` -/

/-- A real number clamped into the unit interval: `toUnit p = p` whenever `0 ≤ p ≤ 1`. -/
def toUnit (p : ℝ) : unitInterval := Set.projIcc 0 1 zero_le_one p

/-- The probability that the binomial random graph `G(n, p)` has the property `P`. The law is
Mathlib's `SimpleGraph.binomialRandom (Fin n) p`, the Erdős–Rényi model `G(n, p)`: each pair of
distinct vertices is an edge with probability `p`, independently of the other pairs. -/
def gnpProb (n : ℕ) (p : ℝ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  (SimpleGraph.binomialRandom (Fin n) (toUnit p)).real {G | P G}

/-! ## Majority dynamics -/

/-- The number of neighbours of `v` in the set `S`. -/
def nbrCount {n : ℕ} (G : SimpleGraph (Fin n)) (S : Set (Fin n)) (v : Fin n) : ℕ :=
  {u | G.Adj v u ∧ u ∈ S}.ncard

/-- The degree of `v`: its number of neighbours. -/
abbrev degree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ := (G.neighborSet v).ncard

/-- One day of majority dynamics, acting on the Blue set `B` (Red is `Bᶜ`): a vertex is Blue the
next day if it has more Blue than Red neighbours, or as many and is Blue today. -/
def majorityStep {n : ℕ} (G : SimpleGraph (Fin n)) (B : Set (Fin n)) : Set (Fin n) :=
  {v | nbrCount G Bᶜ v < nbrCount G B v ∨ (nbrCount G Bᶜ v = nbrCount G B v ∧ v ∈ B)}

/-- The Blue set after `t` days of majority dynamics on `G`, starting from the Blue set `B₀`. -/
def blueAfter {n : ℕ} (G : SimpleGraph (Fin n)) (B₀ : Set (Fin n)) (t : ℕ) : Set (Fin n) :=
  (majorityStep G)^[t] B₀

/-! ## Random initial colourings -/

/-- The joint law of `G(n, p)` and an independent random colouring in which each vertex is Red
(`true`) with probability `q`, independently. -/
def coloredGnp (n : ℕ) (p q : ℝ) : Measure (SimpleGraph (Fin n) × (Fin n → Bool)) :=
  (SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod
    (Measure.pi fun _ => bernoulliMeasure true false (toUnit q))

/-- The probability, under `coloredGnp n p q`, that the graph and the initial Blue set have the
property `P`. -/
def coloredProb (n : ℕ) (p q : ℝ) (P : SimpleGraph (Fin n) → Set (Fin n) → Prop) : ℝ :=
  (coloredGnp n p q).real {x | P x.1 {v | x.2 v = false}}

/-! ## Majority dynamics with random activations and updates -/

/-- One day of majority dynamics with random activations and updates (sparse paper,
Definition 1.6), acting on the Blue set `B`. `A` is the set of active vertices and `U` the set of
vertices whose update coin is `true`; a vertex updates iff it is in `A ∩ U`. An updating vertex
observes its active neighbours only, and takes the majority of their colours, keeping its colour
on a tie; every other vertex keeps its colour. -/
def lazyStep {n : ℕ} (G : SimpleGraph (Fin n)) (A U B : Set (Fin n)) : Set (Fin n) :=
  {v | (v ∈ A ∩ U ∧ (nbrCount G (A ∩ Bᶜ) v < nbrCount G (A ∩ B) v ∨
          (nbrCount G (A ∩ Bᶜ) v = nbrCount G (A ∩ B) v ∧ v ∈ B))) ∨
       (v ∉ A ∩ U ∧ v ∈ B)}

/-- The coins of one day: activation coins and update coins, one of each per vertex. -/
abbrev DayCoins (n : ℕ) : Type := (Fin n → Bool) × (Fin n → Bool)

/-- The law of one day's coins: independent activations with probability `pac` and independent
update coins with probability `pup`. -/
def dayLaw (n : ℕ) (pac pup : ℝ) : Measure (DayCoins n) :=
  (Measure.pi fun _ => bernoulliMeasure true false (toUnit pac)).prod
    (Measure.pi fun _ => bernoulliMeasure true false (toUnit pup))

/-- The Blue set after `t` days of majority dynamics with activations and updates, where `c t`
are the coins of day `t + 1`. -/
def lazyBlueAfter {n : ℕ} (G : SimpleGraph (Fin n)) (c : ℕ → DayCoins n) (B₀ : Set (Fin n)) :
    ℕ → Set (Fin n)
  | 0 => B₀
  | t + 1 => lazyStep G {v | (c t).1 v = true} {v | (c t).2 v = true} (lazyBlueAfter G c B₀ t)

/-- The joint law of `G(n, p)` and of the coins of all days, independent of each other. -/
def lazyLaw (n : ℕ) (p pac pup : ℝ) : Measure (SimpleGraph (Fin n) × (ℕ → DayCoins n)) :=
  (SimpleGraph.binomialRandom (Fin n) (toUnit p)).prod
    (Measure.infinitePi fun _ : ℕ => dayLaw n pac pup)

/-- The probability, under `lazyLaw n p pac pup`, that the graph and the coins have the property
`P`. -/
def lazyProb (n : ℕ) (p pac pup : ℝ) (P : SimpleGraph (Fin n) → (ℕ → DayCoins n) → Prop) : ℝ :=
  (lazyLaw n p pac pup).real {x | P x.1 x.2}

/-! ## The normal distribution function -/

/-- `Φ₀(a) = (2π)^(-1/2) ∫₀^a e^(-x²/2) dx`, so that `Φ(a) = 1/2 + Φ₀(a)`. -/
def Φ₀ (a : ℝ) : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x in (0 : ℝ)..a, Real.exp (-x ^ 2 / 2)

/-- The distribution function of the standard normal law, `Φ(a) = 1/2 + Φ₀(a)`. -/
def Φ (a : ℝ) : ℝ := 1 / 2 + Φ₀ a

/-! ## The dense paper's Theorem 1.6 (journal version) -/

/-- `F(n, p, c)` of the dense paper's Theorem 1.6. -/
def denseF (n : ℕ) (p c : ℝ) : ℝ :=
  Real.sqrt n * Φ₀ ((2 * p * c + min p (1 - p)) / Real.sqrt (p * (1 - p) * n)) -
    0.6 * (1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p)) - 0.8 / p

/-- `P₁(n, p, c)` of the dense paper's Theorem 1.6. -/
def denseP1 (n : ℕ) (p c : ℝ) : ℝ :=
  (0.25 + 0.7 * (1 - 2 * p + 2 * p ^ 2) ^ 2 * (1 + 4 * c ^ 2 / (n : ℝ) ^ 2)) / denseF n p c ^ 2

/-- `P₂(n)` of the dense paper's Theorem 1.6, with the coefficient `1.83` that its proof
(Lemma 3.5) computes; the statement prints `1.38`. -/
def denseP2 (n : ℕ) : ℝ := (n : ℝ)⁻¹ * Real.exp (-(0.076 * n - 1.83 * Real.sqrt n))

/-- `P₃(n, p)` of the dense paper's Theorem 1.6. -/
def denseP3 (n : ℕ) (p : ℝ) : ℝ := (n : ℝ)⁻¹ * Real.exp (-(0.02 * n * (p ^ 3 * n - 80)))

/-- `P₄(n, p)` of the dense paper's Theorem 1.6. -/
def denseP4 (n : ℕ) (p : ℝ) : ℝ := n * Real.exp (-(2 / 9 * p ^ 2 * (n - 1)))

/-! ## Cited results that the formalization assumes -/

/-- The Berry–Esseen inequality with constant `C`: for `m ≥ 1` independent real random variables
`X₁, …, Xₘ` with zero means, positive variances and finite absolute third moments, writing
`B² = ∑ E Xᵢ²`, for every `x`,
`|P(X₁ + ⋯ + Xₘ ≤ x B) − Φ(x)| ≤ C (∑ E|Xᵢ|³) / B³`. -/
def BerryEsseenInequality (C : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ)
    (X : Fin m → Ω → ℝ), 0 < m → (∀ i, Measurable (X i)) → iIndepFun X μ →
    (∀ i, Integrable (fun ω => |X i ω| ^ 3) μ) → (∀ i, ∫ ω, X i ω ∂μ = 0) →
    (∀ i, 0 < ∫ ω, X i ω ^ 2 ∂μ) →
    ∀ x : ℝ,
      |μ.real {ω | ∑ i, X i ω ≤ x * Real.sqrt (∑ i, ∫ ω, X i ω ^ 2 ∂μ)} - Φ x| ≤
        C * (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) / Real.sqrt (∑ i, ∫ ω, X i ω ^ 2 ∂μ) ^ 3

/-- **Shevtsova (2010)** (`D:thm:esseen`, `S:thm:esseen`), *An improvement of convergence rate estimates in the
Lyapunov theorem*, Doklady Mathematics 82(3), 862–864: the Berry–Esseen inequality holds with the
constant `0.56`.
Both papers use it (dense paper, Theorem 2.2; sparse paper, Theorem A.1). It is assumed, not
proved: its proof rests on computer-assisted estimates of characteristic functions. -/
def ShevtsovaBerryEsseen : Prop := BerryEsseenInequality 0.56

/-- The adjacency matrix of `G`, with real entries. -/
def adjMat {n : ℕ} (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun u v => by classical exact if G.Adj u v then 1 else 0

/-- The mean adjacency matrix of `G(n, p)`: `p` off the diagonal and `0` on it. -/
def meanAdj (n : ℕ) (p : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun u v => if u = v then 0 else p

/-- The spectral norm (the `ℓ² → ℓ²` operator norm) of a square real matrix. -/
def specNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) M‖

end PowerOfFew

end

-- END SHARED DEFINITIONS

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
        gnpProb n p (fun G => blueAfter G B₀ 4 = ∅) := by
  sorry

/-- Dense paper, **Theorem 1.2** (the power of few). -/
theorem dense_theorem1_2 (hBE : ShevtsovaBerryEsseen) {n : ℕ} (hn : 1000 ≤ n)
    {B₀ : Set (Fin n)} (hB₀ : (B₀.ncard : ℝ) ≤ n / 2 - 5) :
    0.9 ≤ gnpProb n (1 / 2) (fun G => blueAfter G B₀ 4 = ∅) := by
  sorry

/-- Dense paper, **Theorem 1.3** (asymptotic bound). -/
theorem dense_theorem1_3 (hBE : ShevtsovaBerryEsseen) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ K : ℝ, ∀ (n c : ℕ), 0 < c → ∀ B₀ : Set (Fin n), (B₀.ncard : ℝ) ≤ n / 2 - c →
      1 - K * max ((n : ℝ)⁻¹) (((c : ℝ) ^ 2)⁻¹) ≤ gnpProb n p (fun G => blueAfter G B₀ 4 = ∅) := by
  sorry

/-- Sparse paper, **Theorem 1.2** (the power of few for sparse graphs). -/
theorem sparse_theorem1_2 (hBE : ShevtsovaBerryEsseen) {lam : ℝ} (hlam : 0 < lam) :
    ∃ C K : ℝ, ∀ (n : ℕ) (p : ℝ) (B₀ : Set (Fin n)), 0 < p →
      p * n ≤ (n : ℝ) - 10 → (1 + lam) * Real.log n ≤ p * n →
      10 ≤ p * ((n : ℝ) / 2 - B₀.ncard) →
      1 - C * (1 / min (n : ℝ) (p * ((n : ℝ) / 2 - B₀.ncard) ^ 2) + (n : ℝ) ^ (-(lam / 2))) ≤
        gnpProb n p (fun G => ∃ t : ℕ,
          (t : ℝ) ≤ K * (Real.log n / Real.log (p * n)) ∧ blueAfter G B₀ t = ∅) := by
  sorry

/-- Sparse paper, **Theorem 1.4** (a delayed version of the theorem of Fountoulakis, Kang and
Makai). -/
theorem sparse_theorem1_4 (hBE : ShevtsovaBerryEsseen) {ε : ℝ} (hε : 0 < ε) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ T : ℕ, ∀ (n : ℕ) (p : ℝ), lam ≤ p * Real.sqrt n → p ≤ 1 →
      1 - ε ≤ coloredProb n p (1 / 2) (fun G B₀ =>
        ((B₀.ncard : ℝ) < n / 2 ∧ blueAfter G B₀ T = ∅) ∨
          ((n : ℝ) / 2 < B₀.ncard ∧ blueAfter G B₀ T = Set.univ)) := by
  sorry

/-- Sparse paper, **Theorem 1.5**, corrected (bias `ω(max{(pn)⁻¹, n^(−1/2)})`). -/
theorem sparse_theorem1_5 (hBE : ShevtsovaBerryEsseen) {lam : ℝ} (hlam : 0 < lam) {p q : ℕ → ℝ}
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n ≤ 1)
    (hlog : ∀ᶠ n : ℕ in atTop, (1 + lam) * Real.log n / n ≤ p n) (hq : ∀ n, q n ≤ 1)
    (hbias : Tendsto (fun n : ℕ => (q n - 1 / 2) * min (p n * n) (Real.sqrt n)) atTop atTop) :
    Tendsto (fun n : ℕ =>
      coloredProb n (p n) (q n) (fun G B₀ => ∃ t, blueAfter G B₀ t = ∅)) atTop (𝓝 1) := by
  sorry

/-- Sparse paper, **Theorem 1.5** as printed (bias `ω((pn)⁻¹)`) is false. -/
theorem sparse_theorem1_5_printed_false :
    ¬ ∀ (lam : ℝ), 0 < lam → ∀ (p q : ℕ → ℝ), (∀ n, 0 < p n) → (∀ n, p n ≤ 1) →
      (∀ n : ℕ, (1 + lam) * Real.log n / n ≤ p n) → (∀ n, q n ≤ 1) →
      Tendsto (fun n : ℕ => (q n - 1 / 2) * (p n * n)) atTop atTop →
      Tendsto (fun n : ℕ =>
        coloredProb n (p n) (q n) (fun G B₀ => ∃ t, blueAfter G B₀ t = ∅)) atTop (𝓝 1) := by
  sorry

/-- Sparse paper, **Theorem 3.1** (below the connectivity threshold). -/
theorem sparse_theorem3_1 (hBE : ShevtsovaBerryEsseen) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1) :
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
            K * Real.sqrt ((1 - lam) * Real.log n) * (blueAfter G B₀ t₀).ncard) := by
  sorry

/-- Sparse paper, **Theorem 1.7**, corrected (random activations and updates). -/
theorem sparse_theorem1_7 (hBE : ShevtsovaBerryEsseen)
    {pac pup : ℝ} (hpac0 : 0 < pac) (hpac1 : pac ≤ 1) (hpup0 : 0 < pup) (hpup1 : pup ≤ 1)
    {lam : ℝ} (hlam : 0 < lam) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C S A C' c : ℝ, 0 < c ∧ ∀ (n : ℕ) (p : ℝ) (B₀ : Set (Fin n)), 0 < p →
      (1 + lam) * Real.log n ≤ p * pac * n → 10 ≤ (1 - p) * pac * n →
      C ≤ p * ((n : ℝ) / 2 - B₀.ncard) → S * Real.sqrt n ≤ (n : ℝ) / 2 - B₀.ncard →
      1 - ε - C' * (n : ℝ) ^ (-(lam / 4)) - (n : ℝ) ^ (-c) ≤
        lazyProb n p pac pup (fun G c' => ∃ t : ℕ,
          (t : ℝ) ≤ A * Real.log n ∧ lazyBlueAfter G c' B₀ t = ∅) := by
  sorry

/-- Sparse paper, **Theorem 4.1**, corrected. -/
theorem sparse_theorem4_1 (hBE : ShevtsovaBerryEsseen) :
    ∃ (M S : ℝ → ℝ) (A c₁ : ℝ), 0 < c₁ ∧ ∀ ε K lam : ℝ, 0 < ε → ε < 1 → 8 ≤ K → 0 < lam →
      ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ pac pup : ℝ, 0 < pac → pac ≤ 1 → 0 < pup → pup ≤ 1 →
      ∃ C : ℝ, ∀ (n : ℕ) (p : ℝ) (B₀ : Set (Fin n)), 0 < p →
        (1 + lam) * Real.log n ≤ p * pac * n → 10 ≤ (1 - p) * pac * n →
        S ε * Real.sqrt n ≤ Real.sqrt pac * ((n : ℝ) / 2 - B₀.ncard) →
        M K ≤ p * pup * pac ^ 2 * ((n : ℝ) / 2 - B₀.ncard) →
        1 - ε - Real.exp (-(c₁ * K ^ 2 / p)) - C * (n : ℝ) ^ (-(lam / 4)) -
            (n : ℝ) ^ (-(c₂ * pup * pac)) ≤
          lazyProb n p pac pup (fun G c => ∃ t : ℕ,
            (t : ℝ) ≤ A * Real.log n / (pup * pac) ∧ lazyBlueAfter G c B₀ t = ∅) := by
  sorry

/-- Sparse paper, **Theorem 1.7** as printed fails along one sequence. -/
theorem sparse_theorem1_7_printed_false_seq :
    ∃ B : (n : ℕ) → Set (Fin n),
      (∀ C₀ : ℝ, ∀ᶠ n : ℕ in atTop, (1 + 1 / 2) * Real.log n ≤ 1 * (1 / 2) * n ∧
        C₀ ≤ 1 * ((n : ℝ) / 2 - (B n).ncard)) ∧
      ¬ ∃ A C₁ C₂ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
          1 - C₁ / min (n : ℝ) (1 * ((n : ℝ) / 2 - (B n).ncard) ^ 2) -
              C₂ * (n : ℝ) ^ (-((1 / 2 : ℝ) / 4)) - (n : ℝ) ^ (-c) ≤
            lazyProb n 1 (1 / 2) 1 (fun G c' => ∃ t : ℕ,
              (t : ℝ) ≤ A * Real.log n ∧ lazyBlueAfter G c' (B n) t = ∅) := by
  sorry

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
              (t : ℝ) ≤ A * Real.log n / (1 * (1 / 2)) ∧ lazyBlueAfter G c (B n) t = ∅) := by
  sorry

/-- `Φ` is the distribution function of the standard Gaussian law (a compared theorem: it
identifies the Challenge's `Φ` with Mathlib's `gaussianReal 0 1`). -/
theorem Φ_eq_cdf_gaussianReal (a : ℝ) : Φ a = cdf (gaussianReal 0 1) a := by
  sorry

end Challenge
