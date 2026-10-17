module

public import Mathlib

/-!
# Shared definitions

The definitions that the statements of record in `Challenge.lean` use. The block between the two
marker comments is copied word for word into `Challenge.lean` by
`scripts/sync_challenge_defs.py`, so that the Challenge and the library elaborate the same
constants (Comparator compares them). This module imports exactly what the Challenge imports.

* Probabilities under the random graph `G(n, p)` on `Fin n`, Mathlib's
  `SimpleGraph.binomialRandom` (`gnpProb`).
* Majority dynamics (Tran–Vu, Definition 1.1 of the sparse paper): every day each vertex takes
  the colour of the majority of its neighbours, and keeps its colour on a tie (`majorityStep`,
  `blueAfter`). Colourings are given by their Blue sets; Red is the complement.
* Majority dynamics with random activations and updates (sparse paper, Definition 1.6):
  `lazyStep`, `lazyBlueAfter`, `lazyLaw`.
* Random initial colourings (sparse paper, Theorems 1.4 and 1.5): `coloredGnp`.
* The normal distribution function `Φ` and `Φ₀(a) = Φ(a) − 1/2`.
* The functions `F, P₁, …, P₄` of the dense paper's Theorem 1.6 (journal version).
* The cited result that the formalization assumes, as a proposition named after its source:
  the Berry–Esseen inequality with Shevtsova's constant `0.56`
  (`PowerOfFew/External/BerryEsseen/README.md`).
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
