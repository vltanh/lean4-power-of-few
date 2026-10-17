module

public import PowerOfFew.Model.BerryEsseen

/-!
# Dense paper, Section 2.1: the difference of two binomial variables

Lemmas 2.3 and 2.4 of Tran–Vu, *Reaching a consensus on random networks: the power of few*
(Theory of Computing 19 (2023), article 6), which apply the Berry–Esseen inequality with
Shevtsova's constant (the paper's Theorem 2.2, assumed here as `ShevtsovaBerryEsseen`).

Independent binomial variables `Y₁ ∼ Bin(n₁, p)` and `Y₂ ∼ Bin(n₂, p)` are represented as the sums
of a Bernoulli(`p`) family over disjoint finite index sets `S₁` and `S₂` (`#S₁ = n₁`,
`#S₂ = n₂`); `IsBernoulliFamily.measureReal_sum_eq` shows that such sums are binomial.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Dense

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*}
  {p : ℝ} {X : ι → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- The difference of the sums over two disjoint index sets, centred, is the signed sum
`∑_{S₁ ∪ S₂} sᵢ (Xᵢ − p)` with `s = 1` on `S₁` and `s = −1` off `S₁`. -/
theorem dayOneAux_sum_sign_mul [DecidableEq ι] (X : ι → Ω → ℝ) (p : ℝ) {S₁ S₂ : Finset ι}
    (hS : Disjoint S₁ S₂) (ω : Ω) [DecidablePred (· ∈ S₁)] :
    ∑ i ∈ S₁ ∪ S₂, (if i ∈ S₁ then (1 : ℝ) else -1) * (X i ω - p) =
      (∑ i ∈ S₁, X i ω - ∑ i ∈ S₂, X i ω) - p * ((S₁.card : ℝ) - S₂.card) := by
  rw [Finset.sum_union hS]
  have h1 : ∑ i ∈ S₁, (if i ∈ S₁ then (1 : ℝ) else -1) * (X i ω - p) =
      ∑ i ∈ S₁, (X i ω - p) :=
    Finset.sum_congr rfl fun i hi => by simp [hi]
  have h2 : ∑ i ∈ S₂, (if i ∈ S₁ then (1 : ℝ) else -1) * (X i ω - p) =
      -∑ i ∈ S₂, (X i ω - p) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i hi => by
      simp [Finset.disjoint_right.1 hS hi]
  rw [h1, h2, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

/-- The Berry–Esseen bound for the difference of the sums of a Bernoulli family over two disjoint
index sets (the computation in the proof of the dense paper's Lemma 2.3):
`|P(∑_{S₁} X − ∑_{S₂} X ≤ y) − Φ((y − p(n₁ − n₂)) / √(p(1 − p)(n₁ + n₂)))|
  ≤ 0.56 (1 − 2p + 2p²) / √(p(1 − p)(n₁ + n₂))`. -/
theorem dayOneAux_berryEsseen_diff (hBE : ShevtsovaBerryEsseen) (hp0 : 0 < p) (hp1 : p < 1)
    (hX : IsBernoulliFamily μ p X) {S₁ S₂ : Finset ι} (hS : Disjoint S₁ S₂)
    (hne : 0 < S₁.card + S₂.card) (y : ℝ) :
    |μ.real {ω | ∑ i ∈ S₁, X i ω ≤ ∑ i ∈ S₂, X i ω + y} -
        Φ ((y - p * ((S₁.card : ℝ) - S₂.card)) /
          Real.sqrt (p * (1 - p) * (S₁.card + S₂.card)))| ≤
      0.56 * (1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p) * (S₁.card + S₂.card)) := by
  classical
  have hpq : 0 ≤ p * (1 - p) := mul_nonneg hp0.le (by linarith)
  have hSne : (S₁ ∪ S₂).Nonempty := by
    rw [← Finset.card_pos, Finset.card_union_of_disjoint hS]; exact hne
  have hcard : ((S₁ ∪ S₂).card : ℝ) = S₁.card + S₂.card := by
    rw [Finset.card_union_of_disjoint hS]; push_cast; rfl
  have h := berryEsseen_signedBernoulli hBE hp0 hp1 hX (fun i => if i ∈ S₁ then 1 else -1)
    (fun i => by by_cases hi : i ∈ S₁ <;> simp [hi]) hSne (y - p * ((S₁.card : ℝ) - S₂.card))
  rw [hcard, ← Real.sqrt_mul hpq] at h
  have hset : {ω | ∑ i ∈ S₁ ∪ S₂, (if i ∈ S₁ then (1 : ℝ) else -1) * (X i ω - p) ≤
      y - p * ((S₁.card : ℝ) - S₂.card)} = {ω | ∑ i ∈ S₁, X i ω ≤ ∑ i ∈ S₂, X i ω + y} := by
    ext ω
    simp only [Set.mem_ofPred_eq, dayOneAux_sum_sign_mul X p hS ω]
    constructor <;> intro h <;> linarith
  rw [hset] at h
  convert h using 2
  ring

/-- **Lemma 2.3** (`D:thm:diff-of-binom-r.v.-gen.`). For `p ∈ (0, 1)`, independent
`Y₁ ∼ Bin(n₁, p)` and `Y₂ ∼ Bin(n₂, p)` with `n₁ > n₂`, and every real `d`,
`P(Y₁ > Y₂ + d) ≥ 1/2 + Φ₀((p(n₁ − n₂) − d) / √(p(1 − p)(n₁ + n₂)))
  − 0.56 (1 − 2p + 2p²) / √(p(1 − p)(n₁ + n₂))`. -/
theorem lemma2_3 (hBE : ShevtsovaBerryEsseen) (hp0 : 0 < p) (hp1 : p < 1)
    (hX : IsBernoulliFamily μ p X) {S₁ S₂ : Finset ι} (hS : Disjoint S₁ S₂)
    (h21 : S₂.card < S₁.card) (d : ℝ) :
    1 / 2 + Φ₀ ((p * ((S₁.card : ℝ) - S₂.card) - d) /
          Real.sqrt (p * (1 - p) * (S₁.card + S₂.card))) -
        0.56 * (1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p) * (S₁.card + S₂.card)) ≤
      μ.real {ω | ∑ i ∈ S₂, X i ω + d < ∑ i ∈ S₁, X i ω} := by
  -- `P(Y₁ ≤ Y₂ + d) ≤ Φ((d − p(n₁ − n₂)) / σ_X) + 0.56 (1 − 2p + 2p²) / σ_X` (Theorem 2.2)
  have h := dayOneAux_berryEsseen_diff hBE hp0 hp1 hX hS (by omega) d
  -- `Φ(−a) = 1/2 − Φ₀(a)`
  have hΦ : Φ ((d - p * ((S₁.card : ℝ) - S₂.card)) /
        Real.sqrt (p * (1 - p) * (S₁.card + S₂.card))) =
      1 / 2 - Φ₀ ((p * ((S₁.card : ℝ) - S₂.card) - d) /
        Real.sqrt (p * (1 - p) * (S₁.card + S₂.card))) := by
    have harg : (d - p * ((S₁.card : ℝ) - S₂.card)) /
          Real.sqrt (p * (1 - p) * (S₁.card + S₂.card)) =
        -((p * ((S₁.card : ℝ) - S₂.card) - d) /
          Real.sqrt (p * (1 - p) * (S₁.card + S₂.card))) := by ring
    rw [Φ, harg, Φ₀_neg]
    ring
  rw [hΦ] at h
  -- the complement event
  have hmeas : MeasurableSet {ω | ∑ i ∈ S₂, X i ω + d < ∑ i ∈ S₁, X i ω} :=
    measurableSet_lt ((Finset.measurable_sum _ fun i _ => hX.measurable i).add_const d)
      (Finset.measurable_sum _ fun i _ => hX.measurable i)
  have hcompl : {ω | ∑ i ∈ S₁, X i ω ≤ ∑ i ∈ S₂, X i ω + d} =
      {ω | ∑ i ∈ S₂, X i ω + d < ∑ i ∈ S₁, X i ω}ᶜ := by
    ext ω; simp
  rw [hcompl, measureReal_compl hmeas, probReal_univ] at h
  linarith [(abs_le.1 h).2]

/-- `Φ` is continuous. -/
theorem dayOneAux_continuous_Φ : Continuous Φ :=
  continuous_const.add continuous_Φ₀

/-- **Lemma 2.4** (`D:thm:1/sqrt-n`). For `p ∈ (0, 1)`, independent `X₁ ∼ Bin(n₁, p)` and
`X₂ ∼ Bin(n₂, p)`, and every integer `d`,
`P(X₁ = X₂ + d) ≤ 1.12 (1 − 2p + 2p²) / √(p(1 − p)(n₁ + n₂))`.

Reading: the paper's bound is undefined (infinite) when `n₁ + n₂ = 0`, so the statement assumes
`n₁ + n₂ ≥ 1` (in Lean, division by zero gives `0`). -/
theorem lemma2_4 (hBE : ShevtsovaBerryEsseen) (hp0 : 0 < p) (hp1 : p < 1)
    (hX : IsBernoulliFamily μ p X) {S₁ S₂ : Finset ι} (hS : Disjoint S₁ S₂)
    (hne : 0 < S₁.card + S₂.card) (d : ℤ) :
    μ.real {ω | ∑ i ∈ S₁, X i ω = ∑ i ∈ S₂, X i ω + d} ≤
      1.12 * (1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p) * (S₁.card + S₂.card)) := by
  -- `μ_X = p(n₁ − n₂)`, `σ_X = √(p(1 − p)n)` and the Berry–Esseen error `E`
  set m : ℝ := p * ((S₁.card : ℝ) - S₂.card) with hm
  set s : ℝ := Real.sqrt (p * (1 - p) * (S₁.card + S₂.card)) with hs
  set E : ℝ := 0.56 * (1 - 2 * p + 2 * p ^ 2) / s with hE
  -- the event `X₁ − X₂ ≤ y`
  let A : ℝ → Set Ω := fun y => {ω | ∑ i ∈ S₁, X i ω ≤ ∑ i ∈ S₂, X i ω + y}
  have hAmeas : ∀ y, MeasurableSet (A y) := fun y =>
    measurableSet_le (Finset.measurable_sum _ fun i _ => hX.measurable i)
      ((Finset.measurable_sum _ fun i _ => hX.measurable i).add_const y)
  have hBE' : ∀ y, |μ.real (A y) - Φ ((y - m) / s)| ≤ E := fun y =>
    dayOneAux_berryEsseen_diff hBE hp0 hp1 hX hS hne y
  -- for every `ε ∈ (0, 1)`,
  -- `P(X₁ = X₂ + d) ≤ Φ((d − μ_X + ε) / σ_X) − Φ((d − μ_X − ε) / σ_X) + 2E`
  have hε : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, μ.real {ω | ∑ i ∈ S₁, X i ω = ∑ i ∈ S₂, X i ω + d} ≤
      Φ ((d + ε - m) / s) - Φ ((d - ε - m) / s) + 2 * E := by
    intro ε hε
    -- `P(X₁ = X₂ + d) ≤ P(d − ε < X₁ − X₂ ≤ d + ε)`
    have hsub : {ω | ∑ i ∈ S₁, X i ω = ∑ i ∈ S₂, X i ω + d} ⊆ A (d + ε) \ A (d - ε) := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      simp only [A, Set.mem_sdiff, Set.mem_ofPred_eq, not_le]
      constructor <;> linarith [hε.1]
    have hAA : A (d - ε) ⊆ A (d + ε) := by
      intro ω hω
      simp only [A, Set.mem_ofPred_eq] at hω ⊢
      linarith [hε.1]
    have h1 := (abs_le.1 (hBE' (d + ε))).2
    have h2 := (abs_le.1 (hBE' (d - ε))).1
    calc μ.real {ω | ∑ i ∈ S₁, X i ω = ∑ i ∈ S₂, X i ω + d}
        ≤ μ.real (A (d + ε) \ A (d - ε)) := measureReal_mono hsub
      _ = μ.real (A (d + ε)) - μ.real (A (d - ε)) := measureReal_sdiff hAA (hAmeas _)
      _ ≤ Φ ((d + ε - m) / s) - Φ ((d - ε - m) / s) + 2 * E := by linarith
  -- letting `ε → 0`
  have hlim : Filter.Tendsto (fun ε : ℝ => Φ ((d + ε - m) / s) - Φ ((d - ε - m) / s) + 2 * E)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 * E)) := by
    have hc : Continuous (fun ε : ℝ => Φ ((d + ε - m) / s) - Φ ((d - ε - m) / s) + 2 * E) :=
      ((dayOneAux_continuous_Φ.comp (by fun_prop)).sub
        (dayOneAux_continuous_Φ.comp (by fun_prop))).add continuous_const
    have := (hc.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0)
    simpa using this
  have hfin := ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) hε)
  calc μ.real {ω | ∑ i ∈ S₁, X i ω = ∑ i ∈ S₂, X i ω + d} ≤ 2 * E := hfin
    _ = 1.12 * (1 - 2 * p + 2 * p ^ 2) / s := by rw [hE]; ring

end PowerOfFew.Dense

end
