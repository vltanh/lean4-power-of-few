module

public import PowerOfFew.Model.BerryEsseen

/-!
# Sparse paper, Appendix A: consequences of the Berry–Esseen inequality

Corollary A.2 and Lemma A.3 of B. Tran–Vu, *The "Power of Few" phenomenon: the sparse case*
(Random Structures & Algorithms 66 (2025), e21260; arXiv:2302.05605v2). The paper states that they
"naturally follow" from the Berry–Esseen inequality (its Theorem A.1, assumed here as
`ShevtsovaBerryEsseen`) and gives no proof.

Reading: Corollary A.2 does not say that its Bernoulli variables are independent; the
Berry–Esseen inequality needs it, and the paper applies the corollary to independent variables.

Proofs. Corollary A.2 is the Berry–Esseen inequality for the centred sum
`∑ sᵢ Yᵢ − E ∑ sᵢ Yᵢ = ∑ sᵢ (Yᵢ − p)` (`PowerOfFew.berryEsseen_signedBernoulli`). Lemma A.3 is
proved by the argument of the dense paper's Lemma 2.4 (the sparse paper derives it from Corollary A.2
without details: "This implies the following lemma"):
`P(X = d) ≤ P(X ≤ d) − P(X ≤ d − ε)`, both terms by Corollary A.2, and `ε → 0`. The argument
holds for every real `d` and needs only `n₁ + n₂ ≥ 1`; that general form is
`sparseAux_pointProb_le`, which the proof of Proposition 2.2 uses (with `d ∈ {−1, 0, 1}`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

namespace PowerOfFew.Sparse

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*}
  {p : ℝ} {Y : ι → Ω → ℝ}

/-- Each variable of a Bernoulli family is integrable: it is measurable with values in `{0, 1}`. -/
theorem sparseAux_integrable (hY : IsBernoulliFamily μ p Y) (i : ι) : Integrable (Y i) μ := by
  refine Integrable.of_bound (hY.measurable i).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => ?_)
  rcases hY.zero_or_one i ω with h | h <;> simp [h]

/-- **Corollary A.2** (`S:lem:strongesseen`). Let `p ∈ (0, 1)` and let `X₁, …, Xₙ` be independent
variables such that each `Xᵢ ∼ Ber(p)` or `Xᵢ ∼ −Ber(p)`; let `X = ∑ Xᵢ` and `μ_X = E X`. Then
`sup_x |P(X − μ_X ≤ x) − Φ(x / (σ √n))| ≤ 0.56 (1 − 2σ²) / (σ √n)`, `σ = √(p(1 − p))`.
Here `Xᵢ = sᵢ Yᵢ` with signs `sᵢ = ±1` and a Bernoulli(`p`) family `Y`. -/
theorem corollaryA_2 (hBE : ShevtsovaBerryEsseen) (hp0 : 0 < p) (hp1 : p < 1)
    (hY : IsBernoulliFamily μ p Y) (s : ι → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) {S : Finset ι}
    (hS : S.Nonempty) (x : ℝ) :
    |μ.real {ω | ∑ i ∈ S, s i * Y i ω - ∫ ω', ∑ i ∈ S, s i * Y i ω' ∂μ ≤ x} -
        Φ (x / (Real.sqrt (p * (1 - p)) * Real.sqrt S.card))| ≤
      0.56 * (1 - 2 * (p * (1 - p))) / (Real.sqrt (p * (1 - p)) * Real.sqrt S.card) := by
  -- `μ_X = ∑ sᵢ p`, so that `X − μ_X = ∑ sᵢ (Yᵢ − p)`.
  have hint : ∫ ω', ∑ i ∈ S, s i * Y i ω' ∂μ = ∑ i ∈ S, s i * p := by
    rw [integral_finsetSum S fun i _ => (sparseAux_integrable hY i).const_mul (s i)]
    exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul, hY.integral_eq i]
  have hset : {ω | ∑ i ∈ S, s i * Y i ω - ∫ ω', ∑ i ∈ S, s i * Y i ω' ∂μ ≤ x} =
      {ω | ∑ i ∈ S, s i * (Y i ω - p) ≤ x} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hint, mul_sub, Finset.sum_sub_distrib]
  rw [hset]
  exact berryEsseen_signedBernoulli hBE hp0 hp1 hY s hs hS x

/-- The general form of Lemma A.3 (the dense paper's Lemma 2.4, whose proof is the one given
here): for independent `X₁ ∼ Bin(n₁, p)`, `X₂ ∼ Bin(n₂, p)` with `n₁ + n₂ ≥ 1` and every real
`d`, `P(X₁ = X₂ + d) ≤ 1.12 (1 − 2σ²) / (σ √(n₁ + n₂))`. Proposition 2.2 applies Lemma A.3 with
`d ∈ {−1, 0, 1}`, outside the range of its statement; this form covers it. -/
theorem sparseAux_pointProb_le (hBE : ShevtsovaBerryEsseen) (hp0 : 0 < p) (hp1 : p < 1)
    (hY : IsBernoulliFamily μ p Y) {S₁ S₂ : Finset ι} (hS : Disjoint S₁ S₂)
    (hne : 0 < S₁.card + S₂.card) (d : ℝ) :
    μ.real {ω | ∑ i ∈ S₁, Y i ω = ∑ i ∈ S₂, Y i ω + d} ≤
      1.12 * (1 - 2 * (p * (1 - p))) /
        (Real.sqrt (p * (1 - p)) * Real.sqrt (S₁.card + S₂.card)) := by
  classical
  -- `X₁ − X₂ = ∑_{i ∈ S₁ ∪ S₂} sᵢ Yᵢ` with `sᵢ = 1` on `S₁` and `sᵢ = −1` on `S₂`.
  set S := S₁ ∪ S₂ with hSdef
  set s : ι → ℝ := fun i => if i ∈ S₁ then 1 else -1 with hsdef
  have hs : ∀ i, s i = 1 ∨ s i = -1 := fun i => by
    by_cases h : i ∈ S₁ <;> simp [hsdef, h]
  have hcard : (S.card : ℝ) = S₁.card + S₂.card := by
    rw [hSdef, Finset.card_union_of_disjoint hS]; push_cast; ring
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos, hSdef, Finset.card_union_of_disjoint hS]; exact hne
  have hX : ∀ ω, ∑ i ∈ S, s i * Y i ω = ∑ i ∈ S₁, Y i ω - ∑ i ∈ S₂, Y i ω := by
    intro ω
    rw [hSdef, Finset.sum_union hS]
    have h1 : ∑ i ∈ S₁, s i * Y i ω = ∑ i ∈ S₁, Y i ω :=
      Finset.sum_congr rfl fun i hi => by simp [hsdef, hi]
    have h2 : ∑ i ∈ S₂, s i * Y i ω = -∑ i ∈ S₂, Y i ω := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i hi => by simp [hsdef, Finset.disjoint_right.mp hS hi]
    rw [h1, h2]; ring
  set m := ∫ ω', ∑ i ∈ S, s i * Y i ω' ∂μ with hm
  set σn := Real.sqrt (p * (1 - p)) * Real.sqrt S.card with hσn
  set err := 0.56 * (1 - 2 * (p * (1 - p))) / σn with herr
  have hBEx := corollaryA_2 hBE hp0 hp1 hY s hs hSne
  have hmeas : ∀ a : ℝ, MeasurableSet {ω | ∑ i ∈ S, s i * Y i ω ≤ a} := fun a =>
    measurableSet_le (Finset.measurable_sum S fun i _ => (hY.measurable i).const_mul (s i))
      measurable_const
  -- Corollary A.2 at `x = a − μ_X`: `|P(X ≤ a) − Φ((a − μ_X)/(σ√n))| ≤ err`.
  have hcor : ∀ a : ℝ, |μ.real {ω | ∑ i ∈ S, s i * Y i ω ≤ a} - Φ ((a - m) / σn)| ≤ err := by
    intro a
    have h := hBEx (a - m)
    have hset : {ω | ∑ i ∈ S, s i * Y i ω - m ≤ a - m} = {ω | ∑ i ∈ S, s i * Y i ω ≤ a} := by
      ext ω; simp only [Set.mem_ofPred_eq, sub_le_sub_iff_right]
    rwa [hset] at h
  -- For every `ε > 0`: `P(X = d) ≤ P(X ≤ d) − P(X ≤ d − ε) ≤ Φ(⋯) − Φ(⋯) + 2 err`.
  have key : ∀ ε > 0, μ.real {ω | ∑ i ∈ S₁, Y i ω = ∑ i ∈ S₂, Y i ω + d} ≤
      Φ ((d - m) / σn) - Φ ((d - ε - m) / σn) + 2 * err := by
    intro ε hε
    have hsub : {ω | ∑ i ∈ S₁, Y i ω = ∑ i ∈ S₂, Y i ω + d} ⊆
        {ω | ∑ i ∈ S, s i * Y i ω ≤ d} \ {ω | ∑ i ∈ S, s i * Y i ω ≤ d - ε} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq, hX ω, hω]
      constructor <;> linarith
    have hsub' : {ω | ∑ i ∈ S, s i * Y i ω ≤ d - ε} ⊆ {ω | ∑ i ∈ S, s i * Y i ω ≤ d} :=
      fun ω hω => by simp only [Set.mem_ofPred_eq] at hω ⊢; linarith
    have h1 := (abs_le.mp (hcor d)).2
    have h2 := (abs_le.mp (hcor (d - ε))).1
    calc μ.real {ω | ∑ i ∈ S₁, Y i ω = ∑ i ∈ S₂, Y i ω + d}
        ≤ μ.real ({ω | ∑ i ∈ S, s i * Y i ω ≤ d} \ {ω | ∑ i ∈ S, s i * Y i ω ≤ d - ε}) :=
          measureReal_mono hsub
      _ = μ.real {ω | ∑ i ∈ S, s i * Y i ω ≤ d} -
            μ.real {ω | ∑ i ∈ S, s i * Y i ω ≤ d - ε} := measureReal_sdiff hsub' (hmeas _)
      _ ≤ Φ ((d - m) / σn) - Φ ((d - ε - m) / σn) + 2 * err := by linarith
  -- Let `ε → 0`: `Φ` is continuous.
  have hΦ : Continuous Φ := continuous_const.add continuous_Φ₀
  have hcont : Continuous (fun ε : ℝ => Φ ((d - m) / σn) - Φ ((d - ε - m) / σn) + 2 * err) := by
    refine (continuous_const.sub (hΦ.comp ?_)).add continuous_const
    exact ((continuous_const.sub continuous_id).sub continuous_const).div_const _
  have hlim : Tendsto (fun ε : ℝ => Φ ((d - m) / σn) - Φ ((d - ε - m) / σn) + 2 * err)
      (𝓝[>] 0) (𝓝 (2 * err)) := by
    have h := hcont.tendsto 0
    simp only [sub_zero, sub_self, zero_add] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hfin := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  calc μ.real {ω | ∑ i ∈ S₁, Y i ω = ∑ i ∈ S₂, Y i ω + d} ≤ 2 * err := hfin
    _ = 1.12 * (1 - 2 * (p * (1 - p))) /
          (Real.sqrt (p * (1 - p)) * Real.sqrt (S₁.card + S₂.card)) := by
      rw [herr, hσn, hcard]; ring

/-- **Lemma A.3** (`S:lem:esseen-err-term`). Let `p ∈ (0, 1)`, `σ = √(p(1 − p))`, and let
`X₁ ∼ Bin(n₁, p)` and `X₂ ∼ Bin(n₂, p)` be independent. For every positive integer
`d < (n₁ + n₂)/2`, `P(X₁ = X₂ + d) ≤ 1.12 (1 − 2σ²) / (σ √(n₁ + n₂))`. -/
theorem lemmaA_3 (hBE : ShevtsovaBerryEsseen) (hp0 : 0 < p) (hp1 : p < 1)
    (hY : IsBernoulliFamily μ p Y) {S₁ S₂ : Finset ι} (hS : Disjoint S₁ S₂) {d : ℕ} (hd : 0 < d)
    (hdn : (d : ℝ) < (S₁.card + S₂.card) / 2) :
    μ.real {ω | ∑ i ∈ S₁, Y i ω = ∑ i ∈ S₂, Y i ω + d} ≤
      1.12 * (1 - 2 * (p * (1 - p))) /
        (Real.sqrt (p * (1 - p)) * Real.sqrt (S₁.card + S₂.card)) := by
  have hne : 0 < S₁.card + S₂.card := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have : (0 : ℝ) < S₁.card + S₂.card := by linarith
    exact_mod_cast this
  exact sparseAux_pointProb_le hBE hp0 hp1 hY hS hne d

end PowerOfFew.Sparse

end
