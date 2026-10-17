module

public import Basic.Probability.Chernoff

/-!
# Sparse paper, Appendix A: a Chernoff bound for a binomial variable of random size

Lemma A.6 of the sparse paper. A variable `X ∼ Bin(Y, p)` with a random size `Y` (independent
coins) is represented as `X = ∑_{i < Y} ξᵢ`, with `ξ` a Bernoulli(`p`) family independent of `Y`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- The complementary coins `1 − ξᵢ` of a Bernoulli(`p`) family form a Bernoulli(`1 − p`) family
(in the proof of Lemma A.6, `Z' = m − Z ∼ Bin(m, 1 − p)`). -/
private theorem appAux_isBernoulliFamily_one_sub {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ℝ} {ξ : ι → Ω → ℝ}
    (hξ : IsBernoulliFamily μ p ξ) : IsBernoulliFamily μ (1 - p) (fun i ω => 1 - ξ i ω) where
  measurable i := measurable_const.sub (hξ.measurable i)
  indep := hξ.indep.comp (fun _ x => 1 - x) (fun _ => measurable_const.sub measurable_id)
  zero_or_one i ω := by
    rcases hξ.zero_or_one i ω with h | h <;> simp [h]
  prob_one i := by
    have hset : {ω | 1 - ξ i ω = 1} = {ω | ξ i ω = 1}ᶜ := by
      ext ω
      rcases hξ.zero_or_one i ω with h | h <;> simp [h]
    have hms : MeasurableSet {ω | ξ i ω = 1} := hξ.measurable i (measurableSet_singleton 1)
    rw [hset, probReal_compl_eq_one_sub hms, hξ.prob_one i]

-- The coupling of the proof is pointwise: neither the measurability of `Y` (`hYm`) nor its
-- independence from `ξ` (`hindep`) is needed.
set_option linter.unusedVariables false in
/-- **Lemma A.6** (`S:lem:gen-chernoff`). Let `p ∈ (0, 1)` and `m > 0`. If `Y` takes values in
`[0, m] ∩ ℤ` and `X ∼ Bin(Y, p)`, then for every `t > 0`,
`P(X ≥ pm + t) ≤ exp(−max{t² / (2(pm + t)), t² / (2(1 − p)m)})`.

Proof (the paper's): the two Chernoff bounds (29) and (31) for `Z ∼ Bin(m, p)`, the second one
obtained from the lower-tail bound (30) for `Z' = m − Z ∼ Bin(m, 1 − p)`, and the coupling
`Z = X + X₁ ≥ X` with `X₁ = ∑_{Y ≤ i < m} ξᵢ`. Reading: the paper's `Bin(m, p)` needs `m ∈ ℕ`;
here `Z = ∑_{i < ⌊m⌋} ξᵢ` (since `Y ≤ m` is an integer, `Y ≤ ⌊m⌋`), and the bounds for
`Bin(⌊m⌋, p)` imply those for `m` since `p⌊m⌋ ≤ pm` and `(1 − p)⌊m⌋ ≤ (1 − p)m`. The coupling is
pointwise, so the independence of `Y` and `ξ` is not needed. -/
theorem lemmaA_6 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {m : ℝ} (hm : 0 < m) {Y : Ω → ℕ} (hYm : Measurable Y)
    (hY : ∀ ω, (Y ω : ℝ) ≤ m) {ξ : ℕ → Ω → ℝ} (hξ : IsBernoulliFamily μ p ξ)
    (hindep : IndepFun Y (fun ω i => ξ i ω) μ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | p * m + t ≤ ∑ i ∈ Finset.range (Y ω), ξ i ω} ≤
      Real.exp (-max (t ^ 2 / (2 * (p * m + t))) (t ^ 2 / (2 * (1 - p) * m))) := by
  classical
  set m' : ℕ := ⌊m⌋₊ with hm'_def
  have hm'm : (m' : ℝ) ≤ m := Nat.floor_le hm.le
  have hξ0 : ∀ i ω, 0 ≤ ξ i ω := fun i ω => by
    rcases hξ.zero_or_one i ω with h | h <;> simp [h]
  -- The coupling: `X = ∑_{i < Y} ξᵢ ≤ Z = X + ∑_{Y ≤ i < ⌊m⌋} ξᵢ`, as `Y ≤ ⌊m⌋`.
  have hXZ : {ω | p * m + t ≤ ∑ i ∈ Finset.range (Y ω), ξ i ω} ⊆
      {ω | p * m + t ≤ ∑ i ∈ Finset.range m', ξ i ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    refine hω.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => hξ0 i ω)
    exact Finset.range_mono (Nat.le_floor (hY ω))
  refine (measureReal_mono hXZ).trans ?_
  -- It remains to bound the upper tail of `Z ∼ Bin(⌊m⌋, p)`.
  rcases Nat.eq_zero_or_pos m' with h0 | hpos
  · -- `⌊m⌋ = 0`: `Z = 0 < pm + t`, the event is empty.
    have hempty : {ω | p * m + t ≤ ∑ i ∈ Finset.range m', ξ i ω} = ∅ := by
      ext ω
      simp only [h0, Finset.range_zero, Finset.sum_empty, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false, not_le]
      positivity
    rw [hempty, measureReal_empty]
    positivity
  have hm'pos : (0 : ℝ) < m' := by exact_mod_cast hpos
  have hcard : ((Finset.range m').card : ℝ) = m' := by simp
  have hpm : p * (m' : ℝ) ≤ p * m := mul_le_mul_of_nonneg_left hm'm hp0.le
  have hgap : t ≤ p * m + t - p * m' := by linarith
  have hsq : t ^ 2 ≤ (p * m + t - p * m') ^ 2 := pow_le_pow_left₀ ht.le hgap 2
  -- Equation (29): `P(Z ≥ T) ≤ exp(−(T − pm)² / (2T))` with `T = pm + t`.
  have h29 : μ.real {ω | p * m + t ≤ ∑ i ∈ Finset.range m', ξ i ω} ≤
      Real.exp (-(t ^ 2 / (2 * (p * m + t)))) := by
    have hT : p * ((Finset.range m').card : ℝ) < p * m + t := by rw [hcard]; linarith
    refine (hξ.measureReal_sum_ge_le_exp hp0.le hp1.le (Finset.range m') hT).trans ?_
    rw [hcard]
    gcongr
  -- Equation (31): `P(Z ≥ T) = P(Z' ≤ m − T) ≤ exp(−(T − pm)² / (2(1 − p)m))`, by
  -- equation (30) for `Z' = m − Z ∼ Bin(m, 1 − p)`.
  have h31 : μ.real {ω | p * m + t ≤ ∑ i ∈ Finset.range m', ξ i ω} ≤
      Real.exp (-(t ^ 2 / (2 * (1 - p) * m))) := by
    have hξ' := appAux_isBernoulliFamily_one_sub hξ
    have hT' : (m' : ℝ) - (p * m + t) < (1 - p) * ((Finset.range m').card : ℝ) := by
      rw [hcard]; linarith
    have hset : {ω | p * m + t ≤ ∑ i ∈ Finset.range m', ξ i ω} =
        {ω | ∑ i ∈ Finset.range m', (1 - ξ i ω) ≤ (m' : ℝ) - (p * m + t)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one]
      constructor <;> intro h <;> linarith
    rw [hset]
    refine (hξ'.measureReal_sum_le_le_exp (by linarith) (by linarith) (Finset.range m')
      hT').trans ?_
    rw [hcard]
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    have h1 : (1 - p) * (m' : ℝ) - ((m' : ℝ) - (p * m + t)) = p * m + t - p * m' := by ring
    rw [h1]
    refine div_le_div₀ (sq_nonneg _) hsq (mul_pos two_pos (mul_pos (by linarith) hm'pos)) ?_
    have : (1 - p) * (m' : ℝ) ≤ (1 - p) * m := mul_le_mul_of_nonneg_left hm'm (by linarith)
    linarith
  rcases le_total (t ^ 2 / (2 * (p * m + t))) (t ^ 2 / (2 * (1 - p) * m)) with h | h
  · rw [max_eq_right h]; exact h31
  · rw [max_eq_left h]; exact h29

end PowerOfFew.Sparse

end
