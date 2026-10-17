module

public import Mathlib

/-!
# Families of independent Bernoulli random variables

A family `X : ι → Ω → ℝ` of independent random variables, each with values in `{0, 1}` and equal
to `1` with probability `p`. Sums of such variables over disjoint finite index sets are the
independent binomial variables of the two papers: `∑ i ∈ S, X i` has the law `Bin(#S, p)`
(`IsBernoulliFamily.measureReal_sum_eq`).

## Main declarations

* `ProbabilityTheory.IsBernoulliFamily`: the predicate.
* `IsBernoulliFamily.measureReal_sum_eq`: the law of a sum is binomial.
* `IsBernoulliFamily.integral_eq`, `integral_sq_sub`, `integral_abs_pow_three_sub`: the mean `p`,
  the variance `p(1 - p)` and the third absolute central moment `p(1 - p)(1 - 2p + 2p²)`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- `X` is a family of independent random variables with values in `{0, 1}`, each equal to `1`
with probability `p`. -/
structure IsBernoulliFamily (μ : Measure Ω) (p : ℝ) (X : ι → Ω → ℝ) : Prop where
  measurable : ∀ i, Measurable (X i)
  indep : iIndepFun X μ
  zero_or_one : ∀ i ω, X i ω = 0 ∨ X i ω = 1
  prob_one : ∀ i, μ.real {ω | X i ω = 1} = p

namespace IsBernoulliFamily

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ℝ} {X : ι → Ω → ℝ}

/-- Each variable is bounded, hence integrable. -/
theorem gnpAux_integrable (hX : IsBernoulliFamily μ p X) (i : ι) : Integrable (X i) μ := by
  refine Integrable.of_bound (hX.measurable i).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => ?_)
  rcases hX.zero_or_one i ω with h | h <;> simp [h]

/-- The mean of each variable is `p`. -/
theorem integral_eq (hX : IsBernoulliFamily μ p X) (i : ι) : ∫ ω, X i ω ∂μ = p := by
  have h : (fun ω => X i ω) = Set.indicator {ω | X i ω = 1} 1 := by
    ext ω
    rcases hX.zero_or_one i ω with h | h <;> simp [Set.indicator, h]
  rw [h, integral_indicator_one (s := {ω | X i ω = 1})
    (hX.measurable i (measurableSet_singleton 1)), hX.prob_one i]

/-- The variance of each variable is `p (1 - p)`. -/
theorem integral_sq_sub (hX : IsBernoulliFamily μ p X) (i : ι) :
    ∫ ω, (X i ω - p) ^ 2 ∂μ = p * (1 - p) := by
  have h : ∀ ω, (X i ω - p) ^ 2 = (1 - 2 * p) * X i ω + p ^ 2 := by
    intro ω
    rcases hX.zero_or_one i ω with h | h <;> rw [h] <;> ring
  simp_rw [h]
  rw [integral_add ((gnpAux_integrable hX i).const_mul _) (integrable_const _), integral_const_mul,
    hX.integral_eq i, integral_const]
  simp
  ring

/-- The third absolute central moment of each variable is `p (1 - p) (1 - 2p + 2p²)`. -/
theorem integral_abs_pow_three_sub (hX : IsBernoulliFamily μ p X) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : ι) : ∫ ω, |X i ω - p| ^ 3 ∂μ = p * (1 - p) * (1 - 2 * p + 2 * p ^ 2) := by
  have h : ∀ ω, |X i ω - p| ^ 3 = ((1 - p) ^ 3 - p ^ 3) * X i ω + p ^ 3 := by
    intro ω
    rcases hX.zero_or_one i ω with h | h <;> rw [h]
    · rw [zero_sub, abs_neg, abs_of_nonneg hp0]
      ring
    · rw [abs_of_nonneg (by linarith)]
      ring
  simp_rw [h]
  rw [integral_add ((gnpAux_integrable hX i).const_mul _) (integrable_const _), integral_const_mul,
    hX.integral_eq i, integral_const]
  simp
  ring

/-- The sum over a finite set `S` has the binomial law `Bin(#S, p)`. -/
theorem measureReal_sum_eq (hX : IsBernoulliFamily μ p X) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset ι) (k : ℕ) :
    μ.real {ω | ∑ i ∈ S, X i ω = k} = (S.card.choose k : ℝ) * p ^ k * (1 - p) ^ (S.card - k) := by
  classical
  induction S using Finset.induction_on generalizing k with
  | empty =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have h : {ω : Ω | ∑ i ∈ (∅ : Finset ι), X i ω = k} = ∅ := by
        ext ω
        simp only [Finset.sum_empty, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact_mod_cast hk.ne
      rw [h]
      simp [Nat.choose_eq_zero_of_lt hk]
  | insert a S ha ih =>
    -- `Y = ∑_{i ∈ S} X i` is independent of `X a`.
    have hind : IndepFun (∑ j ∈ S, X j) (X a) μ :=
      hX.indep.indepFun_finsetSum_of_notMem hX.measurable ha
    have hmul : ∀ s t : Set ℝ, MeasurableSet s → MeasurableSet t →
        μ.real ((∑ j ∈ S, X j) ⁻¹' s ∩ X a ⁻¹' t) =
          μ.real ((∑ j ∈ S, X j) ⁻¹' s) * μ.real (X a ⁻¹' t) := by
      intro s t hs ht
      simp only [measureReal_def, hind.measure_inter_preimage_eq_mul s t hs ht,
        ENNReal.toReal_mul]
    have hY : ∀ k' : ℕ, μ.real ((∑ j ∈ S, X j) ⁻¹' {(k' : ℝ)}) =
        (S.card.choose k' : ℝ) * p ^ k' * (1 - p) ^ (S.card - k') := by
      intro k'
      rw [← ih k']
      congr 1
      ext ω
      simp [Finset.sum_apply]
    have hY0 : ∀ ω, 0 ≤ ∑ i ∈ S, X i ω := fun ω => Finset.sum_nonneg fun i _ => by
      rcases hX.zero_or_one i ω with h | h <;> simp [h]
    have hXa1 : μ.real (X a ⁻¹' {1}) = p := hX.prob_one a
    have hXa0 : μ.real (X a ⁻¹' {0}) = 1 - p := by
      have h : X a ⁻¹' {0} = (X a ⁻¹' {1})ᶜ := by
        ext ω
        rcases hX.zero_or_one a ω with h | h <;> simp [h]
      rw [h, probReal_compl_eq_one_sub (hX.measurable a (measurableSet_singleton 1)), hXa1]
    -- Split on the value of `X a`.
    have hsplit : {ω | ∑ i ∈ insert a S, X i ω = k} =
        ((∑ j ∈ S, X j) ⁻¹' {(k : ℝ) - 1} ∩ X a ⁻¹' {1}) ∪
          ((∑ j ∈ S, X j) ⁻¹' {(k : ℝ)} ∩ X a ⁻¹' {0}) := by
      ext ω
      simp only [Finset.sum_insert ha, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
        Set.mem_preimage, Finset.sum_apply, Set.mem_singleton_iff]
      rcases hX.zero_or_one a ω with h | h <;> rw [h]
      · constructor
        · intro h'
          exact Or.inr ⟨by linarith, rfl⟩
        · rintro (⟨_, h'⟩ | ⟨h', _⟩)
          · norm_num at h'
          · linarith
      · constructor
        · intro h'
          exact Or.inl ⟨by linarith, rfl⟩
        · rintro (⟨h', _⟩ | ⟨_, h'⟩)
          · linarith
          · norm_num at h'
    have hdisj : Disjoint ((∑ j ∈ S, X j) ⁻¹' {(k : ℝ) - 1} ∩ X a ⁻¹' {1})
        ((∑ j ∈ S, X j) ⁻¹' {(k : ℝ)} ∩ X a ⁻¹' {0}) := by
      rw [Set.disjoint_left]
      rintro ω ⟨_, h1⟩ ⟨_, h0⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h0
      rw [h1] at h0
      norm_num at h0
    have hmeasY : Measurable (∑ j ∈ S, X j) := by
      have := Finset.measurable_sum S fun j _ => hX.measurable j
      simpa [← Finset.sum_apply] using this
    rw [hsplit, measureReal_union hdisj
      ((hmeasY (measurableSet_singleton _)).inter (hX.measurable a (measurableSet_singleton _))),
      hmul _ _ (measurableSet_singleton _) (measurableSet_singleton _),
      hmul _ _ (measurableSet_singleton _) (measurableSet_singleton _), hXa1, hXa0, hY k,
      Finset.card_insert_of_notMem ha]
    rcases k with _ | j
    · have h : (∑ j ∈ S, X j) ⁻¹' {((0 : ℕ) : ℝ) - 1} = ∅ := by
        ext ω
        simp only [Set.mem_preimage, Finset.sum_apply, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false, Nat.cast_zero]
        intro h'
        linarith [hY0 ω]
      rw [h]
      simp
      ring
    · have h : ((j + 1 : ℕ) : ℝ) - 1 = (j : ℝ) := by
        push_cast
        ring
      rw [h, hY j, Nat.choose_succ_succ', Nat.succ_sub_succ]
      by_cases hj : j + 1 ≤ S.card
      · obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hj
        rw [hr]
        have h1 : j + 1 + r - j = r + 1 := by omega
        have h2 : j + 1 + r - (j + 1) = r := by omega
        rw [h1, h2]
        push_cast
        ring
      · push Not at hj
        rw [Nat.choose_eq_zero_of_lt hj]
        push_cast
        ring

/-- Restricting a Bernoulli family along an injective map gives a Bernoulli family. -/
theorem comp {κ : Type*} (hX : IsBernoulliFamily μ p X) {f : κ → ι}
    (hf : Function.Injective f) : IsBernoulliFamily μ p (fun k => X (f k)) := by
  exact
    { measurable := fun k => hX.measurable (f k)
      indep := hX.indep.precomp hf
      zero_or_one := fun k => hX.zero_or_one (f k)
      prob_one := fun k => hX.prob_one (f k) }

end IsBernoulliFamily

end ProbabilityTheory
