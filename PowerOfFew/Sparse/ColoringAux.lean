module

public import PowerOfFew.Model.EdgeConditioning
public import PowerOfFew.Model.Normal
public import Basic.Probability.Chernoff

/-!
# Random initial colourings: shared tools

Tools for the theorems on random initial colourings (the sparse paper's Theorems 1.4 and 1.5, the
dense paper's Theorem 1.5 and Appendix A). None of them is a numbered result of either paper.

* Colour symmetry of majority dynamics (`colorAux_blueAfter_compl`): exchanging the colours of the
  initial colouring exchanges them on every later day.
* The complete graph: if Blue has at least `n/2 + 1` vertices, Blue is unanimous from day one on
  (`colorAux_blueAfter_top_ne_empty`); `G(n, 1)` is the complete graph (`colorAux_gnpProb_one`).
* The random colouring (`colorAux_law`, the product of Bernoulli laws on `Fin n → Bool`, where
  `true` is Red), its Red indicators as a Bernoulli family (`colorAux_isBernoulliFamily`), and
  conditioning on the colouring (`colorAux_le_coloredProb`): if the colouring is good with
  probability `1 − b` and every good colouring wins with probability `1 − a` over the graph, then
  the colouring and the graph together win with probability `1 − a − b`. The weight of a colouring
  (`colorAux_weight_eq`) and the colour symmetry of the `1/2` colouring
  (`colorAux_law_half_compl`).
* The Berry–Esseen estimate of the initial gap of a random `1/2` colouring (`colorAux_gap_le`),
  from any Berry–Esseen bound for the number of Red vertices.
* **The near-complete case** `p > 1 − 10/n` (`colorAux_nearComplete`), which the sparse paper's
  Theorem 1.2 excludes (it assumes `pn ≤ n − 10`): if Red leads by `m > 1` vertices, Red is
  unanimous after two days with probability at least `1 − 40/(m − 1) − 2048/n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew

/-! ### Colour symmetry -/

/-- Exchanging the colours today exchanges them tomorrow. -/
theorem colorAux_majorityStep_compl {n : ℕ} (G : SimpleGraph (Fin n)) (B : Set (Fin n)) :
    majorityStep G Bᶜ = (majorityStep G B)ᶜ := by
  ext v
  simp only [majorityStep, compl_compl, Set.mem_ofPred_eq, Set.mem_compl_iff]
  by_cases h : v ∈ B <;> simp [h] <;> omega

/-- **Colour symmetry** of majority dynamics: from the swapped initial colouring, the Blue set of
every day is the complement of the original one. -/
theorem colorAux_blueAfter_compl {n : ℕ} (G : SimpleGraph (Fin n)) (B₀ : Set (Fin n)) (t : ℕ) :
    blueAfter G B₀ᶜ t = (blueAfter G B₀ t)ᶜ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [blueAfter_succ, blueAfter_succ, ih, colorAux_majorityStep_compl]

/-- If the swapped colouring has no Blue vertex on day `t`, every vertex is Blue on day `t`. -/
theorem colorAux_blueAfter_eq_univ {n : ℕ} {G : SimpleGraph (Fin n)} {B₀ : Set (Fin n)} {t : ℕ}
    (h : blueAfter G B₀ᶜ t = ∅) : blueAfter G B₀ t = Set.univ := by
  rw [colorAux_blueAfter_compl, Set.compl_empty_iff] at h
  exact h

/-- The number of vertices outside a set. -/
theorem colorAux_ncard_compl {n : ℕ} (B : Set (Fin n)) :
    ((Bᶜ).ncard : ℝ) = n - B.ncard := by
  have h := Set.ncard_add_ncard_compl B
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have : ((B.ncard + Bᶜ.ncard : ℕ) : ℝ) = n := by exact_mod_cast h
  push_cast at this
  linarith

/-- On the complete graph, if Blue has at least `n/2 + 1` vertices, every vertex is Blue the next
day: each vertex sees at least `|B| − 1 ≥ n/2` Blue and at most `n − |B| ≤ n/2 − 1` Red
neighbours. -/
theorem colorAux_majorityStep_top {n : ℕ} {B : Set (Fin n)} (hB : (n : ℝ) / 2 + 1 ≤ B.ncard) :
    majorityStep ⊤ B = Set.univ := by
  ext v
  simp only [Set.mem_univ, iff_true, majorityStep, Set.mem_ofPred_eq]
  left
  have h1 : nbrCount ⊤ Bᶜ v ≤ (Bᶜ).ncard := Set.ncard_le_ncard (fun u hu => hu.2)
  have h2 : B.ncard ≤ nbrCount ⊤ B v + 1 := by
    have hsub : B ⊆ insert v {u | (⊤ : SimpleGraph (Fin n)).Adj v u ∧ u ∈ B} := by
      intro u hu
      by_cases huv : u = v
      · exact Or.inl huv
      · exact Or.inr ⟨by simpa [SimpleGraph.top_adj, eq_comm] using huv, hu⟩
    exact (Set.ncard_le_ncard hsub).trans (Set.ncard_insert_le _ _)
  have h3 := colorAux_ncard_compl B
  have h1' : ((nbrCount ⊤ Bᶜ v : ℕ) : ℝ) ≤ ((Bᶜ).ncard : ℝ) := by exact_mod_cast h1
  have h2' : (B.ncard : ℝ) ≤ (nbrCount ⊤ B v : ℝ) + 1 := by exact_mod_cast h2
  have : ((nbrCount ⊤ Bᶜ v : ℕ) : ℝ) < (nbrCount ⊤ B v : ℕ) := by linarith
  exact_mod_cast this

/-- On the complete graph, if Blue has at least `n/2 + 1` vertices, Red never wins: Blue is
unanimous from day one on. -/
theorem colorAux_blueAfter_top_ne_empty {n : ℕ} {B : Set (Fin n)}
    (hB : (n : ℝ) / 2 + 1 ≤ B.ncard) (t : ℕ) : blueAfter ⊤ B t ≠ ∅ := by
  have hBn := colorAux_ncard_compl B
  have hn : 0 < n := by
    have : (0 : ℝ) ≤ (Bᶜ).ncard := Nat.cast_nonneg _
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  intro ht
  cases t with
  | zero =>
    rw [blueAfter_zero] at ht
    rw [ht, Set.ncard_empty] at hB
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    push_cast at hB
    linarith
  | succ t =>
    have h1 : blueAfter ⊤ B 1 = Set.univ := by
      rw [blueAfter_succ, blueAfter_zero, colorAux_majorityStep_top hB]
    rw [blueAfter_eq_univ_of_le ⊤ h1 (by omega)] at ht
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Set.univ_nonempty.ne_empty ht

/-! ### The random colouring -/

/-- The law of the random colouring: each vertex is Red (`true`) with probability `q`,
independently (the second factor of `coloredGnp`). -/
abbrev colorAux_law (n : ℕ) (q : ℝ) : Measure (Fin n → Bool) :=
  Measure.pi fun _ : Fin n => bernoulliMeasure true false (toUnit q)

/-- The indicator that `v` is Red. -/
def colorAux_red {n : ℕ} (v : Fin n) (χ : Fin n → Bool) : ℝ := if χ v then 1 else 0

/-- The Red indicators of the random colouring form a Bernoulli(`q`) family. -/
theorem colorAux_isBernoulliFamily {n : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsBernoulliFamily (colorAux_law n q) q (colorAux_red (n := n)) where
  measurable _ := Measurable.of_discrete
  indep := iIndepFun_pi (μ := fun _ : Fin n => bernoulliMeasure true false (toUnit q))
    (X := fun _ (b : Bool) => if b then (1 : ℝ) else 0)
    (fun _ => Measurable.of_discrete.aemeasurable)
  zero_or_one v χ := by unfold colorAux_red; split <;> simp
  prob_one v := by
    have h : {χ : Fin n → Bool | colorAux_red v χ = 1} =
        Function.eval v ⁻¹' ({true} : Set Bool) := by
      ext χ; simp [colorAux_red]
    rw [h, (measurePreserving_eval _ v).measureReal_preimage
        (measurableSet_singleton _).nullMeasurableSet,
      bernoulliMeasure_real_apply_of_mem_of_notMem _ (measurableSet_singleton _) rfl (by simp),
      toUnit_coe hq0 hq1]

/-- The number of Blue vertices is `n` minus the number of Red vertices. -/
theorem colorAux_ncard_blue {n : ℕ} (χ : Fin n → Bool) :
    (({v | χ v = false} : Set (Fin n)).ncard : ℝ) = n - ∑ v, colorAux_red v χ := by
  classical
  have h1 : ∑ v, colorAux_red v χ = ((Finset.univ.filter (fun v => χ v = true)).card : ℝ) := by
    simp [colorAux_red, Finset.sum_boole]
  have h2 : ({v | χ v = false} : Set (Fin n)).ncard =
      (Finset.univ.filter (fun v => χ v = false)).card := by
    rw [← Set.ncard_coe_finset]; congr; ext v; simp
  have h3 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun v : Fin n => χ v = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h3
  rw [h1, h2]
  have : ((Finset.univ.filter (fun v => χ v = true)).card : ℝ) +
      (Finset.univ.filter (fun v => χ v = false)).card = n := by exact_mod_cast h3
  linarith

/-- The joint law of the graph and the colouring is a probability measure. -/
instance colorAux_isProbabilityMeasure_coloredGnp {n : ℕ} {p q : ℝ} :
    IsProbabilityMeasure (coloredGnp n p q) := by
  unfold coloredGnp; infer_instance

theorem colorAux_coloredProb_le_one {n : ℕ} {p q : ℝ}
    (P : SimpleGraph (Fin n) → Set (Fin n) → Prop) : coloredProb n p q P ≤ 1 :=
  measureReal_le_one

/-- An event about the colouring only has its probability under the colouring's law. -/
theorem colorAux_coloredProb_color {n : ℕ} {p q : ℝ} (E : Set (Fin n) → Prop) :
    coloredProb n p q (fun _ B₀ => E B₀) = (colorAux_law n q).real {χ | E {v | χ v = false}} := by
  have h : {x : SimpleGraph (Fin n) × (Fin n → Bool) | E {v | x.2 v = false}} =
      Set.univ ×ˢ {χ | E {v | χ v = false}} := by
    ext x; simp
  rw [coloredProb, coloredGnp, h, measureReal_def, Measure.prod_prod, measure_univ, one_mul]
  rfl

/-- The probability of a property that does not depend on the graph. -/
theorem colorAux_gnpProb_const {n : ℕ} {p : ℝ} (c : Prop) [Decidable c] :
    gnpProb n p (fun _ => c) = if c then 1 else 0 := by
  by_cases hc : c <;> simp [hc, gnpProb]

/-- `G(n, 1)` is the complete graph. -/
theorem colorAux_gnpProb_one {n : ℕ} (P : SimpleGraph (Fin n) → Prop) [Decidable (P ⊤)] :
    gnpProb n 1 P = if P ⊤ then 1 else 0 := by
  have h1 : toUnit 1 = 1 := by
    rw [toUnit, Set.projIcc_right]; rfl
  rw [gnpProb, h1, SimpleGraph.binomialRandom_one, measureReal_def,
    Measure.dirac_apply' _ (measurableSet_simpleGraph _)]
  by_cases h : P ⊤ <;> simp [h]

/-- The weight of a colouring is nonnegative. -/
theorem colorAux_weight_nonneg {n : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (χ : Fin n → Bool) : 0 ≤ ∏ v, (if χ v then q else 1 - q) :=
  Finset.prod_nonneg fun v _ => by split <;> linarith

/-- An event about the colouring only, as a weighted sum over the colourings. -/
theorem colorAux_coloredProb_color_sum {n : ℕ} {p q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (E : Set (Fin n) → Prop) [DecidablePred E] :
    coloredProb n p q (fun _ B₀ => E B₀) =
      ∑ χ : Fin n → Bool, (∏ v, if χ v then q else 1 - q) *
        (if E {v | χ v = false} then 1 else 0) := by
  rw [coloredProb_eq_sum n p q hq0 hq1]
  simp only [colorAux_gnpProb_const]

/-- The colouring's law, as a weighted sum over the colourings. -/
theorem colorAux_law_real_eq_sum {n : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (E : Set (Fin n) → Prop) [DecidablePred E] :
    (colorAux_law n q).real {χ | E {v | χ v = false}} =
      ∑ χ : Fin n → Bool, (∏ v, if χ v then q else 1 - q) *
        (if E {v | χ v = false} then 1 else 0) := by
  rw [← colorAux_coloredProb_color (p := 0), colorAux_coloredProb_color_sum hq0 hq1]

/-- At `p = 1` the graph is complete. -/
theorem colorAux_coloredProb_one {n : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (P : SimpleGraph (Fin n) → Set (Fin n) → Prop) :
    coloredProb n 1 q P = coloredProb n 1 q (fun _ B₀ => P ⊤ B₀) := by
  classical
  rw [coloredProb_eq_sum n 1 q hq0 hq1, coloredProb_eq_sum n 1 q hq0 hq1]
  simp only [colorAux_gnpProb_one, colorAux_gnpProb_const]

/-- **Conditioning on the colouring.** If the colouring is good with probability at least
`1 − b`, and for every good initial Blue set the graph makes `P` happen with probability at least
`1 − a`, then `P` happens with probability at least `1 − a − b`. -/
theorem colorAux_le_coloredProb {n : ℕ} {p q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {P : SimpleGraph (Fin n) → Set (Fin n) → Prop} {good : Set (Fin n) → Prop} {a b : ℝ}
    (hgood : ∀ B₀, good B₀ → 1 - a ≤ gnpProb n p (fun G => P G B₀))
    (hcol : 1 - b ≤ coloredProb n p q (fun _ B₀ => good B₀)) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 - a - b ≤ coloredProb n p q P := by
  classical
  by_cases ha1 : 1 < a
  · have : 0 ≤ coloredProb n p q P := measureReal_nonneg
    linarith
  push Not at ha1
  rw [colorAux_coloredProb_color_sum hq0 hq1] at hcol
  rw [coloredProb_eq_sum n p q hq0 hq1]
  have key : ∀ χ : Fin n → Bool, (∏ v, if χ v then q else 1 - q) *
      ((1 - a) * (if good {v | χ v = false} then 1 else 0)) ≤
      (∏ v, if χ v then q else 1 - q) * gnpProb n p (fun G => P G {v | χ v = false}) := by
    intro χ
    refine mul_le_mul_of_nonneg_left ?_ (colorAux_weight_nonneg hq0 hq1 χ)
    split_ifs with h
    · simpa using hgood _ h
    · simpa using gnpProb_nonneg _
  calc 1 - a - b ≤ (1 - a) * (1 - b) := by nlinarith
    _ ≤ (1 - a) * ∑ χ : Fin n → Bool, (∏ v, if χ v then q else 1 - q) *
        (if good {v | χ v = false} then 1 else 0) :=
        mul_le_mul_of_nonneg_left hcol (by linarith)
    _ = ∑ χ : Fin n → Bool, (∏ v, if χ v then q else 1 - q) *
        ((1 - a) * (if good {v | χ v = false} then 1 else 0)) := by
        rw [Finset.mul_sum]; congr 1; ext χ; ring
    _ ≤ _ := Finset.sum_le_sum fun χ _ => key χ

theorem colorAux_coloredProb_mono {n : ℕ} {p q : ℝ}
    {P Q : SimpleGraph (Fin n) → Set (Fin n) → Prop} (h : ∀ G B, P G B → Q G B) :
    coloredProb n p q P ≤ coloredProb n p q Q :=
  measureReal_mono (fun _ hx => h _ _ hx)

/-- The complement of an event about the colouring only. -/
theorem colorAux_coloredProb_color_not {n : ℕ} {p q : ℝ} (E : Set (Fin n) → Prop) :
    coloredProb n p q (fun _ B₀ => ¬ E B₀) = 1 - coloredProb n p q (fun _ B₀ => E B₀) := by
  rw [colorAux_coloredProb_color, colorAux_coloredProb_color]
  have h : {χ : Fin n → Bool | ¬ E {v | χ v = false}} = {χ | E {v | χ v = false}}ᶜ := rfl
  rw [h, measureReal_compl MeasurableSet.of_discrete, probReal_univ]

/-- The number of Red vertices, as a cardinality. -/
theorem colorAux_sum_red {n : ℕ} (χ : Fin n → Bool) :
    ∑ v, colorAux_red v χ = ((Finset.univ.filter (fun v => χ v = true)).card : ℝ) := by
  classical
  simp [colorAux_red, Finset.sum_boole]

/-- The weight of a colouring with `r` Red and `b` Blue vertices is `q^r (1 − q)^b`. -/
theorem colorAux_weight_eq {n : ℕ} (q : ℝ) (χ : Fin n → Bool) :
    ∏ v, (if χ v then q else 1 - q) =
      q ^ (Finset.univ.filter (fun v => χ v = true)).card *
        (1 - q) ^ (Finset.univ.filter (fun v => χ v = false)).card := by
  classical
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2

/-- **Colour symmetry of the random `1/2` colouring**: exchanging the colours does not change the
law. -/
theorem colorAux_law_half_compl {n : ℕ} (E : Set (Fin n) → Prop) :
    (colorAux_law n (1 / 2)).real {χ | E {v | χ v = false}ᶜ} =
      (colorAux_law n (1 / 2)).real {χ | E {v | χ v = false}} := by
  classical
  rw [colorAux_law_real_eq_sum (by norm_num) (by norm_num) (fun B => E Bᶜ),
    colorAux_law_real_eq_sum (by norm_num) (by norm_num) E]
  have hw : ∀ χ : Fin n → Bool,
      (∏ v, if χ v then (1 / 2 : ℝ) else 1 - 1 / 2) = (1 / 2) ^ n := by
    intro χ
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    simp
  simp only [hw]
  let e : Equiv.Perm (Fin n → Bool) :=
    Function.Involutive.toPerm (fun χ v => !χ v) (fun χ => by funext v; simp)
  have he : ∀ χ, e χ = fun v => !χ v := fun χ => rfl
  refine Fintype.sum_equiv e _ _ (fun χ => ?_)
  have h : ({v | χ v = false}ᶜ : Set (Fin n)) = {v | e χ v = false} := by
    ext v; simp [he]
  rw [h]

/-! ### The gap of a random `1/2` colouring -/

/-- **The initial gap of a random `1/2` colouring** (the computation of the dense paper's
Appendix A). If the number of Red vertices `X` satisfies the Berry–Esseen bound
`|P(X − n/2 ≤ x) − Φ(2x/√n)| ≤ e` for every `x`, then
`P(|X − n/2| < c√n) ≤ Φ(2c) − Φ(−2c) + 2e ≤ 4c/√(2π) + 2e`. -/
theorem colorAux_gap_le {n : ℕ} (hn : 0 < n) {e c : ℝ} (hc : 0 ≤ c)
    (hBE : ∀ x : ℝ, |(colorAux_law n (1 / 2)).real {χ | ∑ v, colorAux_red v χ - n / 2 ≤ x} -
      Φ (2 * x / Real.sqrt n)| ≤ e) :
    (colorAux_law n (1 / 2)).real {χ | |∑ v, colorAux_red v χ - n / 2| < c * Real.sqrt n} ≤
      4 * c / Real.sqrt (2 * Real.pi) + 2 * e := by
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  set μ := colorAux_law n (1 / 2)
  set S : (Fin n → Bool) → ℝ := fun χ => ∑ v, colorAux_red v χ - n / 2 with hS
  set a := c * Real.sqrt n
  have hsub : {χ | |S χ| < a} ⊆ {χ | S χ ≤ a} \ {χ | S χ ≤ -a} := by
    intro χ hχ
    simp only [Set.mem_ofPred_eq, abs_lt] at hχ
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_le]
    exact ⟨hχ.2.le, hχ.1⟩
  have hsub2 : {χ | S χ ≤ -a} ⊆ {χ | S χ ≤ a} := by
    intro χ hχ
    simp only [Set.mem_ofPred_eq] at hχ ⊢
    have : 0 ≤ a := by positivity
    linarith
  have h1 := hBE a
  have h2 := hBE (-a)
  have ha1 : 2 * a / Real.sqrt n = 2 * c := by
    simp only [a]; field_simp
  have ha2 : 2 * (-a) / Real.sqrt n = -(2 * c) := by
    simp only [a]; field_simp
  rw [ha1] at h1
  rw [ha2] at h2
  rw [abs_le] at h1 h2
  have hΦ : Φ (2 * c) - Φ (-(2 * c)) ≤ 4 * c / Real.sqrt (2 * Real.pi) := by
    simp only [Φ, Φ₀_neg]
    have := Φ₀_le_div (a := 2 * c) (by linarith)
    have : 2 * (2 * c / Real.sqrt (2 * Real.pi)) = 4 * c / Real.sqrt (2 * Real.pi) := by ring
    linarith
  calc μ.real {χ | |S χ| < a} ≤ μ.real ({χ | S χ ≤ a} \ {χ | S χ ≤ -a}) :=
        measureReal_mono hsub
    _ = μ.real {χ | S χ ≤ a} - μ.real {χ | S χ ≤ -a} :=
        measureReal_sdiff hsub2 MeasurableSet.of_discrete
    _ ≤ 4 * c / Real.sqrt (2 * Real.pi) + 2 * e := by linarith

/-- The colouring probability of a large gap: `|n/2 − |B₀|| ≥ c√n` fails only when the number of
Red vertices is within `c√n` of `n/2`. -/
theorem colorAux_coloredProb_gap {n : ℕ} {p c : ℝ} :
    coloredProb n p (1 / 2) (fun _ B₀ => c * Real.sqrt n ≤ |(n : ℝ) / 2 - B₀.ncard|) =
      1 - (colorAux_law n (1 / 2)).real
        {χ | |∑ v, colorAux_red v χ - n / 2| < c * Real.sqrt n} := by
  rw [colorAux_coloredProb_color]
  have h : {χ : Fin n → Bool | c * Real.sqrt n ≤
      |(n : ℝ) / 2 - (({v | χ v = false} : Set (Fin n)).ncard : ℝ)|} =
      {χ | |∑ v, colorAux_red v χ - n / 2| < c * Real.sqrt n}ᶜ := by
    ext χ
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt, colorAux_ncard_blue]
    rw [show (n : ℝ) / 2 - (n - ∑ v, colorAux_red v χ) = ∑ v, colorAux_red v χ - n / 2 by ring]
  rw [h, measureReal_compl MeasurableSet.of_discrete, probReal_univ]

/-! ### The near-complete case -/

/-- In `G(n, p)`, the degree of `v` is the sum of the edge indicators at `v`. -/
theorem colorAux_degree_graphOfEdges {n : ℕ} (ω : EdgeVars n) (v : Fin n) :
    (degree (graphOfEdges ω) v : ℝ) = ∑ u : {u : Fin n // u ≠ v}, edgeInd s(v, u.1) ω := by
  classical
  have h := nbrCount_graphOfEdges ω Set.univ v
  have hdeg : nbrCount (graphOfEdges ω) Set.univ v = degree (graphOfEdges ω) v := by
    simp [nbrCount, degree, SimpleGraph.neighborSet]
  rw [← hdeg, h, Finset.sum_subtype]
  intro u; simp

theorem colorAux_card_ne {n : ℕ} (v : Fin n) :
    ((Finset.univ : Finset {u : Fin n // u ≠ v}).card : ℝ) = n - 1 := by
  have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact v.elim0)
  rw [Finset.card_univ, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  push_cast [h1]
  ring

/-- Chernoff's bound for the lower tail of a degree. -/
theorem colorAux_degree_le_prob {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : Fin n) {T : ℝ}
    (hT : T < p * (n - 1)) :
    gnpProb n p (fun G => (degree G v : ℝ) ≤ T) ≤
      Real.exp (-((p * (n - 1) - T) ^ 2 / (2 * (p * (n - 1))))) := by
  rw [gnpProb_eq]
  have hX := isBernoulliFamily_edgesAt (n := n) hp0 hp1 v
  have h := hX.measureReal_sum_le_le_exp hp0 hp1 Finset.univ (T := T)
    (by rwa [colorAux_card_ne])
  rw [colorAux_card_ne] at h
  simpa only [colorAux_degree_graphOfEdges] using h

/-- A degree is at most `n − 1`. -/
theorem colorAux_degree_le {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    (degree G v : ℝ) ≤ n - 1 := by
  have h1 : (G.neighborSet v).ncard ≤ ({v}ᶜ : Set (Fin n)).ncard :=
    Set.ncard_le_ncard (fun u hu => by simpa [eq_comm] using G.ne_of_adj hu)
  have h2 := Set.ncard_add_ncard_compl ({v} : Set (Fin n))
  simp only [Set.ncard_singleton, Nat.card_eq_fintype_card, Fintype.card_fin] at h2
  have h3 : degree G v + 1 ≤ n := by unfold degree; omega
  have : ((degree G v + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h3
  push_cast at this
  linarith

/-- The expected degree is `p (n − 1)`. -/
theorem colorAux_integral_degree {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : Fin n) :
    ∫ ω, (degree (graphOfEdges ω) v : ℝ) ∂(edgeLaw n p) = p * (n - 1) := by
  simp_rw [colorAux_degree_graphOfEdges]
  rw [integral_finsetSum _ (fun i _ => Integrable.of_finite)]
  simp_rw [(isBernoulliFamily_edgesAt hp0 hp1 v).integral_eq]
  rw [Finset.sum_const, nsmul_eq_mul, colorAux_card_ne]
  ring

/-- Markov's inequality for the number `∑ᵥ (n − 1 − deg v)` of ordered non-adjacent pairs, whose
mean is `n (n − 1)(1 − p)`. -/
theorem colorAux_nonEdges_ge_prob {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {s : ℝ}
    (hs : 0 < s) :
    gnpProb n p (fun G => s ≤ ∑ v, ((n : ℝ) - 1 - degree G v)) ≤
      n * ((n - 1) * (1 - p)) / s := by
  rw [gnpProb_eq, le_div_iff₀ hs, mul_comm]
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := edgeLaw n p)
    (f := fun ω => ∑ v, ((n : ℝ) - 1 - degree (graphOfEdges ω) v))
    (Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun v _ => by
      have := colorAux_degree_le (graphOfEdges ω) v; linarith)
    Integrable.of_finite s
  refine hM.trans (le_of_eq ?_)
  rw [integral_finsetSum _ (fun i _ => Integrable.of_finite)]
  have : ∀ v : Fin n, ∫ ω, ((n : ℝ) - 1 - degree (graphOfEdges ω) v) ∂(edgeLaw n p) =
      (n - 1) * (1 - p) := by
    intro v
    rw [integral_sub (integrable_const _) Integrable.of_finite, integral_const,
      colorAux_integral_degree hp0 hp1 v]
    simp; ring
  simp_rw [this]
  simp

/-- A vertex that is Blue the next day has at most twice as many neighbours as there are Blue
vertices today. -/
theorem colorAux_degree_le_of_mem_majorityStep {n : ℕ} {G : SimpleGraph (Fin n)}
    {B : Set (Fin n)} {v : Fin n} (hv : v ∈ majorityStep G B) :
    (degree G v : ℝ) ≤ 2 * B.ncard := by
  have h1 : nbrCount G Bᶜ v ≤ nbrCount G B v := by
    simp only [majorityStep, Set.mem_ofPred_eq] at hv
    rcases hv with h | h
    · exact h.le
    · exact h.1.le
  have h2 : nbrCount G B v ≤ B.ncard := Set.ncard_le_ncard (fun u hu => hu.2)
  have h3 := nbrCount_add_nbrCount_compl G B v
  have : degree G v ≤ 2 * B.ncard := by omega
  exact_mod_cast this

/-- `x e^(−x/32) ≤ 2048 / x` for `x > 0`. -/
theorem colorAux_mul_exp_le {x : ℝ} (hx : 0 < x) : x * Real.exp (-(x / 32)) ≤ 2048 / x := by
  have hE : x ^ 2 / 2048 ≤ Real.exp (x / 32) := by
    have := Real.quadratic_le_exp_of_nonneg (x := x / 32) (by positivity)
    nlinarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hx]
  nlinarith

/-- **The near-complete case** (`pn > n − 10`, which the sparse paper's Theorem 1.2 excludes): if
Red leads by at least `m > 1` vertices (`n − 2|B₀| ≥ m`), Red is unanimous after two days with
probability at least `1 − 40/(m − 1) − 2048/n`.

On day one, only a vertex of degree at most `2|B₀|`, that is with at least `m − 1` non-neighbours,
can be Blue (`colorAux_degree_le_of_mem_majorityStep`). By Markov's inequality for the number of
non-adjacent pairs (mean `n(n − 1)(1 − p) < 10n`), there are at most `n/4` such vertices with
probability at least `1 − 40/(m − 1)`. By Chernoff's bound and the union bound, every vertex has
more than `n/2` neighbours with probability at least `1 − n e^(−n/32) ≥ 1 − 2048/n`; then the at
most `n/4` Blue vertices of day one vanish on day two (`majorityStep_eq_empty_of_lt_degree`). -/
theorem colorAux_nearComplete {n : ℕ} {p : ℝ} (hn : 44 ≤ n) (hp1 : p ≤ 1)
    (hpn : (n : ℝ) - 10 < p * n) {B₀ : Set (Fin n)} {m : ℝ} (hm : 1 < m)
    (hB : m ≤ n - 2 * (B₀.ncard : ℝ)) :
    1 - (40 / (m - 1) + 2048 / n) ≤ gnpProb n p (fun G => blueAfter G B₀ 2 = ∅) := by
  classical
  have hn' : (44 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 ≤ p := by
    by_contra h
    push Not at h
    nlinarith
  have hA : (n : ℝ) - 11 < p * (n - 1) := by nlinarith
  have hA1 : p * (n - 1) ≤ n := by nlinarith
  set s : ℝ := (m - 1) * n / 4 with hs_def
  have hs : 0 < s := by
    have : 0 < m - 1 := by linarith
    positivity
  -- the good event
  have hgood : ∀ G : SimpleGraph (Fin n), (∀ v, (n : ℝ) / 2 < degree G v) →
      ∑ v, ((n : ℝ) - 1 - degree G v) < s → blueAfter G B₀ 2 = ∅ := by
    intro G hdeg hsum
    set H := Finset.univ.filter (fun v => (degree G v : ℝ) ≤ 2 * B₀.ncard) with hH_def
    have hH : (H.card : ℝ) ≤ n / 4 := by
      by_contra hcon
      push Not at hcon
      have hle : (m - 1) * H.card ≤ ∑ v, ((n : ℝ) - 1 - degree G v) := by
        calc (m - 1) * H.card = ∑ v, if v ∈ H then (m - 1) else 0 := by
              rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]; ring
          _ ≤ _ := Finset.sum_le_sum fun v _ => by
              split_ifs with hv
              · simp only [hH_def, Finset.mem_filter, Finset.mem_univ, true_and] at hv
                linarith
              · linarith [colorAux_degree_le G v]
      have : s < (m - 1) * H.card := by
        rw [hs_def]
        have hm1 : 0 < m - 1 := by linarith
        nlinarith
      linarith
    have hB1 : majorityStep G B₀ ⊆ ↑H := fun v hv => by
      simp only [hH_def, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      exact colorAux_degree_le_of_mem_majorityStep hv
    have hB1card : ((majorityStep G B₀).ncard : ℝ) ≤ n / 4 := by
      calc ((majorityStep G B₀).ncard : ℝ) ≤ ((H : Set (Fin n)).ncard : ℝ) := by
            exact_mod_cast Set.ncard_le_ncard hB1
        _ = H.card := by rw [Set.ncard_coe_finset]
        _ ≤ n / 4 := hH
    show majorityStep G (majorityStep G B₀) = ∅
    exact majorityStep_eq_empty_of_lt_degree G (m := n / 4) (fun v => by linarith [hdeg v])
      hB1card
  -- the bad events
  have hP1 : gnpProb n p (fun G => ∃ v ∈ Finset.univ, (degree G v : ℝ) ≤ n / 2) ≤
      2048 / n := by
    refine (gnpProb_exists_le _ _).trans ?_
    have hv : ∀ v : Fin n, gnpProb n p (fun G => (degree G v : ℝ) ≤ n / 2) ≤
        Real.exp (-((n : ℝ) / 32)) := by
      intro v
      refine (colorAux_degree_le_prob hp0 hp1 v (by linarith)).trans ?_
      rw [Real.exp_le_exp, neg_le_neg_iff, le_div_iff₀ (by linarith)]
      nlinarith
    refine (Finset.sum_le_sum fun v _ => hv v).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact colorAux_mul_exp_le (by linarith)
  have hP2 : gnpProb n p (fun G => s ≤ ∑ v, ((n : ℝ) - 1 - degree G v)) ≤ 40 / (m - 1) := by
    refine (colorAux_nonEdges_ge_prob hp0 hp1 hs).trans ?_
    have hm1 : 0 < m - 1 := by linarith
    rw [hs_def, div_le_div_iff₀ (by positivity) hm1]
    have : ((n : ℝ) - 1) * (1 - p) ≤ 10 := by nlinarith
    nlinarith
  apply le_gnpProb_of_not_le
  calc gnpProb n p (fun G => ¬ blueAfter G B₀ 2 = ∅)
      ≤ gnpProb n p (fun G => (∃ v ∈ Finset.univ, (degree G v : ℝ) ≤ n / 2) ∨
          s ≤ ∑ v, ((n : ℝ) - 1 - degree G v)) := by
        refine gnpProb_mono fun G hG => ?_
        by_contra h
        push Not at h
        exact hG (hgood G (fun v => h.1 v (Finset.mem_univ _)) h.2)
    _ ≤ _ := gnpProb_or_le _ _
    _ ≤ 2048 / n + 40 / (m - 1) := add_le_add hP1 hP2
    _ = 40 / (m - 1) + 2048 / n := by ring

/-! ### Elementary estimates -/

/-- `log n ≤ 2 √n`. -/
theorem colorAux_log_le_two_sqrt (n : ℕ) : Real.log n ≤ 2 * Real.sqrt n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hn')
  rw [Real.log_sqrt hn'.le] at h1
  linarith

end PowerOfFew

end
