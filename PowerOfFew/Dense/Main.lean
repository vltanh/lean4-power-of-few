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
  -- Part 1: Lemma 2.1, read through the complementary event.
  have h1 : 1 - denseP1 n p c ≤
      gnpProb n p (fun G => ((blueAfter G B₀ 1).ncard : ℝ) ≤ n / 2 - 0.8 * Real.sqrt n / p) :=
    le_gnpProb_of_not_le ((gnpProb_mono fun G hG => not_le.mp hG).trans
      (lemma2_1 hBE hp0 hp1 hF hB₀))
  -- Part 2: Lemma 3.5 (its threshold `0.8 / p * √n` is `0.8 √n / p`).
  have h2 : 1 - denseP2 n ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
      (B.ncard : ℝ) ≤ n / 2 - 0.8 * Real.sqrt n / p →
        ((majorityStep G B).ncard : ℝ) ≤ 0.4 * n) := by
    refine (lemma3_5 hn hp0 hp1).trans (gnpProb_mono fun G hG B hB => hG B ?_)
    rwa [div_mul_eq_mul_div]
  -- Part 3: Lemma 3.6.
  have h3 : 1 - denseP3 n p ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
      (B.ncard : ℝ) ≤ 0.4 * n → ((majorityStep G B).ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3) :=
    lemma3_6 hn hp0 hp1
  -- Part 4: Lemma 3.3, second component (for `n = 1`, `1 − P₄(1, p) = 0`).
  have h4 : 1 - denseP4 n p ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
      (B.ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3 → majorityStep G B = ∅) := by
    rcases Nat.lt_or_ge 1 n with hn1 | hn1
    · exact (lemma3_3 hn1 hp0 hp1).trans (gnpProb_mono fun G hG => hG.2)
    · obtain rfl : n = 1 := le_antisymm hn1 hn
      simpa [denseP4] using gnpProb_nonneg (n := 1) (p := p) _
  refine ⟨h1, h2, h3, h4, ?_⟩
  -- The chain of shrinking: the four events together give `B₄ = ∅`.
  have hchain : gnpProb n p (fun G =>
      ((blueAfter G B₀ 1).ncard : ℝ) ≤ n / 2 - 0.8 * Real.sqrt n / p ∧
      ((∀ B : Set (Fin n), (B.ncard : ℝ) ≤ n / 2 - 0.8 * Real.sqrt n / p →
          ((majorityStep G B).ncard : ℝ) ≤ 0.4 * n) ∧
        ((∀ B : Set (Fin n), (B.ncard : ℝ) ≤ 0.4 * n →
            ((majorityStep G B).ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3) ∧
          ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3 → majorityStep G B = ∅))) ≤
      gnpProb n p (fun G => blueAfter G B₀ 4 = ∅) := by
    refine gnpProb_mono fun G ⟨e1, e2, e3, e4⟩ => ?_
    have hB2 : ((blueAfter G B₀ 2).ncard : ℝ) ≤ 0.4 * n := by
      rw [show blueAfter G B₀ 2 = majorityStep G (blueAfter G B₀ 1) from blueAfter_succ G B₀ 1]
      exact e2 _ e1
    have hB3 : ((blueAfter G B₀ 3).ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3 := by
      rw [show blueAfter G B₀ 3 = majorityStep G (blueAfter G B₀ 2) from blueAfter_succ G B₀ 2]
      exact e3 _ hB2
    rw [show blueAfter G B₀ 4 = majorityStep G (blueAfter G B₀ 3) from blueAfter_succ G B₀ 3]
    exact e4 _ hB3
  -- The union bound, by `gnpProb_and_ge` three times.
  have a34 := gnpProb_and_ge (n := n) (p := p)
    (fun G => ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ 0.4 * n →
      ((majorityStep G B).ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3)
    (fun G => ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3 → majorityStep G B = ∅)
  have a234 := gnpProb_and_ge (n := n) (p := p)
    (fun G => ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ n / 2 - 0.8 * Real.sqrt n / p →
      ((majorityStep G B).ncard : ℝ) ≤ 0.4 * n)
    (fun G => (∀ B : Set (Fin n), (B.ncard : ℝ) ≤ 0.4 * n →
        ((majorityStep G B).ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3) ∧
      ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3 → majorityStep G B = ∅)
  have a1234 := gnpProb_and_ge (n := n) (p := p)
    (fun G => ((blueAfter G B₀ 1).ncard : ℝ) ≤ n / 2 - 0.8 * Real.sqrt n / p)
    (fun G => (∀ B : Set (Fin n), (B.ncard : ℝ) ≤ n / 2 - 0.8 * Real.sqrt n / p →
        ((majorityStep G B).ncard : ℝ) ≤ 0.4 * n) ∧
      ((∀ B : Set (Fin n), (B.ncard : ℝ) ≤ 0.4 * n →
          ((majorityStep G B).ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3) ∧
        ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3 → majorityStep G B = ∅))
  linarith

/-! ### Theorem 1.2: the numbers for `p = 1/2`, `c = 5`, `n ≥ 1000` -/

/-- `Φ₀(a) ≥ (a − a³/6) / √(2π)` for `a ≥ 0`: integrate `e^{−t²/2} ≥ 1 − t²/2` over `[0, a]`. -/
private lemma denseMainAux_Φ₀_ge {a : ℝ} (ha : 0 ≤ a) :
    (a - a ^ 3 / 6) / Real.sqrt (2 * Real.pi) ≤ Φ₀ a := by
  have hint : ∫ x in (0 : ℝ)..a, (1 - x ^ 2 / 2) = a - a ^ 3 / 6 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (((continuous_pow 2).div_const 2).intervalIntegrable _ _), integral_one,
      intervalIntegral.integral_div, integral_pow]
    ring
  have hle : a - a ^ 3 / 6 ≤ ∫ x in (0 : ℝ)..a, Real.exp (-x ^ 2 / 2) := by
    rw [← hint]
    refine intervalIntegral.integral_mono_on ha ?_ ?_ fun x _ => ?_
    · exact (by fun_prop : Continuous fun x : ℝ => 1 - x ^ 2 / 2).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun x : ℝ => Real.exp (-x ^ 2 / 2)).intervalIntegrable _ _
    · linarith [Real.add_one_le_exp (-x ^ 2 / 2)]
  unfold Φ₀
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- `√(2π) < 2.5067`, from `π < 3.1416`. -/
private lemma denseMainAux_sqrt_two_pi_lt : Real.sqrt (2 * Real.pi) < 2.5067 := by
  rw [Real.sqrt_lt' (by norm_num)]
  have := Real.pi_lt_d4
  norm_num
  linarith

/-- `F(n, 1/2, 5) = √n Φ₀(11/√n) − 2.2`. -/
private lemma denseMainAux_denseF_half_five {n : ℕ} (hn : 0 < n) :
    denseF n (1 / 2) ((5 : ℕ) : ℝ) = Real.sqrt n * Φ₀ (11 / Real.sqrt n) - 2.2 := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have h1 : Real.sqrt (1 / 2 * (1 - 1 / 2) * n) = Real.sqrt n / 2 := by
    rw [show (1 / 2 : ℝ) * (1 - 1 / 2) * n = (1 / 2) ^ 2 * n by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    ring
  have h2 : Real.sqrt (1 / 2 * (1 - 1 / 2)) = 1 / 2 := by
    rw [show (1 / 2 : ℝ) * (1 - 1 / 2) = (1 / 2) ^ 2 by ring, Real.sqrt_sq (by norm_num)]
  have h3 : min (1 / 2 : ℝ) (1 - 1 / 2) = 1 / 2 := by norm_num
  have h4 : (2 * (1 / 2) * ((5 : ℕ) : ℝ) + 1 / 2) / (Real.sqrt n / 2) = 11 / Real.sqrt n := by
    field_simp
    norm_num
  unfold denseF
  rw [h1, h2, h3, h4]
  ring

/-- The paper's observation that condition (1.1) persists for larger `n`, with the value at
`n = 1000`: for `n ≥ 1000`, `F(n, 1/2, 5) ≥ F(1000, 1/2, 5) ≥ 2.0997` (`x ↦ x Φ₀(11/x)` is
increasing, and `√1000 Φ₀(11/√1000) ≥ (11 − 11³/6000)/√(2π) ≥ 4.2997`). -/
private lemma denseMainAux_denseF_half_five_ge {n : ℕ} (hn : 1000 ≤ n) :
    2.0997 ≤ denseF n (1 / 2) ((5 : ℕ) : ℝ) := by
  have hn0 : 0 < n := by omega
  have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  rw [denseMainAux_denseF_half_five hn0]
  have hmono := monotoneOn_mul_Φ₀_div (a := 11) (by norm_num)
    (show Real.sqrt 1000 ∈ Set.Ioi 0 from Real.sqrt_pos.mpr (by norm_num))
    (show Real.sqrt n ∈ Set.Ioi 0 from Real.sqrt_pos.mpr (by positivity))
    (Real.sqrt_le_sqrt hnR)
  simp only at hmono
  have h1000 : 4.2997 ≤ Real.sqrt 1000 * Φ₀ (11 / Real.sqrt 1000) := by
    have hs : 0 < Real.sqrt 1000 := Real.sqrt_pos.mpr (by norm_num)
    have hs2 : Real.sqrt 1000 ^ 2 = 1000 := Real.sq_sqrt (by norm_num)
    have hΦ := denseMainAux_Φ₀_ge (a := 11 / Real.sqrt 1000) (by positivity)
    have hpi := denseMainAux_sqrt_two_pi_lt
    have hpi0 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have hval : Real.sqrt 1000 * (11 / Real.sqrt 1000 - (11 / Real.sqrt 1000) ^ 3 / 6) =
        64669 / 6000 := by
      field_simp
      rw [hs2]
      norm_num
    calc (4.2997 : ℝ) ≤ 64669 / 6000 / Real.sqrt (2 * Real.pi) := by
          rw [le_div_iff₀ hpi0]; nlinarith
      _ = Real.sqrt 1000 * ((11 / Real.sqrt 1000 - (11 / Real.sqrt 1000) ^ 3 / 6) /
            Real.sqrt (2 * Real.pi)) := by rw [← hval]; ring
      _ ≤ Real.sqrt 1000 * Φ₀ (11 / Real.sqrt 1000) := mul_le_mul_of_nonneg_left hΦ hs.le
  linarith

/-- `P₁(n, 1/2, 5) ≤ 0.42502 / 2.0997² < 0.0965` for `n ≥ 1000` (the paper prints `0.0902`). -/
private lemma denseMainAux_P1_half_five_le {n : ℕ} (hn : 1000 ≤ n) :
    denseP1 n (1 / 2) ((5 : ℕ) : ℝ) ≤ 0.0965 := by
  have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hF := denseMainAux_denseF_half_five_ge hn
  unfold denseP1
  have hc : 4 * ((5 : ℕ) : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤ 0.0001 := by
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  have hnum : 0.25 + 0.7 * (1 - 2 * (1 / 2 : ℝ) + 2 * (1 / 2) ^ 2) ^ 2 *
      (1 + 4 * ((5 : ℕ) : ℝ) ^ 2 / (n : ℝ) ^ 2) ≤ 0.42502 := by
    norm_num at hc ⊢
    linarith
  have hF2 : (2.0997 : ℝ) ^ 2 ≤ denseF n (1 / 2) ((5 : ℕ) : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hF 2
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith

/-- `e^{−18} < 10⁻⁷`, from `e > 2.7`. -/
private lemma denseMainAux_exp_neg_18_lt : Real.exp (-18) < 1e-7 := by
  have h27 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h : (2.7 : ℝ) ^ 18 < Real.exp 1 ^ 18 := pow_lt_pow_left₀ h27 (by norm_num) (by norm_num)
  rw [Real.exp_one_pow] at h
  rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
  norm_num at h ⊢
  linarith

/-- `n⁻¹ ≤ 10⁻³` for `n ≥ 1000`. -/
private lemma denseMainAux_inv_le {n : ℕ} (hn : 1000 ≤ n) : (n : ℝ)⁻¹ ≤ 1e-3 := by
  have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  norm_num
  linarith

/-- `P₂(n) < 10⁻¹⁰` for `n ≥ 1000`, since `0.076 n − 1.83 √n ≥ 18`. -/
private lemma denseMainAux_P2_lt {n : ℕ} (hn : 1000 ≤ n) : denseP2 n < 1e-10 := by
  have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  unfold denseP2
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  have hs31 : 31.62 ≤ Real.sqrt n := by nlinarith
  have hexp : Real.exp (-(0.076 * n - 1.83 * Real.sqrt n)) ≤ Real.exp (-18) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hs31)
      (show (0 : ℝ) ≤ 0.076 * Real.sqrt n + 0.57312 by positivity)]
  calc (n : ℝ)⁻¹ * Real.exp (-(0.076 * n - 1.83 * Real.sqrt n))
      ≤ 1e-3 * Real.exp (-18) :=
        mul_le_mul (denseMainAux_inv_le hn) hexp (Real.exp_pos _).le (by norm_num)
    _ < 1e-3 * 1e-7 := by gcongr; exact denseMainAux_exp_neg_18_lt
    _ = 1e-10 := by norm_num

/-- `P₃(n, 1/2) < 10⁻¹⁰` for `n ≥ 1000`, since `0.02 n (n/8 − 80) ≥ 900 ≥ 18`. -/
private lemma denseMainAux_P3_half_lt {n : ℕ} (hn : 1000 ≤ n) : denseP3 n (1 / 2) < 1e-10 := by
  have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  unfold denseP3
  have hexp : Real.exp (-(0.02 * n * ((1 / 2 : ℝ) ^ 3 * n - 80))) ≤ Real.exp (-18) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc (n : ℝ)⁻¹ * Real.exp (-(0.02 * n * ((1 / 2 : ℝ) ^ 3 * n - 80)))
      ≤ 1e-3 * Real.exp (-18) :=
        mul_le_mul (denseMainAux_inv_le hn) hexp (Real.exp_pos _).le (by norm_num)
    _ < 1e-3 * 1e-7 := by gcongr; exact denseMainAux_exp_neg_18_lt
    _ = 1e-10 := by norm_num

/-- `P₄(n, 1/2) = n e^{−(n−1)/18} < 10⁻¹⁰` for `n ≥ 1000`: with `y = (n − 1)/18 ≥ 55.5`,
`e^y ≥ y¹⁵/15! > 10¹⁰ · 19 y ≥ 10¹⁰ n`. -/
private lemma denseMainAux_P4_half_lt {n : ℕ} (hn : 1000 ≤ n) : denseP4 n (1 / 2) < 1e-10 := by
  have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  unfold denseP4
  obtain ⟨y, hy_def⟩ : ∃ y : ℝ, y = 2 / 9 * (1 / 2) ^ 2 * ((n : ℝ) - 1) := ⟨_, rfl⟩
  rw [← hy_def]
  have hy : 55.5 ≤ y := by rw [hy_def]; linarith
  have hny : (n : ℝ) ≤ 19 * y := by rw [hy_def]; linarith
  have hexp := Real.pow_div_factorial_le_exp y (by linarith) 15
  have hfact : ((Nat.factorial 15 : ℕ) : ℝ) = 1307674368000 := by
    norm_num [Nat.factorial]
  rw [hfact] at hexp
  have hy14 : (55.5 : ℝ) ^ 14 ≤ y ^ 14 := pow_le_pow_left₀ (by norm_num) hy 14
  have hbig : (n : ℝ) * 1307674368000 * 1e10 < y ^ 15 := by
    calc (n : ℝ) * 1307674368000 * 1e10 ≤ 19 * y * 1307674368000 * 1e10 := by gcongr
      _ < 55.5 ^ 14 * y := by nlinarith
      _ ≤ y ^ 14 * y := by gcongr
      _ = y ^ 15 := by ring
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
  rw [div_le_iff₀ (by norm_num)] at hexp
  nlinarith

/-- **Theorem 1.2** (`D:thm:const-advantage-ex`, the power of few). Consider majority dynamics on
`G(n, 1/2)` with `n ≥ 1000`, where the Red camp has at least `n/2 + 5` vertices on day 0. Then Red
wins after the fourth day with probability at least `0.9`.

Departure from the paper (an arithmetic error repaired; E-item D-Thm1.2): the paper's routine
calculation claims `P₁ ≤ 0.0902`, which fails for `1000 ≤ n ≤ 4979` (`P₁(1000, 1/2, 5) ≈ 0.0962`).
The proof shows `P₁ ≤ 0.0965` instead and, as in the paper, `max{P₂, P₃, P₄} < 10⁻¹⁰`; the total
is still below `0.1`. -/
theorem theorem1_2 (hBE : ShevtsovaBerryEsseen) {n : ℕ} (hn : 1000 ≤ n) {B₀ : Set (Fin n)}
    (hB₀ : (B₀.ncard : ℝ) ≤ n / 2 - 5) :
    0.9 ≤ gnpProb n (1 / 2) (fun G => blueAfter G B₀ 4 = ∅) := by
  -- Theorem 1.6 with `p = 1/2` and `c = 5`; condition (1.1) holds since `F ≥ 2.0997 > 0`.
  have hF := denseMainAux_denseF_half_five_ge hn
  have h16 := (theorem1_6 hBE (p := 1 / 2) (c := 5) (by norm_num) (by norm_num) (by omega)
    (by norm_num) (by linarith) (B₀ := B₀) (by push_cast; linarith)).2.2.2.2
  -- `P₁ ≤ 0.0965` and `max{P₂, P₃, P₄} < 10⁻¹⁰`, so `P₁ + P₂ + P₃ + P₄ < 0.1`.
  have h1 := denseMainAux_P1_half_five_le hn
  have h2 := denseMainAux_P2_lt hn
  have h3 := denseMainAux_P3_half_lt hn
  have h4 := denseMainAux_P4_half_lt hn
  linarith

/-! ### Theorem 1.3: the asymptotic bound -/

/-- `n² P₂(n) ≤ e^{22.1} / 0.038` for `n ≥ 1`: `n ≤ e^{0.038 n} / 0.038` and
`1.83 √n − 0.038 n ≤ 22.1`. -/
private lemma denseMainAux_P2_le {n : ℕ} (hn : 0 < n) :
    denseP2 n ≤ Real.exp 22.1 / 0.038 * ((n : ℝ) ^ 2)⁻¹ := by
  unfold denseP2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sq_sqrt hnR.le
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  have h1 : (n : ℝ) ≤ Real.exp (0.038 * n) / 0.038 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith [Real.add_one_le_exp (0.038 * (n : ℝ))]
  have h2 : Real.exp (0.038 * n) * Real.exp (-(0.076 * n - 1.83 * Real.sqrt n)) ≤
      Real.exp 22.1 := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (Real.sqrt n - 24.08)]
  have hE := Real.exp_pos (-(0.076 * n - 1.83 * Real.sqrt n))
  rw [show Real.exp 22.1 / 0.038 * ((n : ℝ) ^ 2)⁻¹ = Real.exp 22.1 / 0.038 / (n : ℝ) ^ 2 by ring,
    le_div_iff₀ (by positivity)]
  calc (n : ℝ)⁻¹ * Real.exp (-(0.076 * n - 1.83 * Real.sqrt n)) * (n : ℝ) ^ 2
      = n * Real.exp (-(0.076 * n - 1.83 * Real.sqrt n)) := by field_simp
    _ ≤ Real.exp (0.038 * n) / 0.038 * Real.exp (-(0.076 * n - 1.83 * Real.sqrt n)) := by
        gcongr
    _ = Real.exp (0.038 * n) * Real.exp (-(0.076 * n - 1.83 * Real.sqrt n)) / 0.038 := by ring
    _ ≤ Real.exp 22.1 / 0.038 := by gcongr

/-- `n² P₃(n, p) ≤ e^{84.5/p³}`: `n ≤ eⁿ` and `2.6 n − 0.02 p³ n² ≤ 84.5/p³`
(`0.02 (p³n)² − 2.6 p³n + 84.5 = 0.02 (p³n − 65)²`). -/
private lemma denseMainAux_P3_le {n : ℕ} (hn : 0 < n) {p : ℝ} (hp0 : 0 < p) :
    denseP3 n p ≤ Real.exp (84.5 / p ^ 3) * ((n : ℝ) ^ 2)⁻¹ := by
  unfold denseP3
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have h2 : Real.exp n * Real.exp (-(0.02 * n * (p ^ 3 * n - 80))) ≤ Real.exp (84.5 / p ^ 3) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (p ^ 3 * n - 65)]
  rw [show Real.exp (84.5 / p ^ 3) * ((n : ℝ) ^ 2)⁻¹ = Real.exp (84.5 / p ^ 3) / (n : ℝ) ^ 2 by
      ring, le_div_iff₀ (by positivity)]
  calc (n : ℝ)⁻¹ * Real.exp (-(0.02 * n * (p ^ 3 * n - 80))) * (n : ℝ) ^ 2
      = n * Real.exp (-(0.02 * n * (p ^ 3 * n - 80))) := by field_simp
    _ ≤ Real.exp n * Real.exp (-(0.02 * n * (p ^ 3 * n - 80))) := by gcongr
    _ ≤ Real.exp (84.5 / p ^ 3) := h2

/-- `n² P₄(n, p) ≤ (27/(2p²))³` for `n ≥ 1`: `n ≤ (27/(2p²))(1 + (2/27)p²(n − 1))
≤ (27/(2p²)) e^{(2/27)p²(n − 1)}`, and cube. -/
private lemma denseMainAux_P4_le {n : ℕ} (hn : 0 < n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    denseP4 n p ≤ (27 / (2 * p ^ 2)) ^ 3 * ((n : ℝ) ^ 2)⁻¹ := by
  unfold denseP4
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hC : 1 ≤ 27 / (2 * p ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h1 : (n : ℝ) ≤ 27 / (2 * p ^ 2) * Real.exp (2 / 27 * p ^ 2 * ((n : ℝ) - 1)) := by
    have h := Real.add_one_le_exp (2 / 27 * p ^ 2 * ((n : ℝ) - 1))
    have e : 27 / (2 * p ^ 2) * (2 / 27 * p ^ 2 * ((n : ℝ) - 1) + 1) =
        (n : ℝ) - 1 + 27 / (2 * p ^ 2) := by
      field_simp
    calc (n : ℝ) ≤ (n : ℝ) - 1 + 27 / (2 * p ^ 2) := by linarith
      _ = 27 / (2 * p ^ 2) * (2 / 27 * p ^ 2 * ((n : ℝ) - 1) + 1) := e.symm
      _ ≤ 27 / (2 * p ^ 2) * Real.exp (2 / 27 * p ^ 2 * ((n : ℝ) - 1)) := by gcongr
  have h3 : (n : ℝ) ^ 3 ≤ (27 / (2 * p ^ 2)) ^ 3 * Real.exp (2 / 9 * p ^ 2 * ((n : ℝ) - 1)) := by
    have h := pow_le_pow_left₀ (by positivity) h1 3
    rw [mul_pow, ← Real.exp_nat_mul] at h
    convert h using 3
    push_cast
    ring
  have hE := Real.exp_pos (2 / 9 * p ^ 2 * ((n : ℝ) - 1))
  rw [Real.exp_neg, show (27 / (2 * p ^ 2)) ^ 3 * ((n : ℝ) ^ 2)⁻¹ =
      (27 / (2 * p ^ 2)) ^ 3 / (n : ℝ) ^ 2 by ring, le_div_iff₀ (by positivity)]
  calc (n : ℝ) * (Real.exp (2 / 9 * p ^ 2 * ((n : ℝ) - 1)))⁻¹ * (n : ℝ) ^ 2
      = (n : ℝ) ^ 3 / Real.exp (2 / 9 * p ^ 2 * ((n : ℝ) - 1)) := by ring
    _ ≤ (27 / (2 * p ^ 2)) ^ 3 := by rwa [div_le_iff₀ hE]

/-- The paper's "`P₂, P₃, P₄ = o(n⁻²)`, absorbed since `n⁻² < n⁻¹`", made uniform:
`P₂ + P₃ + P₄ ≤ K'(p) n⁻² ≤ K'(p) n⁻¹` for `n ≥ 1`, with
`K'(p) = e^{22.1}/0.038 + e^{84.5/p³} + (27/(2p²))³`. -/
private lemma denseMainAux_P234_le {n : ℕ} (hn : 0 < n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    denseP2 n + denseP3 n p + denseP4 n p ≤
      (Real.exp 22.1 / 0.038 + Real.exp (84.5 / p ^ 3) + (27 / (2 * p ^ 2)) ^ 3) *
        (n : ℝ)⁻¹ := by
  have h2 := denseMainAux_P2_le hn
  have h3 := denseMainAux_P3_le hn hp0
  have h4 := denseMainAux_P4_le hn hp0 hp1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv : ((n : ℝ) ^ 2)⁻¹ ≤ (n : ℝ)⁻¹ :=
    inv_anti₀ (by positivity) (by nlinarith)
  have hK : 0 ≤ Real.exp 22.1 / 0.038 + Real.exp (84.5 / p ^ 3) + (27 / (2 * p ^ 2)) ^ 3 := by
    positivity
  have := mul_le_mul_of_nonneg_left hinv hK
  linarith

/-- The numerator of `P₁` is below `2` when `c ≤ n/2`: `0.25 + 0.7 · 1 · (1 + 1) < 2`. -/
private lemma denseMainAux_P1_num_le {n c p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hn : 0 < n)
    (hc : 0 ≤ c) (hcn : 2 * c ≤ n) :
    0.25 + 0.7 * (1 - 2 * p + 2 * p ^ 2) ^ 2 * (1 + 4 * c ^ 2 / n ^ 2) ≤ 2 := by
  have hq0 : 0 ≤ 1 - 2 * p + 2 * p ^ 2 := by nlinarith
  have hq1 : 1 - 2 * p + 2 * p ^ 2 ≤ 1 := by nlinarith
  have hq2 : (1 - 2 * p + 2 * p ^ 2) ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
  have hr : 4 * c ^ 2 / n ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hr0 : 0 ≤ 4 * c ^ 2 / n ^ 2 := by positivity
  have := mul_le_mul hq2 (show 1 + 4 * c ^ 2 / n ^ 2 ≤ 2 by linarith) (by positivity) zero_le_one
  linarith

/-- `1 / min{√n, c}² ≤ max{1/n, 1/c²}`. -/
private lemma denseMainAux_inv_sq_min_le {n c : ℝ} (hn : 0 ≤ n) :
    (min (Real.sqrt n) c ^ 2)⁻¹ ≤ max n⁻¹ (c ^ 2)⁻¹ := by
  rcases min_choice (Real.sqrt n) c with h | h
  · rw [h, Real.sq_sqrt hn]
    exact le_max_left _ _
  · rw [h]
    exact le_max_right _ _

/-- The paper's lower bound on the first term of `F`, by `Φ₀(x) ≥ min{1, x/y} Φ₀(y)` with
`y = 2√p`: `√n Φ₀((2pc + min{p, 1 − p}) / √(p(1 − p)n)) ≥ √n min{1, c/√((1 − p)n)} Φ₀(2√p)
= min{√n, c/√(1 − p)} Φ₀(2√p) ≥ min{√n, c} Φ₀(2√p)`. -/
private lemma denseMainAux_min_mul_Φ₀_le {n c p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hn : 0 < n)
    (hc : 0 ≤ c) :
    min (Real.sqrt n) c * Φ₀ (2 * Real.sqrt p) ≤
      Real.sqrt n * Φ₀ ((2 * p * c + min p (1 - p)) / Real.sqrt (p * (1 - p) * n)) := by
  obtain ⟨x, hx_def⟩ : ∃ x : ℝ,
      x = (2 * p * c + min p (1 - p)) / Real.sqrt (p * (1 - p) * n) := ⟨_, rfl⟩
  rw [← hx_def]
  have hmin0 : 0 ≤ min p (1 - p) := le_min hp0.le (by linarith)
  have hx0 : 0 ≤ x := by rw [hx_def]; positivity
  have hy0 : 0 < 2 * Real.sqrt p := by positivity
  have hφ : 0 ≤ Φ₀ (2 * Real.sqrt p) := Φ₀_nonneg hy0.le
  -- `Φ₀(x) ≥ min{1, x/(2√p)} Φ₀(2√p)`
  have hmin := min_mul_Φ₀_le hx0 hy0
  -- `x / (2√p) ≥ c / √((1 − p) n)`
  have hD : 0 < Real.sqrt ((1 - p) * n) := Real.sqrt_pos.mpr (by nlinarith)
  have hsp : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  have hratio : c / Real.sqrt ((1 - p) * n) ≤ x / (2 * Real.sqrt p) := by
    rw [hx_def, mul_assoc p, Real.sqrt_mul hp0.le, div_div,
      div_le_div_iff₀ hD (by positivity)]
    have e : c * (Real.sqrt p * Real.sqrt ((1 - p) * n) * (2 * Real.sqrt p)) =
        2 * p * c * Real.sqrt ((1 - p) * n) := by
      linear_combination (2 * c * Real.sqrt ((1 - p) * n)) * hsp
    rw [e]
    nlinarith [mul_nonneg hmin0 hD.le]
  -- `√n min{1, c/√((1 − p)n)} = min{√n, c/√(1 − p)}`
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hsqrt : Real.sqrt n * min 1 (c / Real.sqrt ((1 - p) * n)) =
      min (Real.sqrt n) (c / Real.sqrt (1 - p)) := by
    rw [mul_min_of_nonneg _ _ hsn.le, mul_one, Real.sqrt_mul (by linarith)]
    congr 1
    field_simp
  -- `c ≤ c / √(1 − p)`
  have hc_le : c ≤ c / Real.sqrt (1 - p) :=
    le_div_self hc (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_one.mpr (by linarith))
  calc min (Real.sqrt n) c * Φ₀ (2 * Real.sqrt p)
      ≤ min (Real.sqrt n) (c / Real.sqrt (1 - p)) * Φ₀ (2 * Real.sqrt p) :=
        mul_le_mul_of_nonneg_right (min_le_min le_rfl hc_le) hφ
    _ = Real.sqrt n * min 1 (c / Real.sqrt ((1 - p) * n)) * Φ₀ (2 * Real.sqrt p) := by
        rw [hsqrt]
    _ ≤ Real.sqrt n * min 1 (x / (2 * Real.sqrt p)) * Φ₀ (2 * Real.sqrt p) := by
        gcongr
    _ ≤ Real.sqrt n * Φ₀ x := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hmin hsn.le

/-- **Theorem 1.3** (`D:thm:unbounded-advantage`, asymptotic bound). Let `p ∈ (0, 1)` be a
constant. There is `K(p)` such that, whenever the Red camp has at least `n/2 + cₙ` vertices on
day 0 (`cₙ` a positive integer that may depend on `n`), Red wins after four days with probability
at least `1 − K(p) max{n⁻¹, cₙ⁻²}`.

Reading: "Red has `n/2 + cₙ`" is read as "at least `n/2 + cₙ`", as in Theorem 1.6 and the
abstract.

Departure from the paper (an error and a gap repaired; E-item D-Thm1.3). Write `φ = Φ₀(2√p)` and
`L = 0.6 (1 − 2p + 2p²)/√(p(1 − p)) + 0.8/p`. The paper's argument needs `min{√n, cₙ} φ ≥ 2L`
("`n` and `cₙ` both sufficiently large"); when this fails, `max{n⁻¹, cₙ⁻²} > (φ/(2L))²` and the
bound is trivial for `K ≥ (2L/φ)²`. Its `P₁ ≤ 2/(min{cₙ, √n} φ/2)²` equals
`8 φ⁻² max{n⁻¹, cₙ⁻²}` (the paper prints `4 φ⁻²`), and its `P₂, P₃, P₄ = o(n⁻²)` is used in the
uniform form `P₂ + P₃ + P₄ ≤ K'(p) n⁻² ≤ K'(p) n⁻¹`. Hence the proof takes
`K = 8 φ⁻² + K'(p) + (2L/φ)²` in place of the paper's `4 φ⁻² + 1`. The paper's `+ 1` absorbs
`P₂ + P₃ + P₄` only once `n` is large in terms of `p`, even inside its main case: for `p = 0.1`,
`n = 10⁴`, `cₙ = 100` (`min{√n, cₙ} φ ≈ 23.6 ≥ 2L ≈ 19.3`), `P₃ = n⁻¹ e^13991`. -/
theorem theorem1_3 (hBE : ShevtsovaBerryEsseen) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ K : ℝ, ∀ (n c : ℕ), 0 < c → ∀ B₀ : Set (Fin n), (B₀.ncard : ℝ) ≤ n / 2 - c →
      1 - K * max ((n : ℝ)⁻¹) (((c : ℝ) ^ 2)⁻¹) ≤ gnpProb n p (fun G => blueAfter G B₀ 4 = ∅) := by
  -- The constants `φ = Φ₀(2√p)`, `L`, and `K'` with `P₂ + P₃ + P₄ ≤ K'/n`.
  obtain ⟨φ, hφ_def⟩ : ∃ φ : ℝ, φ = Φ₀ (2 * Real.sqrt p) := ⟨_, rfl⟩
  obtain ⟨L, hL_def⟩ : ∃ L : ℝ,
      L = 0.6 * (1 - 2 * p + 2 * p ^ 2) / Real.sqrt (p * (1 - p)) + 0.8 / p := ⟨_, rfl⟩
  obtain ⟨K', hK'_def⟩ : ∃ K' : ℝ,
      K' = Real.exp 22.1 / 0.038 + Real.exp (84.5 / p ^ 3) + (27 / (2 * p ^ 2)) ^ 3 := ⟨_, rfl⟩
  have hφ : 0 < φ := by
    have h := strictMono_Φ₀ (show (0 : ℝ) < 2 * Real.sqrt p by positivity)
    rwa [Φ₀_zero, ← hφ_def] at h
  have hL : 0 < L := by
    have hq0 : 0 < 1 - 2 * p + 2 * p ^ 2 := by nlinarith
    have : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr (by nlinarith)
    rw [hL_def]
    positivity
  have hK' : 0 ≤ K' := by rw [hK'_def]; positivity
  refine ⟨8 * φ⁻¹ ^ 2 + K' + (2 * L / φ) ^ 2, fun n c hc B₀ hB₀ => ?_⟩
  -- `cₙ ≤ n/2` (the paper's "without loss of generality"), since `|B₀| ≥ 0`.
  have hcn : 2 * (c : ℝ) ≤ n := by
    have := (Nat.cast_nonneg B₀.ncard : (0 : ℝ) ≤ B₀.ncard)
    linarith
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hnR : (0 : ℝ) < n := by linarith
  have hn0 : 0 < n := by exact_mod_cast hnR
  -- `m = min{√n, cₙ}`, and `1/m² ≤ max{1/n, 1/cₙ²}`.
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ, m = min (Real.sqrt n) (c : ℝ) := ⟨_, rfl⟩
  have hm0 : 0 < m := by
    rw [hm_def]
    exact lt_min (Real.sqrt_pos.mpr hnR) (by linarith)
  have hmax : (m ^ 2)⁻¹ ≤ max ((n : ℝ)⁻¹) (((c : ℝ) ^ 2)⁻¹) := by
    rw [hm_def]
    exact denseMainAux_inv_sq_min_le hnR.le
  have hmax0 : 0 ≤ max ((n : ℝ)⁻¹) (((c : ℝ) ^ 2)⁻¹) := le_max_of_le_left (by positivity)
  by_cases hbig : 2 * L ≤ m * φ
  · -- `n` and `cₙ` large: `F ≥ (φ/2) min{√n, cₙ} > 0`, and Theorem 1.6 applies.
    have hkey := denseMainAux_min_mul_Φ₀_le hp0 hp1 hnR (by linarith : (0 : ℝ) ≤ c)
    rw [← hm_def, ← hφ_def] at hkey
    have hF : m * φ / 2 ≤ denseF n p c := by
      have hFeq : denseF n p c = Real.sqrt n *
          Φ₀ ((2 * p * c + min p (1 - p)) / Real.sqrt (p * (1 - p) * n)) - L := by
        rw [hL_def]
        unfold denseF
        ring
      rw [hFeq]
      linarith
    have hFpos : 0 < denseF n p c := lt_of_lt_of_le (by positivity) hF
    have h16 := (theorem1_6 hBE hp0 hp1 hn0 hc hFpos hB₀).2.2.2.2
    -- `P₁ ≤ 2 / (m φ/2)² = 8 φ⁻² m⁻² ≤ 8 φ⁻² max{1/n, 1/cₙ²}`.
    have hP1 : denseP1 n p c ≤ 8 * φ⁻¹ ^ 2 * (m ^ 2)⁻¹ := by
      have hnum := denseMainAux_P1_num_le hp0 hp1 hnR (by linarith : (0 : ℝ) ≤ c) hcn
      have hF2 : (m * φ / 2) ^ 2 ≤ denseF n p c ^ 2 := pow_le_pow_left₀ (by positivity) hF 2
      unfold denseP1
      calc _ ≤ 2 / denseF n p c ^ 2 := by gcongr
        _ ≤ 2 / (m * φ / 2) ^ 2 := by gcongr
        _ = 8 * φ⁻¹ ^ 2 * (m ^ 2)⁻¹ := by field_simp; ring
    -- `P₂ + P₃ + P₄ ≤ K' n⁻¹ ≤ K' max{1/n, 1/cₙ²}`.
    have hP234 := denseMainAux_P234_le hn0 hp0 hp1
    rw [← hK'_def] at hP234
    have e1 := mul_le_mul_of_nonneg_left hmax (by positivity : (0 : ℝ) ≤ 8 * φ⁻¹ ^ 2)
    have e2 := mul_le_mul_of_nonneg_left (le_max_left ((n : ℝ)⁻¹) (((c : ℝ) ^ 2)⁻¹)) hK'
    have e3 := mul_nonneg (sq_nonneg (2 * L / φ)) hmax0
    linarith
  · -- Otherwise `min{√n, cₙ} < 2L/φ`, so `K max{1/n, 1/cₙ²} > 1` and the bound is trivial.
    replace hbig := not_le.mp hbig
    have h1 : m < 2 * L / φ := by rwa [lt_div_iff₀ hφ]
    have h2 : m ^ 2 < (2 * L / φ) ^ 2 := pow_lt_pow_left₀ h1 hm0.le (by norm_num)
    have h3 : 1 < (2 * L / φ) ^ 2 * max ((n : ℝ)⁻¹) (((c : ℝ) ^ 2)⁻¹) := by
      calc (1 : ℝ) < (2 * L / φ) ^ 2 * (m ^ 2)⁻¹ := by
            rw [← div_eq_mul_inv, one_lt_div (by positivity)]
            exact h2
        _ ≤ (2 * L / φ) ^ 2 * max ((n : ℝ)⁻¹) (((c : ℝ) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left hmax (by positivity)
    have e1 := mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * φ⁻¹ ^ 2 + K') hmax0
    have := gnpProb_nonneg (n := n) (p := p) (fun G => blueAfter G B₀ 4 = ∅)
    linarith

end PowerOfFew.Dense

end
