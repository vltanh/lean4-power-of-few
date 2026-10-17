module

public import PowerOfFew.Sparse.BerryEsseen
public import PowerOfFew.Model.Gnp
public import PowerOfFew.Model.Majority
public import PowerOfFew.Model.EdgeConditioning
public import Basic.Probability.Concentration

/-!
# Sparse paper, Section 2.2: Step 1, the first day

Lemma 2.1 and Proposition 2.2 of the sparse paper, with the variance constant that the paper's
argument gives (a decision recorded in `REPORT.md`):

The proof of Proposition 2.2 quotes Lemma A.3 as `P(X = …) ≤ C_BE / √(p(1 − p)(n − 2))`, but
Lemma A.3 gives `2 C_BE (1 − 2σ²) / (σ √(n − 2))`. With that bound, the covariance of two
indicators is at most `4 C_BE² (1 − 2σ²)² / (n − 2)`, and
`Var|B₁| ≤ n (1/4 + 4 C_BE² (1 − 2σ²)² (n − 1)/(n − 2))` instead of `7n/12`; the two agree in
form at `p = 1/2`. (Lemma A.3 also requires a positive integer `d < (n₁ + n₂)/2`, while Proposition
2.2 applies it at `d ≤ 0`; it holds for every integer `d`.) `varConst n p` is this coefficient, and Lemma 2.1's constant
`C(c, D) = 7 / (12 (D_c − D)²)` becomes `varConst n p / (D_c − D)²`.

Proofs. Proposition 2.2 follows the paper's two steps. Step 1: `P(v ∈ B₁) ≤ P(δ₀(v) ≤ 0)`, where
`δ₀(v) = ∑_{u ≠ v} ℓ₀(u) 1_{u ∼ v}` (`sparseAux_delta0_eq`), then Corollary A.2,
`E δ₀(v) ≥ p(2Δ − 1)`, `Φ₀(x) ≥ min{1, x/y} Φ₀(y)` with `y = 2 − 1/c` and the paper's two
inequalities (`sparseAux_prob_blue_le`). Step 2: `Var|B₁| = ∑ Var + ∑ Cov`, each variance at most
`1/4`, and each covariance `p(1 − p)(P(E_u) − P(F_u))(P(E_v) − P(F_v))`
(`PowerOfFew.covariance_shared_edge`) with `|P(E_u) − P(F_u)| ≤ P(X = k)` for the difference `X`
of two independent binomials over the `n − 2` other edges at `u` (`sparseAux_edgeCond_diff_le`;
the paper computes the difference exactly, by the same case analysis, `sparseAux_flip`), bounded by
the general form of Lemma A.3 (`sparseAux_pointProb_le`). Lemma 2.1 is Chebyshev's inequality
above the mean.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- `D_c = Φ₀(2 − 1/c) − C_BE / c`, with `C_BE = 0.56` (sparse paper, equation (2)). -/
def Dc (c : ℝ) : ℝ := Φ₀ (2 - 1 / c) - 0.56 / c

/-- The variance coefficient that the argument of Proposition 2.2 gives:
`1/4 + 4 C_BE² (1 − 2σ²)² (n − 1)/(n − 2)`, `σ² = p(1 − p)`, `C_BE = 0.56`. -/
def varConst (n : ℕ) (p : ℝ) : ℝ :=
  1 / 4 + 4 * 0.56 ^ 2 * (1 - 2 * (p * (1 - p))) ^ 2 * (((n : ℝ) - 1) / ((n : ℝ) - 2))

/-! ### Helpers for the proofs of Proposition 2.2 and Lemma 2.1 -/

/-- `ℓ₀(u)`: `1` if `u` is Red (`u ∉ B₀`), `−1` if `u` is Blue. -/
def sparseAux_sgn {n : ℕ} (B₀ : Set (Fin n)) (u : Fin n) : ℝ := by
  classical exact if u ∈ B₀ then -1 else 1

open Classical in
/-- The number of elements of a set of vertices as a sum of indicators. -/
theorem sparseAux_ncard_eq_sum {n : ℕ} (A : Set (Fin n)) :
    (A.ncard : ℝ) = ∑ v, (if v ∈ A then (1 : ℝ) else 0) := by
  classical
  rw [Finset.sum_boole, Set.ncard_eq_toFinset_card']
  congr 2
  ext v; simp

/-- `δ₀(v) = (Red neighbours) − (Blue neighbours) = ∑_{u ≠ v} ℓ₀(u) 1_{u ∼ v}`. -/
theorem sparseAux_delta0_eq {n : ℕ} (B₀ : Set (Fin n)) (v : Fin n) (ω : EdgeVars n) :
    (nbrCount (graphOfEdges ω) B₀ᶜ v : ℝ) - nbrCount (graphOfEdges ω) B₀ v =
      ∑ u : {u : Fin n // u ≠ v}, sparseAux_sgn B₀ u.1 * edgeInd s(v, u.1) ω := by
  classical
  rw [nbrCount_graphOfEdges, nbrCount_graphOfEdges, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  rw [← Finset.sum_subtype (Finset.univ.filter fun u : Fin n => u ≠ v) (by simp)
    (fun u => sparseAux_sgn B₀ u * edgeInd s(v, u) ω), Finset.sum_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases huv : u = v
  · simp [huv]
  · by_cases hu : u ∈ B₀ <;> simp [huv, hu, sparseAux_sgn]

/-- `D_c > 0` forces `c > 1.12` (as `Φ₀ < 1/2`), for `c > 0`. -/
theorem sparseAux_c_gt {c : ℝ} (hc : 0 < c) (hDc : 0 < Dc c) : 1.12 < c := by
  unfold Dc at hDc
  have h1 := Φ₀_lt_half (2 - 1 / c)
  have h2 : 0.56 / c < 1 / 2 := by linarith
  rw [div_lt_iff₀ hc] at h2
  linarith

/-- Step 1 of the proof of Proposition 2.2, for one vertex `v`:
`P(v ∈ B₁) ≤ P(δ₀(v) ≤ 0) ≤ 1/2 − D_c min{1, Δ√p/√n}`. -/
theorem sparseAux_prob_blue_le (hBE : ShevtsovaBerryEsseen) {n : ℕ} {p Δ c : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hc : 0 < c) (hDc : 0 < Dc c) (hcΔ : c ≤ p * Δ)
    (hcn : c ≤ Real.sqrt (p * (1 - p) * n)) {B₀ : Set (Fin n)}
    (hB₀ : (B₀.ncard : ℝ) ≤ n / 2 - Δ) (v : Fin n) :
    (edgeLaw n p).real {ω | v ∈ majorityStep (graphOfEdges ω) B₀} ≤
      1 / 2 - Dc c * min 1 (Δ * Real.sqrt p / Real.sqrt n) := by
  classical
  -- Preliminaries: `c > 1.12`, `σ² = p(1 − p) ≤ 1/4`, `c² ≤ σ² n`, so `n ≥ 5`; `Δ ≥ c`.
  have hc1 := sparseAux_c_gt hc hDc
  set q := p * (1 - p) with hq
  have hq0 : 0 < q := mul_pos hp0 (by linarith)
  have hq4 : q ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have hcq : c ^ 2 ≤ q * n := by
    have := (Real.le_sqrt hc.le (by positivity)).mp hcn
    linarith
  have hn5 : (5 : ℝ) ≤ n := by nlinarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hΔ0 : 0 < Δ := by
    by_contra h; push Not at h; nlinarith
  have hΔc : c ≤ Δ := le_trans hcΔ (by nlinarith)
  set σ := Real.sqrt q with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr hq0
  have hσ2 : σ ^ 2 = q := Real.sq_sqrt hq0.le
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  -- `δ₀(v) = ∑_{u ≠ v} ℓ₀(u) 1_{u ∼ v}`, a sum of `n − 1` signed Bernoulli variables.
  set Y : {u : Fin n // u ≠ v} → EdgeVars n → ℝ := fun u => edgeInd s(v, u.1) with hYdef
  have hY : IsBernoulliFamily (edgeLaw n p) p Y := isBernoulliFamily_edgesAt hp0.le hp1.le v
  set sg : {u : Fin n // u ≠ v} → ℝ := fun u => sparseAux_sgn B₀ u.1 with hsg
  have hsg1 : ∀ u, sg u = 1 ∨ sg u = -1 := fun u => by
    simp only [hsg, sparseAux_sgn]; split_ifs <;> simp
  set S := (Finset.univ : Finset {u : Fin n // u ≠ v}) with hS
  have hScard : (S.card : ℝ) = n - 1 := by
    have h1 : S.card = n - 1 := by rw [hS, Finset.card_univ]; simp
    have h2 : 1 ≤ n := by
      have : (1 : ℝ) ≤ n := by linarith
      exact_mod_cast this
    rw [h1, Nat.cast_sub h2, Nat.cast_one]
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < S.card := by rw [hScard]; linarith
    exact_mod_cast this
  -- `v ∈ B₁ ⟹ δ₀(v) ≤ 0`
  have hsub : {ω | v ∈ majorityStep (graphOfEdges ω) B₀} ⊆
      {ω | ∑ u ∈ S, sg u * Y u ω ≤ 0} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have h := sparseAux_delta0_eq B₀ v ω
    have hle : nbrCount (graphOfEdges ω) B₀ᶜ v ≤ nbrCount (graphOfEdges ω) B₀ v := by
      rcases hω with h' | h'
      · exact h'.le
      · exact h'.1.le
    have hle' : (nbrCount (graphOfEdges ω) B₀ᶜ v : ℝ) ≤ nbrCount (graphOfEdges ω) B₀ v := by
      exact_mod_cast hle
    rw [hS, hsg, hYdef]
    linarith
  -- `E δ₀(v) = p ∑_{u ≠ v} ℓ₀(u) ≥ p (2Δ − 1)`
  set m := ∫ ω', ∑ u ∈ S, sg u * Y u ω' ∂(edgeLaw n p) with hm
  have hmint : m = p * ∑ u ∈ S, sg u := by
    rw [hm, integral_finsetSum S fun i _ => (sparseAux_integrable hY i).const_mul (sg i),
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by rw [integral_const_mul, hY.integral_eq u]; ring
  have hsgsum : ∑ u : Fin n, sparseAux_sgn B₀ u = n - 2 * B₀.ncard := by
    rw [sparseAux_ncard_eq_sum, Finset.mul_sum]
    have : ∀ u : Fin n, sparseAux_sgn B₀ u = 1 - 2 * (if u ∈ B₀ then (1 : ℝ) else 0) := by
      intro u; unfold sparseAux_sgn; split_ifs <;> norm_num
    simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have hsgS : ∑ u ∈ S, sg u = n - 2 * B₀.ncard - sparseAux_sgn B₀ v := by
    have h1 : ∑ u ∈ S, sg u = ∑ u ∈ Finset.univ.erase v, sparseAux_sgn B₀ u := by
      rw [← Finset.filter_ne', Finset.sum_subtype (Finset.univ.filter fun u => u ≠ v)
        (p := fun u => u ≠ v) (fun u => by simp) (fun u => sparseAux_sgn B₀ u)]
    rw [h1, ← hsgsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
    ring
  have hsgv : sparseAux_sgn B₀ v ≤ 1 := by unfold sparseAux_sgn; split_ifs <;> norm_num
  have hmlow : p * (2 * Δ - 1) ≤ m := by
    rw [hmint, hsgS]
    have : 2 * Δ - 1 ≤ n - 2 * B₀.ncard - sparseAux_sgn B₀ v := by linarith
    exact mul_le_mul_of_nonneg_left this hp0.le
  -- Corollary A.2 at `x = −E δ₀(v)`:
  -- `P(δ₀(v) ≤ 0) ≤ 1/2 − Φ₀(E δ₀(v)/(σ √(n − 1))) + C_BE (1 − 2σ²)/(σ √(n − 1))`
  have hBEv := corollaryA_2 hBE hp0 hp1 hY sg hsg1 hSne (-m)
  have hset : {ω | ∑ u ∈ S, sg u * Y u ω - m ≤ -m} = {ω | ∑ u ∈ S, sg u * Y u ω ≤ 0} := by
    ext ω; simp only [Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith
  rw [hset, hScard] at hBEv
  have hn1 : 0 < Real.sqrt (n - 1) := Real.sqrt_pos.mpr (by linarith)
  set K1 := σ * Real.sqrt (n - 1) with hK1
  set K := σ * Real.sqrt n with hK
  have hK10 : 0 < K1 := mul_pos hσ0 hn1
  have hK0 : 0 < K := mul_pos hσ0 hsn
  have hP1 : (edgeLaw n p).real {ω | ∑ u ∈ S, sg u * Y u ω ≤ 0} ≤
      1 / 2 - Φ₀ (m / K1) + 0.56 * (1 - 2 * q) / K1 := by
    have := (abs_le.mp hBEv).2
    rw [Φ, neg_div, Φ₀_neg] at this
    linarith
  -- `E δ₀(v) ≥ p(2Δ − 1) ≥ 0` and `√(n − 1) ≤ √n`; `C_BE (1 − 2σ²)/(σ √(n − 1)) ≤ C_BE/(σ √n)`
  -- since `4σ²(1 − σ²) n ≥ 3 c² ≥ 1`.
  set X := p * (2 * Δ - 1) / K with hX
  have hX0 : 0 ≤ X := by
    rw [hX]; apply div_nonneg _ hK0.le; apply mul_nonneg hp0.le; linarith
  have hΦ1 : Φ₀ X ≤ Φ₀ (m / K1) := by
    apply strictMono_Φ₀.monotone
    rw [hX]
    calc p * (2 * Δ - 1) / K ≤ p * (2 * Δ - 1) / K1 := by
          apply div_le_div_of_nonneg_left _ hK10
          · rw [hK1, hK]
            exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hσ0.le
          · apply mul_nonneg hp0.le; linarith
      _ ≤ m / K1 := div_le_div_of_nonneg_right hmlow hK10.le
  have herr : 0.56 * (1 - 2 * q) / K1 ≤ 0.56 / K := by
    rw [div_le_div_iff₀ hK10 hK0, hK1, hK]
    have h1 : (1 - 2 * q) * Real.sqrt n ≤ Real.sqrt (n - 1) := by
      have hpos : 0 ≤ 1 - 2 * q := by linarith
      rw [show (1 - 2 * q) * Real.sqrt n = Real.sqrt ((1 - 2 * q) ^ 2 * n) by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpos]]
      apply Real.sqrt_le_sqrt
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 0.56 * σ)
    nlinarith
  -- `Φ₀(x) ≥ min{1, x/y} Φ₀(y)` with `y = 2 − 1/c > 0`
  set y := 2 - 1 / c with hy
  have hy0 : 0 < y := by
    rw [hy]
    have : 1 / c < 1 := by rw [div_lt_one hc]; linarith
    linarith
  have hφ := min_mul_Φ₀_le hX0 hy0
  set φ := Φ₀ y with hφdef
  have hφ0 : 0 ≤ φ := Φ₀_nonneg hy0.le
  have hDcφ : Dc c = φ - 0.56 / c := rfl
  -- the two branches of the minimum
  have hA1 : Dc c ≤ φ - 0.56 / K := by
    rw [hDcφ]
    have : 0.56 / K ≤ 0.56 / c := by
      apply div_le_div_of_nonneg_left (by norm_num) hc
      rw [hK, ← Real.sqrt_mul hq0.le]; exact hcn
    linarith
  have hA2 : Dc c * (p * Δ / K) ≤ X / y * φ - 0.56 / K := by
    have hid1 : X / y * φ - 0.56 / K = (2 * (φ / y) * (p * Δ) - (p * (φ / y) + 0.56)) / K := by
      rw [hX]; field_simp; ring
    have hid2 : Dc c = 2 * (φ / y) - (φ / y + 0.56) / c := by
      have h1 : φ / y * (2 - 1 / c) = φ := by rw [← hy]; exact div_mul_cancel₀ φ hy0.ne'
      have h2 : 2 * (φ / y) - (φ / y + 0.56) / c = φ / y * (2 - 1 / c) - 0.56 / c := by ring
      rw [hDcφ, h2, h1]
    rw [hid1, hid2]
    have hφy : 0 ≤ φ / y := div_nonneg hφ0 hy0.le
    have hpΔc : 1 ≤ p * Δ / c := by rw [le_div_iff₀ hc]; linarith
    have key : p * (φ / y) + 0.56 ≤ (φ / y + 0.56) * (p * Δ / c) := by
      have k1 : (φ / y + 0.56) * 1 ≤ (φ / y + 0.56) * (p * Δ / c) :=
        mul_le_mul_of_nonneg_left hpΔc (by positivity)
      have k2 : p * (φ / y) ≤ φ / y := mul_le_of_le_one_left hφy hp1.le
      linarith
    have hLHS : (2 * (φ / y) - (φ / y + 0.56) / c) * (p * Δ / K) =
        (2 * (φ / y) * (p * Δ) - (φ / y + 0.56) * (p * Δ / c)) / K := by
      field_simp
    rw [hLHS]
    apply div_le_div_of_nonneg_right _ hK0.le
    linarith
  have hmin : Dc c * min 1 (p * Δ / K) ≤ min (φ - 0.56 / K) (X / y * φ - 0.56 / K) := by
    rw [mul_min_of_nonneg _ _ hDc.le, mul_one]
    exact min_le_min hA1 hA2
  have hminφ : min 1 (X / y) * φ - 0.56 / K = min (φ - 0.56 / K) (X / y * φ - 0.56 / K) := by
    rw [min_mul_of_nonneg _ _ hφ0, one_mul, min_sub_sub_right]
  -- `pΔ/(σ√n) ≥ Δ√p/√n`
  have hratio : Δ * Real.sqrt p / Real.sqrt n ≤ p * Δ / K := by
    rw [hK, hσ, hq, Real.sqrt_mul hp0.le, div_le_div_iff₀ hsn (by positivity)]
    have hs1 : Real.sqrt (1 - p) ≤ 1 := by
      rw [Real.sqrt_le_one]; linarith
    have hsp : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
    have heq : Δ * Real.sqrt p * (Real.sqrt p * Real.sqrt (1 - p) * Real.sqrt n) =
        (p * Δ * Real.sqrt n) * Real.sqrt (1 - p) := by
      calc _ = (Real.sqrt p * Real.sqrt p) * Δ * Real.sqrt n * Real.sqrt (1 - p) := by ring
        _ = _ := by rw [hsp]
    rw [heq]
    exact mul_le_of_le_one_right (by positivity) hs1
  have hfinal : Dc c * min 1 (Δ * Real.sqrt p / Real.sqrt n) ≤ Dc c * min 1 (p * Δ / K) :=
    mul_le_mul_of_nonneg_left (min_le_min le_rfl hratio) hDc.le
  calc (edgeLaw n p).real {ω | v ∈ majorityStep (graphOfEdges ω) B₀}
      ≤ (edgeLaw n p).real {ω | ∑ u ∈ S, sg u * Y u ω ≤ 0} := measureReal_mono hsub
    _ ≤ 1 / 2 - Φ₀ (m / K1) + 0.56 * (1 - 2 * q) / K1 := hP1
    _ ≤ 1 / 2 - Φ₀ X + 0.56 / K := by linarith
    _ ≤ 1 / 2 - (min 1 (X / y) * φ - 0.56 / K) := by linarith
    _ ≤ 1 / 2 - Dc c * min 1 (Δ * Real.sqrt p / Real.sqrt n) := by
        rw [hminφ]; linarith

open Classical in
/-- Neighbour counts of `u` when the edge variable of `uv` is set to `b`: the edges `uw`, `w ≠ v`,
plus `1` if `b` holds and `v ∈ T`. -/
theorem sparseAux_nbrCount_update {n : ℕ} {u v : Fin n} (huv : u ≠ v) (ω : EdgeVars n) (b : Prop)
    (T : Set (Fin n)) :
    (nbrCount (graphOfEdges (Function.update ω s(u, v) b)) T u : ℝ) =
      ∑ w ∈ Finset.univ.filter (fun w => w ∈ T ∧ w ≠ u ∧ w ≠ v), edgeInd s(u, w) ω +
        (if v ∈ T ∧ b then 1 else 0) := by
  rw [nbrCount_graphOfEdges, Finset.sum_filter, Finset.sum_filter]
  have hpt : ∀ w : Fin n, (if w ∈ T ∧ w ≠ u then edgeInd s(u, w) (Function.update ω s(u, v) b)
      else 0) = (if w ∈ T ∧ w ≠ u ∧ w ≠ v then edgeInd s(u, w) ω else 0) +
        (if v = w then (if v ∈ T ∧ b then 1 else 0) else 0) := by
    intro w
    by_cases hwv : w = v
    · subst hwv
      by_cases hvT : w ∈ T <;> by_cases hb : b <;> simp [edgeInd, Ne.symm huv, hvT, hb]
    · have hne : s(u, w) ≠ s(u, v) := by
        intro h
        rcases Sym2.eq_iff.mp h with h' | h'
        · exact hwv h'.2
        · exact huv h'.1
      by_cases hwu : w = u
      · subst hwu
        simp [Ne.symm hwv]
      · by_cases hwT : w ∈ T <;>
          simp [hwu, hwT, hwv, Ne.symm hwv, edgeInd]
  rw [Finset.sum_congr rfl fun w _ => hpt w, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

open Classical in
/-- The case analysis behind the paper's identity `Pr(E_v) − Pr(F_v) = ℓ₀(u) Pr(X = …)`: if adding
the edge `uv` changes whether `u` is Blue the next day, then the numbers `a` of Red and `β` of Blue
neighbours of `u` other than `v` satisfy `a = β + k`, `k = 1_{u ∈ B₀} − 1_{v ∉ B₀}`. -/
theorem sparseAux_flip {a β : ℕ} {bu bv : Prop}
    (h : ¬ ((a + (if bv then 0 else 1) < β + (if bv then 1 else 0) ∨
        (a + (if bv then 0 else 1) = β + (if bv then 1 else 0) ∧ bu)) ↔ (a < β ∨ (a = β ∧ bu)))) :
    (a : ℝ) = β + ((if bu then 1 else 0) - (if bv then 0 else 1)) := by
  by_cases hu : bu <;> by_cases hv : bv <;>
    simp only [hu, hv, ite_true, ite_false, and_true, and_false, or_false, add_zero] at h ⊢
  · have : a = β + 1 := by omega
    rw [this]; push_cast; ring
  · have : a = β := by omega
    rw [this]; ring
  · have : a = β := by omega
    rw [this]; ring
  · have : a + 1 = β := by omega
    rw [← this]; push_cast; ring

open Classical in
/-- The change of `P(u ∈ B₁)` when the edge `uv` is toggled is at most the point probability of
Lemma A.3 for the `n − 2` other edges at `u`:
`|P(u ∈ B₁ | u ∼ v) − P(u ∈ B₁ | u ≁ v)| ≤ P(X = k) ≤ 1.12 (1 − 2σ²)/(σ √(n − 2))`. -/
theorem sparseAux_edgeCond_diff_le (hBE : ShevtsovaBerryEsseen) {n : ℕ} {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hn : 3 ≤ n) (B₀ : Set (Fin n)) {u v : Fin n} (huv : u ≠ v) :
    |edgeCondExp n p s(u, v) True
          (fun ω => if u ∈ majorityStep (graphOfEdges ω) B₀ then (1 : ℝ) else 0) -
        edgeCondExp n p s(u, v) False
          (fun ω => if u ∈ majorityStep (graphOfEdges ω) B₀ then (1 : ℝ) else 0)| ≤
      1.12 * (1 - 2 * (p * (1 - p))) / (Real.sqrt (p * (1 - p)) * Real.sqrt ((n : ℝ) - 2)) := by
  set μ := edgeLaw n p with hμ
  set f : EdgeVars n → ℝ := fun ω => if u ∈ majorityStep (graphOfEdges ω) B₀ then 1 else 0
    with hf
  set Y : {w : Fin n // w ≠ u} → EdgeVars n → ℝ := fun w => edgeInd s(u, w.1) with hYdef
  have hY : IsBernoulliFamily μ p Y := isBernoulliFamily_edgesAt hp0.le hp1.le u
  set S₁ := Finset.univ.filter (fun w : {w : Fin n // w ≠ u} => w.1 ∈ B₀ᶜ ∧ w.1 ≠ v) with hS₁
  set S₂ := Finset.univ.filter (fun w : {w : Fin n // w ≠ u} => w.1 ∈ B₀ ∧ w.1 ≠ v) with hS₂
  have hS : Disjoint S₁ S₂ := by
    rw [hS₁, hS₂, Finset.disjoint_filter]
    intro w _ h1 h2; exact h1.1 h2.1
  -- `|S₁| + |S₂| = n − 2`
  have hcardN : S₁.card + S₂.card = n - 2 := by
    set s := Finset.univ.filter (fun w : {w : Fin n // w ≠ u} => w.1 ≠ v) with hs
    have hs1 : s.filter (fun w => w.1 ∈ B₀) = S₂ := by
      ext w; simp [hs, hS₂, and_comm]
    have hs2 : s.filter (fun w => ¬ w.1 ∈ B₀) = S₁ := by
      ext w; simp [hs, hS₁, and_comm]
    have hscard : s.card = n - 2 := by
      have h1 : s = (Finset.univ : Finset {w : Fin n // w ≠ u}).erase ⟨v, Ne.symm huv⟩ := by
        ext w; simp [hs, Subtype.ext_iff]
      rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      simp; omega
    have := Finset.card_filter_add_card_filter_not (s := s) (fun w => w.1 ∈ B₀)
    rw [hs1, hs2] at this
    omega
  have hcard : (S₁.card : ℝ) + S₂.card = (n : ℝ) - 2 := by
    have : ((S₁.card + S₂.card : ℕ) : ℝ) = ((n - 2 : ℕ) : ℝ) := by rw [hcardN]
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)] at this
    exact this
  have hne : 0 < S₁.card + S₂.card := by omega
  have hsum : ∀ (T : Set (Fin n)) (ω : EdgeVars n),
      ∑ w ∈ Finset.univ.filter (fun w : {w : Fin n // w ≠ u} => w.1 ∈ T ∧ w.1 ≠ v), Y w ω =
        ∑ w ∈ Finset.univ.filter (fun w => w ∈ T ∧ w ≠ u ∧ w ≠ v), edgeInd s(u, w) ω := by
    intro T ω
    have hmap : (Finset.univ.filter (fun w : {w : Fin n // w ≠ u} => w.1 ∈ T ∧ w.1 ≠ v)).map
        (Function.Embedding.subtype _) = Finset.univ.filter (fun w => w ∈ T ∧ w ≠ u ∧ w ≠ v) := by
      ext w
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coe_subtype, Subtype.exists]
      constructor
      · rintro ⟨w', hw'u, ⟨hT, hv⟩, rfl⟩; exact ⟨hT, hw'u, hv⟩
      · rintro ⟨hT, hu, hv⟩; exact ⟨w, hu, ⟨hT, hv⟩, rfl⟩
    rw [← hmap, Finset.sum_map]
    rfl
  set k : ℝ := (if u ∈ B₀ then 1 else 0) - (if v ∈ B₀ then 0 else 1) with hk
  -- the difference of the two conditional expectations is one integral
  have hdiff : edgeCondExp n p s(u, v) True f - edgeCondExp n p s(u, v) False f =
      ∫ ω, (f (Function.update ω s(u, v) True) - f (Function.update ω s(u, v) False)) ∂μ := by
    unfold edgeCondExp
    rw [integral_sub Integrable.of_finite Integrable.of_finite]
  -- pointwise: the two values differ only if `X = ∑_{S₁} − ∑_{S₂} = k`
  have hpt : ∀ ω, |f (Function.update ω s(u, v) True) - f (Function.update ω s(u, v) False)| ≤
      if ∑ w ∈ S₁, Y w ω = ∑ w ∈ S₂, Y w ω + k then 1 else 0 := by
    intro ω
    have hRT := sparseAux_nbrCount_update huv ω True B₀ᶜ
    have hRF := sparseAux_nbrCount_update huv ω False B₀ᶜ
    have hBT := sparseAux_nbrCount_update huv ω True B₀
    have hBF := sparseAux_nbrCount_update huv ω False B₀
    simp only [and_true, and_false, ite_false, add_zero] at hRT hRF hBT hBF
    set GT := graphOfEdges (Function.update ω s(u, v) True) with hGT
    set GF := graphOfEdges (Function.update ω s(u, v) False) with hGF
    -- in `ℕ`: `a_T = a_F + 1_{v ∉ B₀}`, `β_T = β_F + 1_{v ∈ B₀}`
    have haT : nbrCount GT B₀ᶜ u = nbrCount GF B₀ᶜ u + (if v ∈ B₀ then 0 else 1) := by
      have : (nbrCount GT B₀ᶜ u : ℝ) = nbrCount GF B₀ᶜ u + (if v ∈ B₀ then 0 else 1) := by
        rw [hRT, hRF]; simp only [Set.mem_compl_iff]; split_ifs <;> simp
      exact_mod_cast (by rw [this]; push_cast [Nat.cast_ite]; rfl :
        (nbrCount GT B₀ᶜ u : ℝ) = ((nbrCount GF B₀ᶜ u + (if v ∈ B₀ then 0 else 1) : ℕ) : ℝ))
    have hβT : nbrCount GT B₀ u = nbrCount GF B₀ u + (if v ∈ B₀ then 1 else 0) := by
      have : (nbrCount GT B₀ u : ℝ) = nbrCount GF B₀ u + (if v ∈ B₀ then 1 else 0) := by
        rw [hBT, hBF]
      exact_mod_cast (by rw [this]; push_cast [Nat.cast_ite]; rfl :
        (nbrCount GT B₀ u : ℝ) = ((nbrCount GF B₀ u + (if v ∈ B₀ then 1 else 0) : ℕ) : ℝ))
    have hf01 : ∀ ω', f ω' = 0 ∨ f ω' = 1 := fun ω' => by
      simp only [hf]; split_ifs <;> simp
    by_cases hX : ∑ w ∈ S₁, Y w ω = ∑ w ∈ S₂, Y w ω + k
    · rw [ite_eq_left hX]
      rcases hf01 (Function.update ω s(u, v) True) with h1 | h1 <;>
        rcases hf01 (Function.update ω s(u, v) False) with h2 | h2 <;> simp [h1, h2]
    · rw [ite_eq_right hX]
      -- otherwise `u` is Blue tomorrow with the edge iff without it
      have hiff : u ∈ majorityStep GT B₀ ↔ u ∈ majorityStep GF B₀ := by
        by_contra hcon
        apply hX
        have hR : ∑ w ∈ S₁, Y w ω = nbrCount GF B₀ᶜ u := by
          rw [hRF, hS₁]; convert hsum B₀ᶜ ω
        have hB : ∑ w ∈ S₂, Y w ω = nbrCount GF B₀ u := by
          rw [hBF, hS₂]; convert hsum B₀ ω
        rw [hR, hB, hk]
        apply sparseAux_flip
        simpa only [majorityStep, Set.mem_ofPred_eq, haT, hβT] using hcon
      have : f (Function.update ω s(u, v) True) = f (Function.update ω s(u, v) False) := by
        simp only [hf]
        exact if_congr hiff rfl rfl
      rw [this, sub_self, abs_zero]
  have hmeas : MeasurableSet {ω | ∑ w ∈ S₁, Y w ω = ∑ w ∈ S₂, Y w ω + k} :=
    measurableSet_edgeVars _
  calc |edgeCondExp n p s(u, v) True f - edgeCondExp n p s(u, v) False f|
      = |∫ ω, (f (Function.update ω s(u, v) True) - f (Function.update ω s(u, v) False)) ∂μ| := by
        rw [hdiff]
    _ ≤ ∫ ω, |f (Function.update ω s(u, v) True) - f (Function.update ω s(u, v) False)| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ ω, (if ∑ w ∈ S₁, Y w ω = ∑ w ∈ S₂, Y w ω + k then (1 : ℝ) else 0) ∂μ :=
        integral_mono Integrable.of_finite Integrable.of_finite hpt
    _ = μ.real {ω | ∑ w ∈ S₁, Y w ω = ∑ w ∈ S₂, Y w ω + k} := by
        rw [← integral_indicator_one hmeas]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        by_cases h : ∑ w ∈ S₁, Y w ω = ∑ w ∈ S₂, Y w ω + k <;> simp [h]
    _ ≤ 1.12 * (1 - 2 * (p * (1 - p))) /
          (Real.sqrt (p * (1 - p)) * Real.sqrt (S₁.card + S₂.card)) :=
        sparseAux_pointProb_le hBE hp0 hp1 hY hS hne k
    _ = 1.12 * (1 - 2 * (p * (1 - p))) / (Real.sqrt (p * (1 - p)) * Real.sqrt ((n : ℝ) - 2)) := by
        rw [hcard]
open Classical in
/-- The integral of an indicator on `edgeLaw` is a probability. -/
theorem sparseAux_integral_ite {n : ℕ} {p : ℝ} (P : EdgeVars n → Prop) :
    ∫ ω, (if P ω then (1 : ℝ) else 0) ∂(edgeLaw n p) = (edgeLaw n p).real {ω | P ω} := by
  rw [← integral_indicator_one (measurableSet_edgeVars _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  by_cases h : P ω <;> simp [h]

open Classical in
/-- **Proposition 2.2** (`S:prop:day1-exp-var`), with the variance bound that its proof gives. For
`0 < c ≤ min{pΔ, √(p(1 − p)n)}` and `|B₀| ≤ n/2 − Δ`,
`E|B₁| ≤ n/2 − D_c min{n, Δ √(pn)}` and `Var|B₁| ≤ varConst n p · n` (printed: `7n/12`).

Deviation (hypothesis the proof uses): the statement also assumes `D_c > 0`, which is all that
Lemma 2.1 uses. The proof's last step turns `1/2 − min{D_c, D_c x}` into `1/2 − D_c min{1, x}`,
which needs `D_c ≥ 0`; it also sets `y = 2 − 1/c > 0` and replaces the Berry–Esseen error
`C_BE (1 − 2σ²)/(σ √(n − 1))` by `C_BE / (σ √n)`, valid when `4σ²(1 − σ²) n ≥ 1`. For `c > 0`,
`D_c > 0` gives `0.56/c < Φ₀(2 − 1/c) < 1/2`, so `c > 1.12`, hence both.

Departure from the paper (a cited lemma applied outside its hypotheses): the covariance step
applies Lemma A.3 at points `d ≤ 0` (it prints `d ∈ {0, −1}`; the formal proof needs
`d ∈ {−1, 0, 1}`), while Lemma A.3 assumes `0 < d < (n₁ + n₂)/2`. The proof
uses the form of Lemma A.3 for every integer `d` (`sparseAux_pointProb_le`, from which `lemmaA_3`
follows; it is the dense paper's Lemma 2.4), which Lemma A.3's proof gives. -/
theorem proposition2_2 (hBE : ShevtsovaBerryEsseen) {n : ℕ} {p Δ c : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hc : 0 < c) (hDc : 0 < Dc c) (hcΔ : c ≤ p * Δ)
    (hcn : c ≤ Real.sqrt (p * (1 - p) * n)) {B₀ : Set (Fin n)}
    (hB₀ : (B₀.ncard : ℝ) ≤ n / 2 - Δ) :
    gnpExp n p (fun G => ((blueAfter G B₀ 1).ncard : ℝ)) ≤
        n / 2 - Dc c * min (n : ℝ) (Δ * Real.sqrt (p * n)) ∧
      gnpVar n p (fun G => ((blueAfter G B₀ 1).ncard : ℝ)) ≤ varConst n p * n := by
  -- Preliminaries: `c > 1.12` and `c² ≤ p(1 − p) n ≤ n/4`, so `n ≥ 5`.
  have hc1 := sparseAux_c_gt hc hDc
  set q := p * (1 - p) with hq
  have hq0 : 0 < q := mul_pos hp0 (by linarith)
  have hq4 : q ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have hcq : c ^ 2 ≤ q * n := by
    have := (Real.le_sqrt hc.le (by positivity)).mp hcn
    linarith
  have hn5 : (5 : ℝ) ≤ n := by nlinarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hn3 : 3 ≤ n := by
    have : (3 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  set μ := edgeLaw n p with hμ
  -- `|B₁| = ∑_v 1_{B₁}(v)`
  set f : Fin n → EdgeVars n → ℝ :=
    fun v ω => if v ∈ majorityStep (graphOfEdges ω) B₀ then 1 else 0 with hf
  have hB1 : ∀ ω, ((blueAfter (graphOfEdges ω) B₀ 1).ncard : ℝ) = ∑ v, f v ω := by
    intro ω
    rw [show blueAfter (graphOfEdges ω) B₀ 1 = majorityStep (graphOfEdges ω) B₀ from rfl,
      sparseAux_ncard_eq_sum]
  have hf01 : ∀ v ω, f v ω ∈ Set.Icc (0 : ℝ) 1 := fun v ω => by
    simp only [hf]; split_ifs <;> simp
  have hfmeas : ∀ v, Measurable (f v) := fun v => measurable_of_finite _
  have hmemLp : ∀ v, MemLp (f v) 2 μ := fun v =>
    memLp_of_bounded (Filter.Eventually.of_forall (hf01 v)) (hfmeas v).aestronglyMeasurable 2
  constructor
  · -- Step 1: `E|B₁| = ∑_v P(v ∈ B₁) ≤ ∑_v (1/2 − D_c min{1, Δ√p/√n})`.
    rw [gnpExp_eq]
    simp_rw [hB1]
    rw [integral_finsetSum _ (fun v _ => Integrable.of_finite)]
    have hv : ∀ v, ∫ ω, f v ω ∂μ ≤ 1 / 2 - Dc c * min 1 (Δ * Real.sqrt p / Real.sqrt n) := by
      intro v
      rw [hf, sparseAux_integral_ite]
      exact sparseAux_prob_blue_le hBE hp0 hp1 hc hDc hcΔ hcn hB₀ v
    have hmin : (n : ℝ) * min 1 (Δ * Real.sqrt p / Real.sqrt n) =
        min (n : ℝ) (Δ * Real.sqrt (p * n)) := by
      rw [mul_min_of_nonneg _ _ hn0.le, mul_one, Real.sqrt_mul hp0.le]
      congr 1
      rw [mul_div_assoc', mul_comm, mul_div_assoc, Real.div_sqrt]; ring
    calc ∑ v, ∫ ω, f v ω ∂μ ≤ ∑ v : Fin n, (1 / 2 - Dc c * min 1 (Δ * Real.sqrt p / Real.sqrt n)) :=
          Finset.sum_le_sum fun v _ => hv v
      _ = n * (1 / 2 - Dc c * min 1 (Δ * Real.sqrt p / Real.sqrt n)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = n / 2 - Dc c * min (n : ℝ) (Δ * Real.sqrt (p * n)) := by
          rw [← hmin]; ring
  · -- Step 2: `Var|B₁| = ∑_v Var 1_{B₁}(v) + ∑_{u ≠ v} Cov(1_{B₁}(u), 1_{B₁}(v))`.
    rw [gnpVar_eq]
    have hfun : (fun ω => ((blueAfter (graphOfEdges ω) B₀ 1).ncard : ℝ)) = fun ω => ∑ v, f v ω :=
      funext hB1
    rw [hfun, variance_fun_sum hmemLp]
    -- the variances: `Var 1_{B₁}(v) ≤ 1/4`
    have hdiag : ∀ v, cov[f v, f v; μ] ≤ 1 / 4 := by
      intro v
      rw [covariance_self (hfmeas v).aemeasurable]
      have := variance_le_sq_of_bounded (μ := μ) (Filter.Eventually.of_forall (hf01 v))
        (hfmeas v).aemeasurable
      norm_num at this ⊢; exact this
    -- the covariances: `Cov = p(1 − p)(P(E_u) − P(F_u))(P(E_v) − P(F_v))`, each factor at most
    -- the point probability of Lemma A.3 (general form), `1.12 (1 − 2σ²)/(σ √(n − 2))`
    set Q := 1.12 * (1 - 2 * q) / (Real.sqrt q * Real.sqrt ((n : ℝ) - 2)) with hQ
    set K := 4 * 0.56 ^ 2 * (1 - 2 * q) ^ 2 / ((n : ℝ) - 2) with hK
    have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    have hQK : q * Q ^ 2 = K := by
      rw [hQ, hK, div_pow, mul_pow (Real.sqrt q), Real.sq_sqrt hq0.le, Real.sq_sqrt hn2.le]
      field_simp; ring
    have hoff : ∀ u v, u ≠ v → cov[f u, f v; μ] ≤ K := by
      intro u v huv
      set e := s(u, v) with he
      have hediag : ¬ e.IsDiag := by rw [he, Sym2.mk_isDiag_iff]; exact huv
      have heu : e ∈ edgesAt u := ⟨v, Ne.symm huv, rfl⟩
      have hev : e ∈ edgesAt v := ⟨u, huv, Sym2.eq_swap⟩
      have hdep : ∀ w, DependsOn (f w) (edgesAt w) := by
        intro w x y hxy
        have h := dependsOn_mem_majorityStep B₀ w hxy
        simp only [hf]
        exact if_congr (Iff.of_eq h) rfl rfl
      have hfu : DependsOn (f u) (insert e (edgesAt u \ {e})) := by
        rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem heu]; exact hdep u
      have hfv : DependsOn (f v) (insert e (edgesAt v \ {e})) := by
        rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hev]; exact hdep v
      have hst : Disjoint (edgesAt u \ {e}) (edgesAt v \ {e}) := by
        rw [Set.disjoint_left]
        rintro x ⟨hxu, hxe⟩ ⟨hxv, -⟩
        have : x ∈ edgesAt u ∩ edgesAt v := ⟨hxu, hxv⟩
        rw [edgesAt_inter_edgesAt huv] at this
        exact hxe this
      have hbound : ∀ w ω, |f w ω| ≤ 1 := fun w ω => by
        rw [abs_le]; constructor <;> linarith [(hf01 w ω).1, (hf01 w ω).2]
      have hcov := covariance_shared_edge hp0.le hp1.le hediag hfu hfv hst
        (fun h => h.2 rfl) (fun h => h.2 rfl) (hbound u) (hbound v)
      have hΔu := sparseAux_edgeCond_diff_le hBE hp0 hp1 hn3 B₀ huv
      have hΔv := sparseAux_edgeCond_diff_le hBE hp0 hp1 hn3 B₀ (Ne.symm huv)
      rw [Sym2.eq_swap] at hΔv
      rw [covariance_eq_sub (hmemLp u) (hmemLp v)]
      have hmul : μ[f u * f v] = ∫ ω, f u ω * f v ω ∂μ := rfl
      rw [hmul, hcov]
      set a := edgeCondExp n p e True (f u) - edgeCondExp n p e False (f u)
      set b := edgeCondExp n p e True (f v) - edgeCondExp n p e False (f v)
      have ha : |a| ≤ Q := hΔu
      have hb : |b| ≤ Q := hΔv
      calc p * (1 - p) * a * b ≤ q * (|a| * |b|) := by
            rw [mul_assoc, ← hq]
            exact mul_le_mul_of_nonneg_left
              ((le_abs_self _).trans (abs_mul a b).le) hq0.le
        _ ≤ q * (Q * Q) := by
            apply mul_le_mul_of_nonneg_left _ hq0.le
            exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
        _ = K := by rw [← hQK]; ring
    -- summing: `Var|B₁| ≤ n/4 + n(n − 1) K = varConst n p · n`
    have hrow : ∀ u, ∑ v, cov[f u, f v; μ] ≤ 1 / 4 + ((n : ℝ) - 1) * K := by
      intro u
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
      have h1 : ∑ v ∈ Finset.univ.erase u, cov[f u, f v; μ] ≤
          ∑ v ∈ Finset.univ.erase u, K :=
        Finset.sum_le_sum fun v hv => hoff u v (Ne.symm (Finset.ne_of_mem_erase hv))
      have h2 : ∑ v ∈ Finset.univ.erase u, K = ((n : ℝ) - 1) * K := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      linarith [hdiag u]
    calc ∑ u, ∑ v, cov[f u, f v; μ] ≤ ∑ u : Fin n, (1 / 4 + ((n : ℝ) - 1) * K) :=
          Finset.sum_le_sum fun u _ => hrow u
      _ = n * (1 / 4 + ((n : ℝ) - 1) * K) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = varConst n p * n := by
          rw [varConst, hK, ← hq]; field_simp

/-- **Lemma 2.1** (`S:lem:day1`), with the constant that its proof gives. For
`0 < c ≤ min{pΔ, √(p(1 − p)n)}` and `0 < D < D_c`, if `|B₀| ≤ n/2 − Δ` then
`P(|B₁| ≤ n/2 − D min{n, Δ √(pn)}) ≥ 1 − C'(c, D) / min{n, pΔ²}` with
`C'(c, D) = varConst n p / (D_c − D)²` (printed: `C(c, D) = 7 / (12 (D_c − D)²)`). -/
theorem lemma2_1 (hBE : ShevtsovaBerryEsseen) {n : ℕ} {p Δ c D : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hc : 0 < c) (hcΔ : c ≤ p * Δ) (hcn : c ≤ Real.sqrt (p * (1 - p) * n)) (hD : 0 < D)
    (hDc : D < Dc c) {B₀ : Set (Fin n)} (hB₀ : (B₀.ncard : ℝ) ≤ n / 2 - Δ) :
    1 - varConst n p / ((Dc c - D) ^ 2 * min (n : ℝ) (p * Δ ^ 2)) ≤
      gnpProb n p (fun G =>
        ((blueAfter G B₀ 1).ncard : ℝ) ≤ n / 2 - D * min (n : ℝ) (Δ * Real.sqrt (p * n))) := by
  have hDc0 : 0 < Dc c := hD.trans hDc
  obtain ⟨hE, hV⟩ := proposition2_2 hBE hp0 hp1 hc hDc0 hcΔ hcn hB₀
  -- `n > 0`, `Δ > 0`, so `m = min{n, Δ√(pn)} > 0`, and `m² = n min{n, pΔ²}`
  have hq0 : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  have hn0 : (0 : ℝ) < n := by
    by_contra h; push Not at h
    have : p * (1 - p) * n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq0.le h
    rw [Real.sqrt_eq_zero'.mpr this] at hcn; linarith
  have hΔ0 : 0 < Δ := by
    by_contra h; push Not at h; nlinarith
  set m := min (n : ℝ) (Δ * Real.sqrt (p * n)) with hm
  have hpn : 0 < Real.sqrt (p * n) := Real.sqrt_pos.mpr (by positivity)
  have hm0 : 0 < m := lt_min hn0 (by positivity)
  have hm2 : m ^ 2 = n * min (n : ℝ) (p * Δ ^ 2) := by
    have hsq : (Δ * Real.sqrt (p * n)) ^ 2 = n * (p * Δ ^ 2) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    rcases le_total (n : ℝ) (Δ * Real.sqrt (p * n)) with h | h
    · rw [hm, min_eq_left h]
      have : (n : ℝ) ≤ p * Δ ^ 2 := by
        have h2 : (n : ℝ) ^ 2 ≤ (Δ * Real.sqrt (p * n)) ^ 2 := by gcongr
        rw [hsq] at h2; nlinarith
      rw [min_eq_left this]; ring
    · rw [hm, min_eq_right h]
      have : p * Δ ^ 2 ≤ (n : ℝ) := by
        have h2 : (Δ * Real.sqrt (p * n)) ^ 2 ≤ (n : ℝ) ^ 2 := by
          gcongr
        rw [hsq] at h2; nlinarith
      rw [min_eq_right this, hsq]
  -- Chebyshev above the mean
  set μ := SimpleGraph.binomialRandom (Fin n) (toUnit p) with hμ
  set X : SimpleGraph (Fin n) → ℝ := fun G => ((blueAfter G B₀ 1).ncard : ℝ) with hX
  have hXmeas : Measurable X := fun s _ => measurableSet_simpleGraph _
  have hXb : ∀ G, X G ∈ Set.Icc (0 : ℝ) n := fun G => by
    refine ⟨Nat.cast_nonneg _, ?_⟩
    show ((blueAfter G B₀ 1).ncard : ℝ) ≤ n
    have : (blueAfter G B₀ 1).ncard ≤ n := by
      calc (blueAfter G B₀ 1).ncard ≤ (Set.univ : Set (Fin n)).ncard :=
            Set.ncard_le_ncard (Set.subset_univ _)
        _ = n := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact_mod_cast this
  have hXL : MemLp X 2 μ :=
    memLp_of_bounded (Filter.Eventually.of_forall hXb) hXmeas.aestronglyMeasurable 2
  have hEX : μ[X] = gnpExp n p X := rfl
  have hVX : variance X μ = gnpVar n p X := rfl
  have hgap : 0 < (Dc c - D) * m := mul_pos (by linarith) hm0
  have hlt : μ[X] < μ[X] + (Dc c - D) * m := by linarith
  have hcheb := measureReal_ge_le_variance_div_sq hXL hlt
  rw [add_sub_cancel_left] at hcheb
  apply le_gnpProb_of_not_le
  calc gnpProb n p (fun G => ¬ X G ≤ n / 2 - D * m)
      ≤ μ.real {G | μ[X] + (Dc c - D) * m ≤ X G} := by
        refine measureReal_mono (fun G hG => ?_)
        simp only [Set.mem_ofPred_eq, not_le] at hG ⊢
        rw [hEX]; linarith
    _ ≤ variance X μ / ((Dc c - D) * m) ^ 2 := hcheb
    _ ≤ varConst n p * n / ((Dc c - D) * m) ^ 2 := by
        rw [hVX]; gcongr
    _ = varConst n p / ((Dc c - D) ^ 2 * min (n : ℝ) (p * Δ ^ 2)) := by
        rw [mul_pow, hm2]
        have : (Dc c - D) ^ 2 ≠ 0 := by positivity
        field_simp

end PowerOfFew.Sparse

end
