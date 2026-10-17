module

public import PowerOfFew.Sparse.Main
public import PowerOfFew.Sparse.ColoringAux
public import PowerOfFew.Dense.Shrinking

/-!
# Sparse paper, Section 1.4: random initial colourings

* `theorem1_4`: a "delayed" version of the theorem of Fountoulakis, Kang and Makai: with a random
  balanced colouring and `p ≥ λ n^(−1/2)`, the larger side wins in `O(1)` days.
* `theorem1_5`: with a biased random colouring, Red wins with probability `1 − o(1)`. As printed,
  the bias condition `p_r = 1/2 + ω((pn)⁻¹)` is too weak when `p ≫ n^(−1/2)`
  (`theorem1_5_printed_false`): with `p = 1` and `p_r = 1/2 + (log n)/n`, Blue has the majority
  with probability tending to `1/2`. The corrected statement (agreed with the user) asks for
  `p_r = 1/2 + ω(max{(pn)⁻¹, n^(−1/2)})`, which is what the paper's proof uses ("with probability
  `1 − o(1)`, `|R| > |B|`").

Both theorems are unlabelled in the paper; the labels `S:thm:delayed-FKM` and
`S:thm:biased-coloring` are the formalization's.

Both proofs follow the paper: a central limit or Chernoff estimate for the initial gap, then
Theorem 1.2 for each colouring with a large gap (conditioning on the colouring,
`colorAux_le_coloredProb`). Theorem 1.2 assumes `pn ≤ n − 10`, a restriction that the paper's
proofs overlook; for `pn > n − 10` the formalization uses a direct two-day argument
(`colorAux_nearComplete`, in `PowerOfFew/Sparse/ColoringAux.lean`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

namespace PowerOfFew.Sparse

/-- Corollary A.2 for the number `|R₀| ∼ Bin(n, 1/2)` of Red vertices of a random `1/2`
colouring: `|P(|R₀| − n/2 ≤ x) − Φ(2x/√n)| ≤ 0.56/√n` (here `σ = 1/2` and `1 − 2σ² = 1/2`). -/
private theorem colorAux_corollaryA_2_half (hBE : ShevtsovaBerryEsseen) {n : ℕ} (hn : 0 < n)
    (x : ℝ) :
    |(colorAux_law n (1 / 2)).real {χ | ∑ v, colorAux_red v χ - n / 2 ≤ x} -
      Φ (2 * x / Real.sqrt n)| ≤ 0.56 / Real.sqrt n := by
  have hX := colorAux_isBernoulliFamily (n := n) (q := 1 / 2) (by norm_num) (by norm_num)
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  have h := corollaryA_2 hBE (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hX
    (fun _ => 1) (fun _ => Or.inl rfl) hne x
  have hint : ∫ ω, ∑ i ∈ Finset.univ, (fun _ => (1 : ℝ)) i * colorAux_red i ω
      ∂(colorAux_law n (1 / 2)) = n / 2 := by
    simp only [one_mul]
    rw [integral_finsetSum _ (fun i _ => Integrable.of_finite)]
    simp only [hX.integral_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have hσ : Real.sqrt ((1 / 2 : ℝ) * (1 - 1 / 2)) = 1 / 2 := by
    rw [show (1 / 2 : ℝ) * (1 - 1 / 2) = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hint, hσ, Finset.card_univ, Fintype.card_fin] at h
  simp only [one_mul] at h
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have e1 : x / (1 / 2 * Real.sqrt n) = 2 * x / Real.sqrt n := by field_simp
  have e2 : (0.56 : ℝ) * (1 - 2 * (1 / 2 * (1 - 1 / 2))) / (1 / 2 * Real.sqrt n) =
      0.56 / Real.sqrt n := by
    field_simp; norm_num
  rw [e1, e2] at h
  exact h

/-- **Theorem 1.4** (`S:thm:delayed-FKM`). For every fixed `ε > 0` there is a constant `λ > 0`
such that, for majority dynamics on `G(n, p)` with `p ≥ λ n^(−1/2)` and a random `1/2` initial
colouring, the larger side wins in `O(1)` days with probability at least `1 − ε`.

Reading: `p ≥ λ n^(−1/2)` is written `λ ≤ p √n`; "wins in `O(1)` days" means within `T` days for
some `T` depending on `ε`; a tie (no larger side) counts as a failure.

Proof (the paper's): by Corollary A.2, the gap `Δ = ||R₀| − |B₀||/2` is at least `C_ε √n`
(`C_ε = ε/8`) with probability at least `1 − ε/2`. For such a colouring, Theorem 1.2 (with the
threshold constant `1`: `pn ≥ λ√n ≥ 2 log n`) makes the majority side win within
`K log n / log(pn) ≤ 2K` days (as `pn ≥ √n`), with failure probability
`O(1/min{n, pΔ²} + n^(−1/2)) ≤ O(1/(C_ε²λ²) + 1/λ)`, since `pΔ ≥ C_ε λ ≥ 10` and `n ≥ λ²`
(`p ≤ 1`). The paper takes `λ_ε = 10/C_ε` and lets `n → ∞`; here `λ` is also large enough that
`n ≥ λ²` makes these error terms at most `ε/2`. Blue majorities are handled by colour symmetry.

Departure from the paper: Theorem 1.2 assumes `pn ≤ n − 10`. When `pn > n − 10` (which the paper's
proof does not treat), the majority side, ahead by `2Δ ≥ 2C_ε λ` vertices, wins within two days
with probability at least `1 − 40/(2C_ε λ − 1) − 2048/n` (`colorAux_nearComplete`). -/
theorem theorem1_4 (hBE : ShevtsovaBerryEsseen)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ T : ℕ, ∀ (n : ℕ) (p : ℝ), lam ≤ p * Real.sqrt n → p ≤ 1 →
      1 - ε ≤ coloredProb n p (1 / 2) (fun G B₀ =>
        ((B₀.ncard : ℝ) < n / 2 ∧ blueAfter G B₀ T = ∅) ∨
          ((n : ℝ) / 2 < B₀.ncard ∧ blueAfter G B₀ T = Set.univ)) := by
  -- it suffices to treat `ε ≤ 1`
  wlog hε1 : ε ≤ 1 generalizing ε
  · obtain ⟨lam, hlam, T, h⟩ := this one_pos le_rfl
    exact ⟨lam, hlam, T, fun n p h1 h2 => le_trans (by linarith) (h n p h1 h2)⟩
  -- Theorem 1.2, with the threshold constant `1` (`pn ≥ λ√n ≥ 2 log n`)
  obtain ⟨C, K, hmain⟩ := theorem1_2 hBE (lam := 1) one_pos
  set C' := max C 1 with hC'
  -- the gap constant `C_ε` of the paper
  set c' : ℝ := ε / 8 with hc'
  have hc'0 : 0 < c' := by positivity
  have hc'1 : c' ≤ 1 := by rw [hc']; linarith
  -- the number of days: `K log n / log(pn) ≤ 2K`, and two days in the near-complete case
  set T : ℕ := max ⌈2 * max K 0⌉₊ 2 with hT
  -- choose `λ` large
  have hT1 : Tendsto (fun L : ℝ => C' * (1 / (c' ^ 2 * L ^ 2) + 1 / L)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun L : ℝ => c' ^ 2 * L ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).const_mul_atTop (by positivity)
    have := ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop h1).add
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_id)
    simpa using this.const_mul C'
  have hT2 : Tendsto (fun L : ℝ => 40 / (2 * c' * L - 1) + 2048 / L ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun L : ℝ => 2 * c' * L - 1) atTop atTop := by
      have := tendsto_atTop_add_const_right atTop (-1)
        (tendsto_id.const_mul_atTop (by positivity : 0 < 2 * c'))
      simpa [sub_eq_add_neg] using this
    have := ((tendsto_const_nhds (x := (40 : ℝ))).div_atTop h1).add
      ((tendsto_const_nhds (x := (2048 : ℝ))).div_atTop (tendsto_pow_atTop two_ne_zero))
    simpa using this
  have hT3 : Tendsto (fun L : ℝ => 1.12 / L) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (1.12 : ℝ))).div_atTop tendsto_id
  obtain ⟨lam, hlam44, hlamc, hlam1, hlam2, hlam3, hlam4⟩ := ((eventually_ge_atTop 44).and
    ((eventually_ge_atTop (10 / c')).and (((tendsto_order.1 hT1).2 (ε / 2) (by positivity)).and
    (((tendsto_order.1 hT2).2 (ε / 2) (by positivity)).and
    (((tendsto_order.1 hT3).2 (ε / 4) (by positivity)).and
    (eventually_ge_atTop (1 / c'))))))).exists
  have hc'lam : 10 ≤ c' * lam := by rwa [div_le_iff₀ hc'0, mul_comm] at hlamc
  have hc'lam1 : 1 ≤ c' * lam := by rwa [div_le_iff₀ hc'0, mul_comm] at hlam4
  refine ⟨lam, by linarith, T, fun n p hlam hp1 => ?_⟩
  have hsqrt0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hp0 : 0 < p := by
    by_contra h
    push Not at h
    have : p * Real.sqrt n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hsqrt0
    linarith
  have hlamsqrt : lam ≤ Real.sqrt n :=
    hlam.trans (mul_le_of_le_one_left hsqrt0 hp1)
  have hsqrt : 0 < Real.sqrt n := by linarith
  have hnR : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hsqrt
    · exact_mod_cast h
  have hn : 0 < n := by exact_mod_cast hnR
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnR.le
  have hnlam : lam ^ 2 ≤ n := by
    rw [← hsq, sq]; exact mul_le_mul hlamsqrt hlamsqrt (by linarith) hsqrt0
  have hn44 : 44 ≤ n := by exact_mod_cast (show (44 : ℝ) ≤ n by nlinarith)
  -- `pn = (p√n)√n ≥ λ√n`
  have hpn : lam * Real.sqrt n ≤ p * n := by
    have := mul_le_mul_of_nonneg_right hlam hsqrt0
    rw [mul_assoc, hsq] at this
    exact this
  have hlog : (1 + 1) * Real.log n ≤ p * n := by
    have := Real.log_natCast_le_two_mul_sqrt n
    have : 4 * Real.sqrt n ≤ lam * Real.sqrt n := mul_le_mul_of_nonneg_right (by linarith) hsqrt0
    linarith
  -- if Red leads by `c'√n`, it wins within `T` days with probability `1 − ε/2`
  have hside : ∀ B : Set (Fin n), c' * Real.sqrt n ≤ (n : ℝ) / 2 - B.ncard →
      1 - ε / 2 ≤ gnpProb n p (fun G => blueAfter G B T = ∅) := by
    intro B hB
    set Δ : ℝ := (n : ℝ) / 2 - B.ncard with hΔ
    have hΔ0 : c' * lam ≤ Δ := le_trans (mul_le_mul_of_nonneg_left hlamsqrt hc'0.le) hB
    have hpΔ : c' * lam ≤ p * Δ :=
      calc c' * lam ≤ c' * (p * Real.sqrt n) := mul_le_mul_of_nonneg_left hlam hc'0.le
        _ = p * (c' * Real.sqrt n) := by ring
        _ ≤ p * Δ := mul_le_mul_of_nonneg_left hB hp0.le
    by_cases hnear : p * n ≤ (n : ℝ) - 10
    · -- Theorem 1.2 (`pΔ ≥ c'λ ≥ 10`)
      have h := hmain n p B hp0 hnear hlog (by rw [← hΔ]; linarith)
      -- the time bound `K log n / log(pn) ≤ T`, since `pn ≥ √n`
      have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hsqrtpn : Real.sqrt n ≤ p * n :=
        le_trans (le_mul_of_one_le_left hsqrt0 (by linarith)) hpn
      have hlogpn : Real.log n / 2 ≤ Real.log (p * n) := by
        have := Real.log_le_log hsqrt hsqrtpn
        rwa [Real.log_sqrt hnR.le] at this
      have hr0 : 0 ≤ Real.log n / Real.log (p * n) := div_nonneg hlogn.le (by linarith)
      have hr2 : Real.log n / Real.log (p * n) ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have htime : ∀ t : ℕ, (t : ℝ) ≤ K * (Real.log n / Real.log (p * n)) → t ≤ T := by
        intro t ht
        have h1 : (t : ℝ) ≤ 2 * max K 0 := by
          calc (t : ℝ) ≤ K * (Real.log n / Real.log (p * n)) := ht
            _ ≤ max K 0 * (Real.log n / Real.log (p * n)) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) hr0
            _ ≤ max K 0 * 2 := mul_le_mul_of_nonneg_left hr2 (le_max_right _ _)
            _ = 2 * max K 0 := by ring
        have h2 : t ≤ ⌈2 * max K 0⌉₊ := by exact_mod_cast h1.trans (Nat.le_ceil _)
        exact h2.trans (le_max_left _ _)
      -- the failure probability: `min{n, pΔ²} ≥ c'²λ²` and `n^(−1/2) ≤ 1/λ`
      have hmin : c' ^ 2 * lam ^ 2 ≤ min (n : ℝ) (p * Δ ^ 2) := by
        refine le_min ?_ ?_
        · have : c' ^ 2 ≤ 1 := pow_le_one₀ hc'0.le hc'1
          calc c' ^ 2 * lam ^ 2 ≤ 1 * lam ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg _)
            _ ≤ n := by linarith
        · calc c' ^ 2 * lam ^ 2 = (c' * lam) * (c' * lam) := by ring
            _ ≤ (p * Δ) * Δ := mul_le_mul hpΔ hΔ0 (by positivity) (by linarith)
            _ = p * Δ ^ 2 := by ring
      have hrpow : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / lam := by
        rw [Real.rpow_neg hnR.le, ← Real.sqrt_eq_rpow, ← one_div]
        exact one_div_le_one_div_of_le (by linarith) hlamsqrt
      have hfail : C * (1 / min (n : ℝ) (p * Δ ^ 2) + (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ ε / 2 := by
        have hmin0 : 0 < min (n : ℝ) (p * Δ ^ 2) := lt_of_lt_of_le (by positivity) hmin
        have hpos : 0 ≤ 1 / min (n : ℝ) (p * Δ ^ 2) + (n : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
        calc C * (1 / min (n : ℝ) (p * Δ ^ 2) + (n : ℝ) ^ (-(1 / 2 : ℝ)))
            ≤ C' * (1 / min (n : ℝ) (p * Δ ^ 2) + (n : ℝ) ^ (-(1 / 2 : ℝ))) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
          _ ≤ C' * (1 / (c' ^ 2 * lam ^ 2) + 1 / lam) := by
              refine mul_le_mul_of_nonneg_left (add_le_add ?_ hrpow) (by positivity)
              exact one_div_le_one_div_of_le (by positivity) hmin
          _ ≤ ε / 2 := hlam1.le
      calc 1 - ε / 2 ≤ 1 - C * (1 / min (n : ℝ) (p * Δ ^ 2) + (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
            linarith
        _ ≤ _ := h
        _ ≤ _ := gnpProb_mono fun G ⟨t, ht, hG⟩ => blueAfter_eq_empty_of_le G hG (htime t ht)
    · -- the near-complete case: Red leads by `2Δ ≥ 2c'λ` vertices
      push Not at hnear
      have hm : 1 < 2 * c' * lam := by linarith
      have h := colorAux_nearComplete hn44 hp1 hnear (m := 2 * c' * lam) hm (by linarith)
      have hn2048 : 2048 / (n : ℝ) ≤ 2048 / lam ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hnlam
      calc 1 - ε / 2 ≤ 1 - (40 / (2 * c' * lam - 1) + 2048 / n) := by linarith
        _ ≤ gnpProb n p (fun G => blueAfter G B 2 = ∅) := h
        _ ≤ _ := gnpProb_mono fun G hG => blueAfter_eq_empty_of_le G hG (le_max_right _ _)
  -- the majority side wins when the gap is at least `c'√n`
  have hgood : ∀ B₀ : Set (Fin n), c' * Real.sqrt n ≤ |(n : ℝ) / 2 - B₀.ncard| →
      1 - ε / 2 ≤ gnpProb n p (fun G =>
        ((B₀.ncard : ℝ) < n / 2 ∧ blueAfter G B₀ T = ∅) ∨
          ((n : ℝ) / 2 < B₀.ncard ∧ blueAfter G B₀ T = Set.univ)) := by
    intro B₀ hB
    have hpos : 0 < c' * Real.sqrt n := by positivity
    rcases le_or_gt (B₀.ncard : ℝ) (n / 2) with h | h
    · rw [abs_of_nonneg (by linarith)] at hB
      exact (hside B₀ hB).trans (gnpProb_mono fun G hG => Or.inl ⟨by linarith, hG⟩)
    · rw [abs_of_neg (by linarith)] at hB
      have hBc : c' * Real.sqrt n ≤ (n : ℝ) / 2 - (B₀ᶜ).ncard := by
        rw [colorAux_ncard_compl]; linarith
      exact (hside B₀ᶜ hBc).trans
        (gnpProb_mono fun G hG => Or.inr ⟨h, colorAux_blueAfter_eq_univ hG⟩)
  -- by Corollary A.2, the gap is at least `c'√n` with probability at least `1 − ε/2`
  have hcol : 1 - ε / 2 ≤ coloredProb n p (1 / 2) (fun _ B₀ =>
      c' * Real.sqrt n ≤ |(n : ℝ) / 2 - B₀.ncard|) := by
    rw [colorAux_coloredProb_gap]
    have hgap := colorAux_gap_le hn hc'0.le (colorAux_corollaryA_2_half hBE hn)
    have hpi : 2 ≤ Real.sqrt (2 * Real.pi) :=
      (Real.le_sqrt' two_pos).mpr (by nlinarith [Real.pi_gt_three])
    have h1 : 4 * c' / Real.sqrt (2 * Real.pi) ≤ ε / 4 := by
      rw [div_le_iff₀ (by linarith), hc']
      nlinarith
    have h2 : 2 * (0.56 / Real.sqrt n) ≤ ε / 4 := by
      have : 1.12 / Real.sqrt n ≤ 1.12 / lam :=
        div_le_div_of_nonneg_left (by norm_num) (by linarith) hlamsqrt
      have e : 2 * (0.56 / Real.sqrt n) = 1.12 / Real.sqrt n := by ring
      linarith
    linarith
  have := colorAux_le_coloredProb (by norm_num) (by norm_num) hgood hcol (by linarith)
    (by linarith)
  linarith

/-- **Theorem 1.5** (`S:thm:biased-coloring`), corrected. On `G(n, p)` with
`p ≥ (1 + λ) n⁻¹ log n` for a constant `λ > 0`, majority dynamics from a random colouring in which
each vertex is Red with probability `p_r = 1/2 + ω(max{(pn)⁻¹, n^(−1/2)})` ends in a Red unanimity
with probability `1 − o(1)`.

Correction: the paper asks only for `p_r = 1/2 + ω((pn)⁻¹)`, which is false
(`theorem1_5_printed_false`). Here `p = p n` and `p_r = q n` are sequences, and
`p ≥ (1 + λ) n⁻¹ log n` is required for large `n` only (required for every `n`, it would be
unsatisfiable at `n = 3` when `λ > 3/log 3 − 1`).

Proof (the paper's): write `δ = p_r − 1/2` and `g = δ min{pn, √n} → ∞`. By the Chernoff bound for
`|R₀| ∼ Bin(n, p_r)`, `Δ = |R₀| − n/2 ≥ δn/2` with probability at least `1 − exp(−g²/8)`. For such
a colouring `pΔ ≥ g/2 ≥ 10` and `pΔ² ≥ g²/4`, so Theorem 1.2 gives a Red unanimity with failure
probability `O(1/min{n, pΔ²} + n^(−λ/2)) = o(1)` (the paper writes `O((pΔ²)⁻¹)`, leaving out the
two terms that tend to `0` with `n`).

Departure from the paper: Theorem 1.2 assumes `pn ≤ n − 10`. When `pn > n − 10` (which the paper's
proof does not treat), Red, ahead by `2Δ ≥ δn ≥ g` vertices, wins within two days with probability
at least `1 − 40/(g − 1) − 2048/n` (`colorAux_nearComplete`). -/
theorem theorem1_5 (hBE : ShevtsovaBerryEsseen)
    {lam : ℝ} (hlam : 0 < lam) {p q : ℕ → ℝ} (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n ≤ 1)
    (hlog : ∀ᶠ n : ℕ in atTop, (1 + lam) * Real.log n / n ≤ p n) (hq : ∀ n, q n ≤ 1)
    (hbias : Tendsto (fun n : ℕ => (q n - 1 / 2) * min (p n * n) (Real.sqrt n)) atTop atTop) :
    Tendsto (fun n : ℕ =>
      coloredProb n (p n) (q n) (fun G B₀ => ∃ t, blueAfter G B₀ t = ∅)) atTop (𝓝 1) := by
  obtain ⟨C, K, hmain⟩ := theorem1_2 hBE hlam
  set C' := max C 1 with hC'
  -- `g n = (q n − 1/2) min{pn, √n} → ∞`
  set g : ℕ → ℝ := fun n => (q n - 1 / 2) * min (p n * n) (Real.sqrt n) with hg
  -- the failure bound: Theorem 1.2 or the near-complete case, and the Chernoff bound for `|R₀|`
  set F : ℕ → ℝ := fun n => C' * (1 / (n : ℝ) + 4 / g n ^ 2 + (n : ℝ) ^ (-(lam / 2))) +
      (40 / (g n - 1) + 2048 / n) + Real.exp (-(g n ^ 2 / 8)) with hF
  have hFlim : Tendsto F atTop (𝓝 0) := by
    have hg2 : Tendsto (fun n => g n ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp hbias
    have hg1 : Tendsto (fun n => g n - 1) atTop atTop := by
      have := tendsto_atTop_add_const_right atTop (-1) hbias
      simpa [sub_eq_add_neg] using this
    have t1 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have t2 : Tendsto (fun n => 4 / g n ^ 2) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := (4 : ℝ))).div_atTop hg2
    have t3 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(lam / 2))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    have t4 : Tendsto (fun n => 40 / (g n - 1)) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := (40 : ℝ))).div_atTop hg1
    have t5 : Tendsto (fun n : ℕ => 2048 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 2048
    have t6 : Tendsto (fun n => Real.exp (-(g n ^ 2 / 8))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (hg2.atTop_div_const (by norm_num))
    have := ((((t1.add t2).add t3).const_mul C').add (t4.add t5)).add t6
    rw [show (0 : ℝ) = C' * (0 + 0 + 0) + (0 + 0) + 0 by ring]
    exact this
  have hlower : ∀ᶠ n in atTop, 1 - F n ≤
      coloredProb n (p n) (q n) (fun G B₀ => ∃ t, blueAfter G B₀ t = ∅) := by
    filter_upwards [eventually_ge_atTop 44, hbias.eventually_ge_atTop 20, hlog]
      with n hn44 hg20 hlogn
    have hnR : (44 : ℝ) ≤ n := by exact_mod_cast hn44
    have hnpos : (0 : ℝ) < n := by linarith
    have hpn := hp0 n
    set δ := q n - 1 / 2 with hδ
    set M := min (p n * n) (Real.sqrt n) with hM
    have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hM0 : 0 < M := lt_min (by positivity) hsqrt
    have hgdef : g n = δ * M := rfl
    have hδ0 : 0 < δ := by
      by_contra h
      push Not at h
      have : δ * M ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hM0.le
      linarith
    have hq0 : 0 ≤ q n := by linarith
    have hMpn : M ≤ p n * n := min_le_left _ _
    have hMsq : M ≤ Real.sqrt n := min_le_right _ _
    have hsqn : Real.sqrt n ≤ n := by
      have h1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by linarith)
      calc Real.sqrt n = Real.sqrt n * 1 := (mul_one _).symm
        _ ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left h1 hsqrt.le
        _ = n := Real.mul_self_sqrt hnpos.le
    -- `δpn ≥ g`, `δ√n ≥ g` and `δn ≥ g`
    have hδpn : g n ≤ δ * (p n * n) := mul_le_mul_of_nonneg_left hMpn hδ0.le
    have hδsq : g n ≤ δ * Real.sqrt n := mul_le_mul_of_nonneg_left hMsq hδ0.le
    have hδn : g n ≤ δ * n := hδsq.trans (mul_le_mul_of_nonneg_left hsqn hδ0.le)
    have hA : 0 ≤ C' * (1 / (n : ℝ) + 4 / g n ^ 2 + (n : ℝ) ^ (-(lam / 2))) := by
      have : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
      positivity
    have hB' : 0 ≤ 40 / (g n - 1) + 2048 / n := by
      have : 0 < g n - 1 := by linarith
      positivity
    -- a colouring with gap `Δ ≥ δn/2` wins: `pΔ ≥ g/2 ≥ 10` and `pΔ² ≥ g²/4`
    have hgood : ∀ B : Set (Fin n), δ * n / 2 ≤ (n : ℝ) / 2 - B.ncard →
        1 - (C' * (1 / (n : ℝ) + 4 / g n ^ 2 + (n : ℝ) ^ (-(lam / 2))) +
          (40 / (g n - 1) + 2048 / n)) ≤
          gnpProb n (p n) (fun G => ∃ t, blueAfter G B t = ∅) := by
      intro B hB
      set Δ : ℝ := (n : ℝ) / 2 - B.ncard with hΔ
      have hΔg : g n / 2 ≤ Δ := by linarith
      have hΔpos : 0 < Δ := by linarith
      have hpΔ : g n / 2 ≤ p n * Δ :=
        calc g n / 2 ≤ δ * (p n * n) / 2 := by linarith
          _ = p n * (δ * n / 2) := by ring
          _ ≤ p n * Δ := mul_le_mul_of_nonneg_left hB hpn.le
      have hpΔ2 : g n ^ 2 / 4 ≤ p n * Δ ^ 2 :=
        calc g n ^ 2 / 4 = (g n / 2) * (g n / 2) := by ring
          _ ≤ (p n * Δ) * Δ := mul_le_mul hpΔ hΔg (by linarith) (by positivity)
          _ = p n * Δ ^ 2 := by ring
      by_cases hnear : p n * n ≤ (n : ℝ) - 10
      · -- Theorem 1.2
        have hlog' : (1 + lam) * Real.log n ≤ p n * n := by rwa [div_le_iff₀ hnpos] at hlogn
        have h := hmain n (p n) B hpn hnear hlog' (by rw [← hΔ]; linarith)
        have hpΔ2pos : 0 < p n * Δ ^ 2 := mul_pos hpn (pow_pos hΔpos 2)
        have hmin : 1 / min (n : ℝ) (p n * Δ ^ 2) ≤ 1 / (n : ℝ) + 4 / g n ^ 2 := by
          have h4 : 0 ≤ 4 / g n ^ 2 := by positivity
          have h1n : 0 ≤ 1 / (n : ℝ) := by positivity
          rcases min_choice (n : ℝ) (p n * Δ ^ 2) with hm | hm
          · rw [hm]; linarith
          · rw [hm]
            have : 1 / (p n * Δ ^ 2) ≤ 4 / g n ^ 2 := by
              rw [div_le_div_iff₀ hpΔ2pos (by positivity)]; linarith
            linarith
        have hfail : C * (1 / min (n : ℝ) (p n * Δ ^ 2) + (n : ℝ) ^ (-(lam / 2))) ≤
            C' * (1 / (n : ℝ) + 4 / g n ^ 2 + (n : ℝ) ^ (-(lam / 2))) := by
          have hmin0 : 0 < min (n : ℝ) (p n * Δ ^ 2) := lt_min hnpos hpΔ2pos
          have hpos : 0 ≤ 1 / min (n : ℝ) (p n * Δ ^ 2) + (n : ℝ) ^ (-(lam / 2)) := by
            positivity
          calc C * (1 / min (n : ℝ) (p n * Δ ^ 2) + (n : ℝ) ^ (-(lam / 2)))
              ≤ C' * (1 / min (n : ℝ) (p n * Δ ^ 2) + (n : ℝ) ^ (-(lam / 2))) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
            _ ≤ C' * (1 / (n : ℝ) + 4 / g n ^ 2 + (n : ℝ) ^ (-(lam / 2))) :=
                mul_le_mul_of_nonneg_left (by linarith)
                  (lt_of_lt_of_le one_pos (le_max_right _ _)).le
        calc 1 - (C' * (1 / (n : ℝ) + 4 / g n ^ 2 + (n : ℝ) ^ (-(lam / 2))) +
              (40 / (g n - 1) + 2048 / n))
            ≤ 1 - C * (1 / min (n : ℝ) (p n * Δ ^ 2) + (n : ℝ) ^ (-(lam / 2))) := by linarith
          _ ≤ _ := h
          _ ≤ _ := gnpProb_mono fun G ⟨t, _, ht⟩ => ⟨t, ht⟩
      · -- the near-complete case: Red leads by `2Δ ≥ δn ≥ g` vertices
        push Not at hnear
        have h := colorAux_nearComplete hn44 (hp1 n) hnear (m := g n) (by linarith)
          (by linarith)
        calc 1 - (C' * (1 / (n : ℝ) + 4 / g n ^ 2 + (n : ℝ) ^ (-(lam / 2))) +
              (40 / (g n - 1) + 2048 / n))
            ≤ 1 - (40 / (g n - 1) + 2048 / n) := by linarith
          _ ≤ _ := h
          _ ≤ _ := gnpProb_mono fun G hG => ⟨2, hG⟩
    -- by Chernoff's bound, `Δ ≥ δn/2` with probability at least `1 − exp(−g²/8)`
    have hcol : 1 - Real.exp (-(g n ^ 2 / 8)) ≤ coloredProb n (p n) (q n)
        (fun _ B₀ => δ * n / 2 ≤ (n : ℝ) / 2 - B₀.ncard) := by
      rw [colorAux_coloredProb_color]
      have hX := colorAux_isBernoulliFamily (n := n) hq0 (hq n)
      set T : ℝ := q n * n - δ * n / 2 with hT
      have hTlt : T < q n * (Finset.univ : Finset (Fin n)).card := by
        rw [Finset.card_univ, Fintype.card_fin, hT]
        have : 0 < δ * n / 2 := by positivity
        linarith
      have hch := hX.measureReal_sum_le_le_exp hq0 (hq n) Finset.univ hTlt
      rw [Finset.card_univ, Fintype.card_fin] at hch
      have hsub : {χ : Fin n → Bool |
          δ * n / 2 ≤ (n : ℝ) / 2 - (({v | χ v = false} : Set (Fin n)).ncard : ℝ)}ᶜ ⊆
          {ω | ∑ i ∈ Finset.univ, colorAux_red i ω ≤ T} := by
        intro χ hχ
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, colorAux_ncard_blue] at hχ ⊢
        have hqn : q n * n = δ * n + n / 2 := by rw [hδ]; ring
        rw [hT]
        linarith
      have hg0 : 0 ≤ g n := by linarith
      have hg2 : g n ^ 2 ≤ δ ^ 2 * n :=
        calc g n ^ 2 ≤ (δ * Real.sqrt n) ^ 2 := pow_le_pow_left₀ hg0 hδsq 2
          _ = δ ^ 2 * n := by rw [mul_pow, Real.sq_sqrt hnpos.le]
      have hexp : Real.exp (-((q n * n - T) ^ 2 / (2 * (q n * n)))) ≤
          Real.exp (-(g n ^ 2 / 8)) := by
        rw [Real.exp_le_exp, neg_le_neg_iff]
        have hqn : 0 < q n * n := by
          have : 0 < q n := by linarith
          positivity
        rw [le_div_iff₀ (by positivity)]
        calc g n ^ 2 / 8 * (2 * (q n * n)) = g n ^ 2 * (q n * n) / 4 := by ring
          _ ≤ (δ ^ 2 * n) * (q n * n) / 4 := by gcongr
          _ ≤ (δ ^ 2 * n) * (1 * n) / 4 := by gcongr; exact hq n
          _ = (q n * n - T) ^ 2 := by rw [hT]; ring
      have hc := measureReal_compl (μ := colorAux_law n (q n)) (s := {χ : Fin n → Bool |
          δ * n / 2 ≤ (n : ℝ) / 2 - (({v | χ v = false} : Set (Fin n)).ncard : ℝ)})
        MeasurableSet.of_discrete
      rw [probReal_univ] at hc
      have hm := measureReal_mono (μ := colorAux_law n (q n)) hsub
      linarith
    have := colorAux_le_coloredProb hq0 (hq n) hgood hcol (by linarith) (Real.exp_pos _).le
    simp only [hF]
    linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun n => 1 - F n) (h := fun _ => 1) ?_
    tendsto_const_nhds hlower (Eventually.of_forall fun n => colorAux_coloredProb_le_one _)
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hFlim

/-- `P(|R₀| = k) = C(n, k)/2ⁿ < 1/√n` for the random `1/2` colouring (by the dense paper's
Lemma 3.2). -/
private theorem colorAux_law_half_point {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    (colorAux_law n (1 / 2)).real {χ | ∑ v, colorAux_red v χ = k} < 1 / Real.sqrt n := by
  have hX := colorAux_isBernoulliFamily (n := n) (q := 1 / 2) (by norm_num) (by norm_num)
  have h := hX.measureReal_sum_eq Finset.univ k
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [h]
  have e : (1 / 2 : ℝ) ^ k * (1 - 1 / 2) ^ (n - k) = (1 / 2) ^ n := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← pow_add, Nat.add_sub_cancel' hk]
  rw [mul_assoc, e]
  have h3 := Dense.lemma3_2 hn hk
  calc (n.choose k : ℝ) * (1 / 2) ^ n < 2 ^ n / Real.sqrt n * (1 / 2) ^ n :=
        mul_lt_mul_of_pos_right h3 (by positivity)
    _ = 1 / Real.sqrt n := by
        rw [div_mul_eq_mul_div, ← mul_pow]; norm_num

/-- The window `n/2 − 2√n < |R₀| ≤ n/2 − 1` has probability at least `1/4` under the random `1/2`
colouring, for `n ≥ 64`: by symmetry `P(|R₀| ≤ n/2 − 1) = P(|R₀| ≥ n/2 + 1)`, the at most two
values in between have probability less than `1/√n` each, and Chernoff's bound gives
`P(|R₀| ≤ n/2 − 2√n) ≤ e⁻⁴`. -/
private theorem colorAux_window_ge {n : ℕ} (hn : 64 ≤ n) :
    1 / 4 ≤ (colorAux_law n (1 / 2)).real {χ |
      (n : ℝ) / 2 - 2 * Real.sqrt n < n - (({v | χ v = false} : Set (Fin n)).ncard : ℝ) ∧
        (n : ℝ) - (({v | χ v = false} : Set (Fin n)).ncard : ℝ) ≤ n / 2 - 1} := by
  set μ := colorAux_law n (1 / 2)
  have hnR : (64 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsqrt8 : 8 ≤ Real.sqrt n := (Real.le_sqrt' (by norm_num)).mpr (by linarith)
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
  set X : (Fin n → Bool) → ℝ := fun χ => ∑ v, colorAux_red v χ with hX_def
  have hB : ∀ χ : Fin n → Bool,
      ((({v | χ v = false} : Set (Fin n)).ncard : ℝ)) = n - X χ := colorAux_ncard_blue
  have hset : {χ : Fin n → Bool |
      (n : ℝ) / 2 - 2 * Real.sqrt n < n - (({v | χ v = false} : Set (Fin n)).ncard : ℝ) ∧
        (n : ℝ) - (({v | χ v = false} : Set (Fin n)).ncard : ℝ) ≤ n / 2 - 1} =
      {χ | X χ ≤ n / 2 - 1} \ {χ | X χ ≤ n / 2 - 2 * Real.sqrt n} := by
    ext χ
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_le, hB]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  have hsub : {χ | X χ ≤ n / 2 - 2 * Real.sqrt n} ⊆ {χ | X χ ≤ n / 2 - 1} := fun χ hχ => by
    simp only [Set.mem_ofPred_eq] at hχ ⊢; linarith
  rw [hset, measureReal_sdiff hsub MeasurableSet.of_discrete]
  -- Chernoff: `P(X ≤ n/2 − 2√n) ≤ e⁻⁴ ≤ 1/8`
  have hX := colorAux_isBernoulliFamily (n := n) (q := 1 / 2) (by norm_num) (by norm_num)
  have hch := hX.measureReal_sum_le_le_exp (by norm_num) (by norm_num) Finset.univ
    (T := n / 2 - 2 * Real.sqrt n) (by rw [Finset.card_univ, Fintype.card_fin]; linarith)
  rw [Finset.card_univ, Fintype.card_fin] at hch
  have he : Real.exp (-((1 / 2 * (n : ℝ) - (n / 2 - 2 * Real.sqrt n)) ^ 2 /
      (2 * (1 / 2 * n)))) = Real.exp (-4) := by
    congr 1
    field_simp
    nlinarith [hsq]
  rw [he] at hch
  have he4 : Real.exp (-4) ≤ 1 / 8 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have := Real.quadratic_le_exp_of_nonneg (x := 4) (by norm_num)
    linarith
  -- symmetry and the middle values: `P(X ≤ n/2 − 1) ≥ 1/2 − 1/√n`
  have hA : 1 / 2 - 1 / Real.sqrt n ≤ μ.real {χ | X χ ≤ n / 2 - 1} := by
    have hsym : μ.real {χ | X χ ≤ n / 2 - 1} = μ.real {χ | n / 2 + 1 ≤ X χ} := by
      have h1 : {χ : Fin n → Bool | X χ ≤ n / 2 - 1} =
          {χ | (n : ℝ) / 2 + 1 ≤ (({v | χ v = false} : Set (Fin n)).ncard : ℝ)} := by
        ext χ; simp only [Set.mem_ofPred_eq, hB]; constructor <;> intro h <;> linarith
      have h2 : {χ : Fin n → Bool | (n : ℝ) / 2 + 1 ≤ X χ} =
          {χ | (n : ℝ) / 2 + 1 ≤ ((({v | χ v = false} : Set (Fin n))ᶜ).ncard : ℝ)} := by
        ext χ; simp only [Set.mem_ofPred_eq, colorAux_ncard_compl, hB]
        constructor <;> intro h <;> linarith
      rw [h1, h2, colorAux_law_half_compl (fun B => (n : ℝ) / 2 + 1 ≤ (B.ncard : ℝ))]
    have hmid : μ.real {χ | n / 2 - 1 < X χ ∧ X χ < n / 2 + 1} ≤ 2 / Real.sqrt n := by
      have hsub : {χ : Fin n → Bool | n / 2 - 1 < X χ ∧ X χ < n / 2 + 1} ⊆
          {χ | X χ = ((n / 2 : ℕ) : ℝ)} ∪ {χ | X χ = ((n / 2 + 1 : ℕ) : ℝ)} := by
        intro χ ⟨h1, h2⟩
        have hk : X χ = ((Finset.univ.filter (fun v => χ v = true)).card : ℝ) :=
          colorAux_sum_red χ
        set k := (Finset.univ.filter (fun v => χ v = true)).card
        simp only [Set.mem_union, Set.mem_ofPred_eq]
        rw [hk] at h1 h2 ⊢
        have h1' : n < 2 * k + 2 := by
          have : (n : ℝ) < 2 * k + 2 := by linarith
          exact_mod_cast this
        have h2' : 2 * k < n + 2 := by
          have : (2 * k : ℝ) < n + 2 := by linarith
          exact_mod_cast this
        have : k = n / 2 ∨ k = n / 2 + 1 := by omega
        rcases this with h | h
        · left; rw [h]
        · right; rw [h]
      have hp1 := colorAux_law_half_point (n := n) (k := n / 2) (by omega) (by omega)
      have hp2 := colorAux_law_half_point (n := n) (k := n / 2 + 1) (by omega) (by omega)
      calc μ.real {χ | n / 2 - 1 < X χ ∧ X χ < n / 2 + 1}
          ≤ μ.real ({χ | X χ = ((n / 2 : ℕ) : ℝ)} ∪ {χ | X χ = ((n / 2 + 1 : ℕ) : ℝ)}) :=
            measureReal_mono hsub
        _ ≤ μ.real {χ | X χ = ((n / 2 : ℕ) : ℝ)} + μ.real {χ | X χ = ((n / 2 + 1 : ℕ) : ℝ)} :=
            measureReal_union_le _ _
        _ ≤ 2 / Real.sqrt n := by
            have : 1 / Real.sqrt n + 1 / Real.sqrt n = 2 / Real.sqrt n := by ring
            linarith
    have hcover : (1 : ℝ) ≤ μ.real {χ | X χ ≤ n / 2 - 1} + μ.real {χ | n / 2 + 1 ≤ X χ} +
        μ.real {χ | n / 2 - 1 < X χ ∧ X χ < n / 2 + 1} := by
      have hU : (Set.univ : Set (Fin n → Bool)) ⊆ ({χ | X χ ≤ n / 2 - 1} ∪
          {χ | n / 2 + 1 ≤ X χ}) ∪ {χ | n / 2 - 1 < X χ ∧ X χ < n / 2 + 1} := by
        intro χ _
        by_cases h1 : X χ ≤ n / 2 - 1
        · exact Or.inl (Or.inl h1)
        · by_cases h2 : n / 2 + 1 ≤ X χ
          · exact Or.inl (Or.inr h2)
          · exact Or.inr ⟨by linarith, by linarith⟩
      calc (1 : ℝ) = μ.real Set.univ := probReal_univ.symm
        _ ≤ μ.real (({χ | X χ ≤ n / 2 - 1} ∪ {χ | n / 2 + 1 ≤ X χ}) ∪
            {χ | n / 2 - 1 < X χ ∧ X χ < n / 2 + 1}) := measureReal_mono hU
        _ ≤ μ.real ({χ | X χ ≤ n / 2 - 1} ∪ {χ | n / 2 + 1 ≤ X χ}) +
            μ.real {χ | n / 2 - 1 < X χ ∧ X χ < n / 2 + 1} := measureReal_union_le _ _
        _ ≤ _ := by gcongr; exact measureReal_union_le _ _
    have : 1 / Real.sqrt n + 1 / Real.sqrt n = 2 / Real.sqrt n := by ring
    linarith
  have h18 : 1 / Real.sqrt n ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hsqrt8
  have : μ.real {χ | X χ ≤ n / 2 - 2 * Real.sqrt n} ≤ 1 / 8 := hch.trans he4
  linarith

/-- The change of measure from `p_r = 1/2` to `p_r = 1/2 + δ` on the window: a colouring with
`r ≤ n/2 − 1` Red and `b = n − r` Blue vertices, `r > n/2 − 2√n`, has weight
`(1/2 + δ)^r (1/2 − δ)^b = 2⁻ⁿ (1 − 4δ²)^r (1 − 2δ)^(b − r) ≥ 2⁻ⁿ (1 − 4δ²n)(1 − 8δ√n)`
(Bernoulli's inequality), which is at least `2⁻ⁿ/2` when `4δ²n + 8δ√n ≤ 1/2`. -/
private theorem colorAux_weight_ge {n r b : ℕ} (hrb : r + b = n) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2) (hr1 : (r : ℝ) ≤ n / 2 - 1) (hr2 : (n : ℝ) / 2 - 2 * Real.sqrt n < r)
    (hsmall : 4 * δ ^ 2 * n + 8 * δ * Real.sqrt n ≤ 1 / 2) :
    1 / 2 * (1 / 2) ^ n ≤ (1 / 2 + δ) ^ r * (1 - (1 / 2 + δ)) ^ b := by
  have hrbR : (r : ℝ) + b = n := by exact_mod_cast hrb
  have hrb' : r ≤ b := by
    have : (r : ℝ) ≤ b := by linarith
    exact_mod_cast this
  obtain ⟨j, rfl⟩ : ∃ j, b = r + j := ⟨b - r, by omega⟩
  push_cast at hrbR
  have hj : (j : ℝ) ≤ 4 * Real.sqrt n := by linarith
  have hrn : (r : ℝ) ≤ n := by
    have : (0 : ℝ) ≤ r + j := by positivity
    linarith
  have hsq0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hn : n = 2 * r + j := by omega
  have e1 : (1 / 2 + δ) * (1 - (1 / 2 + δ)) = (1 / 2) ^ 2 * (1 - 4 * δ ^ 2) := by ring
  have e2 : 1 - (1 / 2 + δ) = 1 / 2 * (1 - 2 * δ) := by ring
  have e : (1 / 2 + δ) ^ r * (1 - (1 / 2 + δ)) ^ (r + j) =
      (1 / 2) ^ n * ((1 - 4 * δ ^ 2) ^ r * (1 - 2 * δ) ^ j) := by
    calc (1 / 2 + δ) ^ r * (1 - (1 / 2 + δ)) ^ (r + j) =
          ((1 / 2 + δ) * (1 - (1 / 2 + δ))) ^ r * (1 - (1 / 2 + δ)) ^ j := by
          rw [mul_pow, pow_add]; ring
      _ = ((1 / 2) ^ 2 * (1 - 4 * δ ^ 2)) ^ r * (1 / 2 * (1 - 2 * δ)) ^ j := by rw [e1, e2]
      _ = (1 / 2) ^ (2 * r + j) * ((1 - 4 * δ ^ 2) ^ r * (1 - 2 * δ) ^ j) := by
          rw [mul_pow, mul_pow, ← pow_mul, pow_add]; ring
      _ = _ := by rw [← hn]
  rw [e]
  -- Bernoulli's inequality for both factors
  have h1 : 1 - 4 * δ ^ 2 * n ≤ (1 - 4 * δ ^ 2) ^ r := by
    have := one_add_mul_le_pow (a := -(4 * δ ^ 2)) (by nlinarith) r
    rw [← sub_eq_add_neg] at this
    have : 4 * δ ^ 2 * r ≤ 4 * δ ^ 2 * n := by
      apply mul_le_mul_of_nonneg_left hrn; positivity
    linarith
  have h2 : 1 - 8 * δ * Real.sqrt n ≤ (1 - 2 * δ) ^ j := by
    have := one_add_mul_le_pow (a := -(2 * δ)) (by linarith) j
    rw [← sub_eq_add_neg] at this
    have : 2 * δ * j ≤ 2 * δ * (4 * Real.sqrt n) := by
      apply mul_le_mul_of_nonneg_left hj; positivity
    linarith
  have hA : 1 / 2 ≤ 1 - 4 * δ ^ 2 * n := by
    have : 0 ≤ 8 * δ * Real.sqrt n := by positivity
    linarith
  have hB : 1 / 2 ≤ 1 - 8 * δ * Real.sqrt n := by
    have : 0 ≤ 4 * δ ^ 2 * n := by positivity
    linarith
  have hprod : 1 / 2 ≤ (1 - 4 * δ ^ 2) ^ r * (1 - 2 * δ) ^ j := by
    have := mul_le_mul h1 h2 (by linarith) (le_trans (by linarith) h1)
    nlinarith
  have hpos : (0 : ℝ) < (1 / 2) ^ n := by positivity
  nlinarith

/-- Theorem 1.5 as printed (bias `ω((pn)⁻¹)`) is false: take `λ = 1`, `p = 1` and
`p_r = 1/2 + (log n)/n`. On the complete graph, if Blue has at least two more vertices than Red,
every vertex is Blue after one day; this happens with probability tending to `1/2`.

Proof (the formalization's; it uses none of the assumed cited results): `G(n, 1)` is the complete
graph, on which Red never wins once `|R₀| ≤ n/2 − 1` (`colorAux_blueAfter_top_ne_empty`). Under
the `1/2` colouring the window `n/2 − 2√n < |R₀| ≤ n/2 − 1` has probability at least `1/4` for
`n ≥ 64` (`colorAux_window_ge`: colour symmetry, the dense paper's Lemma 3.2 for the at most two
values of `|R₀|` within `1` of `n/2`, and the Chernoff bound for the lower tail). On the window,
the weight of a colouring changes by the factor `(1 − 4δ²)^r (1 − 2δ)^(n − 2r) ≥ 1/2` when
`p_r = 1/2 + δ`, `δ = (log n)/n` and `n` is large (`colorAux_weight_ge`, Bernoulli's inequality).
Hence Red wins with probability at most `7/8` for large `n`, so the probability does not tend
to `1`. -/
theorem theorem1_5_printed_false :
    ¬ ∀ (lam : ℝ), 0 < lam → ∀ (p q : ℕ → ℝ), (∀ n, 0 < p n) → (∀ n, p n ≤ 1) →
      (∀ n : ℕ, (1 + lam) * Real.log n / n ≤ p n) → (∀ n, q n ≤ 1) →
      Tendsto (fun n : ℕ => (q n - 1 / 2) * (p n * n)) atTop atTop →
      Tendsto (fun n : ℕ =>
        coloredProb n (p n) (q n) (fun G B₀ => ∃ t, blueAfter G B₀ t = ∅)) atTop (𝓝 1) := by
  intro h
  -- `2 log n ≤ n`
  have hlog2 : ∀ n : ℕ, 2 * Real.log n ≤ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hn')
    rw [Real.log_sqrt hn'.le] at h1
    have h2 := Real.mul_self_sqrt hn'.le
    nlinarith [sq_nonneg (Real.sqrt n - 2)]
  -- the counterexample: `λ = 1`, `p = 1`, `p_r = 1/2 + (log n)/n`
  set q : ℕ → ℝ := fun n => 1 / 2 + Real.log n / n with hq_def
  have hδ0 : ∀ n : ℕ, 0 ≤ Real.log n / n := fun n =>
    div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)
  have hδ1 : ∀ n : ℕ, Real.log n / n ≤ 1 / 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn']; linarith [hlog2 n]
  have hq1 : ∀ n, q n ≤ 1 := fun n => by simp only [hq_def]; linarith [hδ1 n]
  have hthr : ∀ n : ℕ, (1 + 1) * Real.log n / n ≤ 1 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn']; linarith [hlog2 n]
  have hbias : Tendsto (fun n : ℕ => (q n - 1 / 2) * (1 * n)) atTop atTop := by
    have : ∀ᶠ n : ℕ in atTop, Real.log n = (q n - 1 / 2) * (1 * n) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (n : ℝ) ≠ 0 := by positivity
      simp only [hq_def]; field_simp; ring
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).congr' this
  have hlim := h 1 one_pos (fun _ => 1) q (fun _ => one_pos) (fun _ => le_rfl) hthr hq1 hbias
  beta_reduce at hlim
  -- but Red wins with probability at most `7/8` for large `n`
  have hu : Tendsto (fun n : ℕ => Real.log n / Real.sqrt n) atTop (𝓝 0) := by
    have h1 := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).tendsto_div_nhds_zero
    have h2 := h1.comp tendsto_natCast_atTop_atTop
    refine h2.congr fun n => ?_
    simp [Function.comp, Real.sqrt_eq_rpow]
  have hle : ∀ᶠ n : ℕ in atTop,
      coloredProb n 1 (q n) (fun G B₀ => ∃ t, blueAfter G B₀ t = ∅) ≤ 7 / 8 := by
    filter_upwards [eventually_ge_atTop 64, (tendsto_order.1 hu).2 (1 / 32) (by norm_num)]
      with n hn64 hun
    have hnR : (64 : ℝ) ≤ n := by exact_mod_cast hn64
    have hnpos : (0 : ℝ) < n := by linarith
    have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
    have hsqrt8 : 8 ≤ Real.sqrt n := (Real.le_sqrt' (by norm_num)).mpr (by linarith)
    set δ := Real.log n / n with hδ
    set u := Real.log n / Real.sqrt n with hu_def
    have hu0 : 0 ≤ u := div_nonneg (Real.log_natCast_nonneg n) hsqrt.le
    have hδsq : δ * Real.sqrt n = u := by
      rw [hδ, hu_def, div_mul_eq_mul_div, div_eq_div_iff hnpos.ne' hsqrt.ne', mul_assoc, hsq]
    have hδn : δ ^ 2 * n = u ^ 2 := by
      rw [← hδsq, mul_pow, Real.sq_sqrt hnpos.le]
    have hsmall : 4 * δ ^ 2 * n + 8 * δ * Real.sqrt n ≤ 1 / 2 := by
      rw [mul_assoc, hδn, mul_assoc, hδsq]
      nlinarith
    have hqn0 : 0 ≤ q n := by simp only [hq_def]; linarith [hδ0 n]
    -- the window event `W`: `n/2 − 2√n < |R₀| ≤ n/2 − 1`
    set W : Set (Fin n) → Prop := fun B =>
      (n : ℝ) / 2 - 2 * Real.sqrt n < n - B.ncard ∧ (n : ℝ) - B.ncard ≤ n / 2 - 1 with hW
    -- on the complete graph, `W` makes Red lose
    have hstep1 : coloredProb n 1 (q n) (fun G B₀ => ∃ t, blueAfter G B₀ t = ∅) ≤
        1 - coloredProb n 1 (q n) (fun _ B₀ => W B₀) := by
      rw [colorAux_coloredProb_one hqn0 (hq1 n), ← colorAux_coloredProb_color_not]
      refine colorAux_coloredProb_mono fun G B ⟨t, ht⟩ hWB => ?_
      exact colorAux_blueAfter_top_ne_empty (by linarith [hWB.2]) t ht
    -- the change of measure from `1/2` to `q n`
    have hstep2 : 1 / 2 * (colorAux_law n (1 / 2)).real {χ | W {v | χ v = false}} ≤
        coloredProb n 1 (q n) (fun _ B₀ => W B₀) := by
      classical
      rw [colorAux_coloredProb_color_sum hqn0 (hq1 n),
        colorAux_law_real_eq_sum (by norm_num) (by norm_num), Finset.mul_sum]
      refine Finset.sum_le_sum fun χ _ => ?_
      split_ifs with hχ
      · rw [mul_one, mul_one, colorAux_weight_eq, colorAux_weight_eq]
        set r := (Finset.univ.filter (fun v => χ v = true)).card
        set b := (Finset.univ.filter (fun v => χ v = false)).card
        have hrb : r + b = n := by
          have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
            (fun v : Fin n => χ v = true)
          simpa using this
        have hbR : (b : ℝ) = (({v | χ v = false} : Set (Fin n)).ncard : ℝ) := by
          rw [colorAux_ncard_blue, colorAux_sum_red]
          have : ((r + b : ℕ) : ℝ) = n := by exact_mod_cast hrb
          push_cast at this
          linarith
        have hrR : (r : ℝ) = n - b := by
          have : ((r + b : ℕ) : ℝ) = n := by exact_mod_cast hrb
          push_cast at this
          linarith
        have hχ' : (n : ℝ) / 2 - 2 * Real.sqrt n < n - b ∧ (n : ℝ) - b ≤ n / 2 - 1 := by
          rw [hbR]; exact hχ
        have e : (1 / 2 : ℝ) ^ r * (1 - 1 / 2) ^ b = (1 / 2) ^ n := by
          rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← pow_add, hrb]
        rw [e]
        exact colorAux_weight_ge hrb (hδ0 n) (hδ1 n) (by rw [hrR]; linarith [hχ'.2])
          (by rw [hrR]; linarith [hχ'.1]) hsmall
      · simp
    -- under the `1/2` colouring, `W` has probability at least `1/4`
    have hstep3 : 1 / 4 ≤ (colorAux_law n (1 / 2)).real {χ | W {v | χ v = false}} :=
      colorAux_window_ge hn64
    nlinarith
  obtain ⟨n, hn1, hn2⟩ := (((tendsto_order.1 hlim).1 (7 / 8) (by norm_num)).and hle).exists
  linarith

end PowerOfFew.Sparse

end
