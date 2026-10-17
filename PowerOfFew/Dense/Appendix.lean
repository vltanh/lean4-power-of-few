module

public import PowerOfFew.Sparse.Main
public import PowerOfFew.Sparse.BerryEsseen
public import PowerOfFew.Sparse.ColoringAux

/-!
# Dense paper: Theorem 1.5 and Appendix A

The dense paper states its Theorem 1.5 (the power of few above the connectivity threshold) without
proof, for its "upcoming paper" (the sparse paper), and in Appendix A derives from it a delayed
version of the theorem of Fountoulakis, Kang and Makai (its Theorem 1.4, cited for context only).

Here Theorem 1.5 is proved from the sparse paper's Theorem 1.2 (and a direct argument when
`p > 1 − 10/n`, a case that Theorem 1.2 excludes: `colorAux_nearComplete` in
`PowerOfFew/Sparse/ColoringAux.lean`), and Appendix A follows the dense paper's argument from
Theorem 1.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

namespace PowerOfFew.Dense

/-- **Theorem 1.5** (`D:thm:general-sparse`). For any `0 < ε ≤ 1` and `λ > 0` there is
`c = c(ε, λ)` such that, for `p ≥ (1 + λ)(log n)/n`, if Red starts with `n/2 + c/p` members then it
wins with probability at least `1 − ε`.

Reading: "starts with `n/2 + c/p` members" is read as "at least", and "wins" as "is unanimous at
some day".

Proof (the formalization's; the paper defers the proof to the sparse paper, whose Theorem 1.2 it
is): `Δ = n/2 − |B₀| ≥ c/p ≥ c` forces `n ≥ 2c`. If `pn ≤ n − 10`, the sparse paper's Theorem 1.2
applies (`pΔ ≥ c ≥ 10`, `pΔ² ≥ cΔ ≥ c² ≥ 2c`), with failure probability at most
`C (1/(2c) + (2c)^(−λ/2)) ≤ ε` for `c` large. If `pn > n − 10`, Theorem 1.2 does not apply, and Red,
ahead by `2Δ ≥ 2c` vertices, wins within two days with probability at least
`1 − 40/(2c − 1) − 2048/n ≥ 1 − 1064/c` (`colorAux_nearComplete`). The paper's `ε ≤ 1` is not
needed and is omitted. -/
theorem theorem1_5 (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10)
    {ε : ℝ} (hε0 : 0 < ε) {lam : ℝ} (hlam : 0 < lam) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (p : ℝ), 0 < p → p ≤ 1 → (1 + lam) * Real.log n / n ≤ p →
      ∀ B₀ : Set (Fin n), (B₀.ncard : ℝ) ≤ n / 2 - c / p →
        1 - ε ≤ gnpProb n p (fun G => ∃ t, blueAfter G B₀ t = ∅) := by
  obtain ⟨C, K, hmain⟩ := Sparse.theorem1_2 hBE hBBK hBLM hlam
  set C' := max C 1 with hC'
  -- the failure bounds tend to `0` as `c → ∞`
  have h2c : Tendsto (fun c : ℝ => 2 * c) atTop atTop := tendsto_id.const_mul_atTop two_pos
  have hT1 : Tendsto (fun c : ℝ => C' * (1 / (2 * c) + (2 * c) ^ (-(lam / 2)))) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop h2c).add
      ((tendsto_rpow_neg_atTop (by linarith : 0 < lam / 2)).comp h2c)
    simpa using this.const_mul C'
  have hT2 : Tendsto (fun c : ℝ => 1064 / c) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  obtain ⟨c, hc22, hc1, hc2⟩ := ((eventually_ge_atTop 22).and
    (((tendsto_order.1 hT1).2 ε hε0).and ((tendsto_order.1 hT2).2 ε hε0))).exists
  refine ⟨c, by linarith, fun n p hp0 hp1 hlog B₀ hB => ?_⟩
  have hB0 : (0 : ℝ) ≤ B₀.ncard := Nat.cast_nonneg _
  have hcp : c ≤ c / p := by rw [le_div_iff₀ hp0]; nlinarith
  -- `Δ = n/2 − |B₀| ≥ c/p ≥ c`, so `n ≥ 2c`
  have hn2c : 2 * c ≤ n := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  set Δ : ℝ := (n : ℝ) / 2 - B₀.ncard with hΔ
  have hΔc : c / p ≤ Δ := by linarith
  have hΔc' : c ≤ Δ := hcp.trans hΔc
  have hpΔ : c ≤ p * Δ := by
    have := mul_le_mul_of_nonneg_left hΔc hp0.le
    rwa [mul_div_cancel₀ _ hp0.ne'] at this
  by_cases hnear : p * n ≤ (n : ℝ) - 10
  · -- the sparse paper's Theorem 1.2: `pΔ ≥ c ≥ 10` and `pΔ² ≥ cΔ ≥ c² ≥ 2c`
    have hlog' : (1 + lam) * Real.log n ≤ p * n := by rwa [div_le_iff₀ hnpos] at hlog
    have h := hmain n p B₀ hp0 hnear hlog' (by rw [← hΔ]; linarith)
    have hmin : 2 * c ≤ min (n : ℝ) (p * Δ ^ 2) := by
      refine le_min hn2c ?_
      nlinarith
    have hfail : C * (1 / min (n : ℝ) (p * Δ ^ 2) + (n : ℝ) ^ (-(lam / 2))) ≤ ε := by
      have hmin0 : 0 < min (n : ℝ) (p * Δ ^ 2) := by linarith
      have hpos : 0 ≤ 1 / min (n : ℝ) (p * Δ ^ 2) + (n : ℝ) ^ (-(lam / 2)) := by positivity
      calc C * (1 / min (n : ℝ) (p * Δ ^ 2) + (n : ℝ) ^ (-(lam / 2)))
          ≤ C' * (1 / min (n : ℝ) (p * Δ ^ 2) + (n : ℝ) ^ (-(lam / 2))) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
        _ ≤ C' * (1 / (2 * c) + (2 * c) ^ (-(lam / 2))) := by
            refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
            · exact one_div_le_one_div_of_le (by linarith) hmin
            · exact Real.rpow_le_rpow_of_nonpos (by linarith) hn2c (by linarith)
        _ ≤ ε := hc1.le
    calc 1 - ε ≤ 1 - C * (1 / min (n : ℝ) (p * Δ ^ 2) + (n : ℝ) ^ (-(lam / 2))) := by
          linarith
      _ ≤ _ := h
      _ ≤ _ := gnpProb_mono fun G ⟨t, _, ht⟩ => ⟨t, ht⟩
  · -- the near-complete case `pn > n − 10`: Red leads by `2Δ ≥ 2c` vertices
    push Not at hnear
    have hn44 : 44 ≤ n := by exact_mod_cast (show (44 : ℝ) ≤ n by linarith)
    have h := colorAux_nearComplete hn44 hp1 hnear (m := 2 * c) (by linarith) (by linarith)
    have hbound : 40 / (2 * c - 1) + 2048 / (n : ℝ) ≤ ε := by
      have h1 : 40 / (2 * c - 1) ≤ 40 / c :=
        div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
      have h2 : 2048 / (n : ℝ) ≤ 1024 / c := by
        rw [div_le_div_iff₀ hnpos (by linarith)]; nlinarith
      have : 40 / c + 1024 / c = 1064 / c := by ring
      linarith
    calc 1 - ε ≤ 1 - (40 / (2 * c - 1) + 2048 / n) := by linarith
      _ ≤ gnpProb n p (fun G => blueAfter G B₀ 2 = ∅) := h
      _ ≤ _ := gnpProb_mono fun G hG => ⟨2, hG⟩

/-- The Berry–Esseen inequality (the dense paper's Theorem 2.2, with Shevtsova's constant `0.56`)
for the number `|R₀| ∼ Bin(n, 1/2)` of Red vertices of a random `1/2` colouring:
`|P(|R₀| − n/2 ≤ x) − Φ(2x/√n)| ≤ 0.56/√n` (here `σ = 1/2` and `1 − 2σ² = 1/2`). -/
private theorem colorAux_berryEsseen_dense (hBE : ShevtsovaBerryEsseen) {n : ℕ} (hn : 0 < n)
    (x : ℝ) :
    |(colorAux_law n (1 / 2)).real {χ | ∑ v, colorAux_red v χ - n / 2 ≤ x} -
      Φ (2 * x / Real.sqrt n)| ≤ 0.56 / Real.sqrt n := by
  have hX := colorAux_isBernoulliFamily (n := n) (q := 1 / 2) (by norm_num) (by norm_num)
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  have h := berryEsseen_signedBernoulli hBE (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hX (fun _ => 1) (fun _ => Or.inl rfl) hne x
  have hσ : Real.sqrt ((1 / 2 : ℝ) * (1 - 1 / 2)) = 1 / 2 := by
    rw [show (1 / 2 : ℝ) * (1 - 1 / 2) = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hset : {ω : Fin n → Bool | ∑ i ∈ Finset.univ, (1 : ℝ) * (colorAux_red i ω - 1 / 2) ≤ x} =
      {χ | ∑ v, colorAux_red v χ - n / 2 ≤ x} := by
    ext χ
    simp only [one_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Set.mem_ofPred_eq]
    ring_nf
  rw [hσ, Finset.card_univ, Fintype.card_fin, hset] at h
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have e1 : x / (1 / 2 * Real.sqrt n) = 2 * x / Real.sqrt n := by field_simp
  have e2 : (0.56 : ℝ) * (1 - 2 * (1 / 2 * (1 - 1 / 2))) / (1 / 2 * Real.sqrt n) =
      0.56 / Real.sqrt n := by
    field_simp; norm_num
  rw [e1, e2] at h
  exact h

/-- **Appendix A** (`D:appx:FKM-proof`): the dense paper's proof of a delayed version of the
theorem of Fountoulakis, Kang and Makai (Theorem 1.4) from Theorem 1.5. For any `0 < ε ≤ 1` there
is `λ` such that, for `p ≥ λ n^(−1/2)`, with probability at least `1 − ε` over the random graph
`G(n, p)` and the random `1/2` initial colouring, the dominating colour wins.

Reading: the appendix proves that the dominating colour wins, without the four-day bound of
Theorem 1.4 ("a delayed version", Section 1.4); `p ≥ λ n^(−1/2)` is written `λ ≤ p √n`; a tie
counts as a failure.

Proof (the paper's): with `c' = ε/6`, the Berry–Esseen inequality (Theorem 2.2) gives
`P(||R₀| − n/2| < c'√n) ≤ Φ(2c') − Φ(−2c') + 2 · 0.56/√n ≤ 4c'/√(2π) + 1.12/√n ≤ ε/2`; the TeX
prints `20.56/√n` for `2 · 0.56/√n`. The bad event is taken with a strict inequality, so that its
probability is at most `P(|R₀| − n/2 ≤ c'√n) − P(|R₀| − n/2 ≤ −c'√n)` as the paper computes;
otherwise the majority side has at least `n/2 + c'√n ≥ n/2 + c/p` members (as `p c'√n ≥ c'λ ≥ c`)
and wins with probability at least `1 − ε/2` by Theorem 1.5 (colour symmetry for Blue). The
paper's "for sufficiently large `n`" holds because `p ≤ 1` forces `n ≥ λ²`, and Theorem 1.5's
condition `p ≥ 2 log n / n` holds because `pn ≥ λ√n ≥ 4√n`. -/
theorem appendixA (hBE : ShevtsovaBerryEsseen) (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ (n : ℕ) (p : ℝ), lam ≤ p * Real.sqrt n → p ≤ 1 →
      1 - ε ≤ coloredProb n p (1 / 2) (fun G B₀ =>
        ((B₀.ncard : ℝ) < n / 2 ∧ ∃ t, blueAfter G B₀ t = ∅) ∨
          ((n : ℝ) / 2 < B₀.ncard ∧ ∃ t, blueAfter G B₀ t = Set.univ)) := by
  -- Theorem 1.5 with `ε/2` (and `λ = 1`: `p ≥ λ n^(−1/2)` gives `p ≥ 2 log n / n`)
  obtain ⟨c, hc, h15⟩ := theorem1_5 hBE hBBK hBLM (ε := ε / 2) (by linarith)
    (lam := 1) one_pos
  -- the paper's constant `c' ≤ ε/6`
  set c' : ℝ := ε / 6 with hc'
  have hc'0 : 0 < c' := by positivity
  set lam : ℝ := max (max 4 (c / c')) (6.72 / ε) with hlam_def
  have hlam4 : 4 ≤ lam := le_trans (le_max_left _ _) (le_max_left _ _)
  have hlamc : c / c' ≤ lam := le_trans (le_max_right _ _) (le_max_left _ _)
  have hlamε : 6.72 / ε ≤ lam := le_max_right _ _
  refine ⟨lam, by linarith, fun n p hlam hp1 => ?_⟩
  have hsqrt0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hp0 : 0 < p := by
    by_contra h
    push Not at h
    nlinarith
  have hlamsqrt : lam ≤ Real.sqrt n := by nlinarith
  have hsqrt : 0 < Real.sqrt n := by linarith
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hsqrt
    · exact h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  -- `pn = (p√n)√n ≥ λ√n ≥ 4√n ≥ 2 log n`
  have hlog : (1 + 1) * Real.log n / n ≤ p := by
    rw [div_le_iff₀ hnR]
    have h1 := colorAux_log_le_two_sqrt n
    have h2 : p * n = p * Real.sqrt n * Real.sqrt n := by
      rw [mul_assoc, Real.mul_self_sqrt hnR.le]
    have h3 := mul_le_mul_of_nonneg_right hlam hsqrt0
    nlinarith
  -- `c/p ≤ c'√n`, because `p c'√n ≥ c'λ ≥ c`
  have hcp : c / p ≤ c' * Real.sqrt n := by
    rw [div_le_iff₀ hp0]
    have : c ≤ c' * lam := by rwa [div_le_iff₀ hc'0, mul_comm] at hlamc
    nlinarith
  -- a majority side with at least `n/2 + c'√n` members wins with probability `1 − ε/2`
  have hgood : ∀ B₀ : Set (Fin n), c' * Real.sqrt n ≤ |(n : ℝ) / 2 - B₀.ncard| →
      1 - ε / 2 ≤ gnpProb n p (fun G =>
        ((B₀.ncard : ℝ) < n / 2 ∧ ∃ t, blueAfter G B₀ t = ∅) ∨
          ((n : ℝ) / 2 < B₀.ncard ∧ ∃ t, blueAfter G B₀ t = Set.univ)) := by
    intro B₀ hB
    have hpos : 0 < c' * Real.sqrt n := by positivity
    rcases le_or_gt (B₀.ncard : ℝ) (n / 2) with h | h
    · -- Red is the majority side
      rw [abs_of_nonneg (by linarith)] at hB
      exact (h15 n p hp0 hp1 hlog B₀ (by linarith)).trans
        (gnpProb_mono fun G hG => Or.inl ⟨by linarith, hG⟩)
    · -- Blue is the majority side: Theorem 1.5 for the swapped colouring
      rw [abs_of_neg (by linarith)] at hB
      have hBc : ((B₀ᶜ).ncard : ℝ) ≤ n / 2 - c / p := by
        rw [colorAux_ncard_compl]; linarith
      exact (h15 n p hp0 hp1 hlog B₀ᶜ hBc).trans
        (gnpProb_mono fun G ⟨t, ht⟩ => Or.inr ⟨h, t, colorAux_blueAfter_eq_univ ht⟩)
  -- by Berry–Esseen, the gap is at least `c'√n` with probability at least `1 − ε/2`
  have hcol : 1 - ε / 2 ≤ coloredProb n p (1 / 2) (fun _ B₀ =>
      c' * Real.sqrt n ≤ |(n : ℝ) / 2 - B₀.ncard|) := by
    rw [colorAux_coloredProb_gap]
    have hgap := colorAux_gap_le hn hc'0.le (colorAux_berryEsseen_dense hBE hn)
    have hpi : 2 ≤ Real.sqrt (2 * Real.pi) :=
      (Real.le_sqrt' two_pos).mpr (by nlinarith [Real.pi_gt_three])
    have h1 : 4 * c' / Real.sqrt (2 * Real.pi) ≤ ε / 3 := by
      rw [div_le_iff₀ (by linarith), hc']
      nlinarith
    have h2 : 2 * (0.56 / Real.sqrt n) ≤ ε / 6 := by
      rw [show 2 * (0.56 / Real.sqrt n) = 1.12 / Real.sqrt n by ring, div_le_iff₀ hsqrt]
      have : 6.72 ≤ lam * ε := by rwa [div_le_iff₀ hε0] at hlamε
      nlinarith
    linarith
  have := colorAux_le_coloredProb (by norm_num) (by norm_num) hgood hcol (by linarith)
    (by linarith)
  linarith

end PowerOfFew.Dense

end
