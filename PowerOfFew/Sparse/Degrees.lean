module

public import PowerOfFew.Model.Gnp
public import PowerOfFew.Model.Majority
public import PowerOfFew.Model.EdgeConditioning
public import Basic.Probability.Chernoff
public import Basic.Combinatorics.Choose

/-!
# Sparse paper, Appendix A: degrees of `G(n, p)`

* Lemma A.4: above the connectivity threshold, the minimum degree is a constant fraction of `pn`.
* Lemma A.5: below it, every large set of vertices has a large average degree.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-! ### Lemma A.4 -/

/-- The numerics of the proof of Lemma A.4: with `α = exp(−(8/ε + 7))` and `t = −log α`,
`α(1 − log α) = e^(−t)(1 + t) = 8(1/ε + 1) exp(−8/ε − 7) < ε/(4(1 + ε))`. (Equivalently
`32(1 + ε)² < ε² exp(8/ε + 7)`, which follows from `exp(8/ε) ≥ (1 + 4/ε)²` and `e⁷ > 32`.) -/
private theorem appAux_alpha_numeric {ε : ℝ} (hε : 0 < ε) :
    Real.exp (-(8 / ε + 7)) * (1 - Real.log (Real.exp (-(8 / ε + 7)))) < ε / (4 * (1 + ε)) := by
  have hx : 1 + 4 / ε ≤ Real.exp (4 / ε) := by linarith [Real.add_one_le_exp (4 / ε)]
  have h7 : (32 : ℝ) < Real.exp 7 := by
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 7 by norm_num)
    linarith
  have hsplit : Real.exp (8 / ε + 7) = Real.exp (4 / ε) ^ 2 * Real.exp 7 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have hE : ε + 4 ≤ ε * Real.exp (4 / ε) := by
    have := mul_le_mul_of_nonneg_left hx hε.le
    rw [mul_add, mul_one, mul_div_cancel₀ _ hε.ne'] at this
    linarith
  have hE2 : (ε + 4) ^ 2 ≤ ε ^ 2 * Real.exp (4 / ε) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hE 2
  have key : 32 * (1 + ε) ^ 2 < ε ^ 2 * Real.exp (8 / ε + 7) := by
    rw [hsplit]
    have h1 : 32 * (1 + ε) ^ 2 ≤ 32 * (ε + 4) ^ 2 := by nlinarith
    have h2 : 32 * (ε + 4) ^ 2 < Real.exp 7 * (ε + 4) ^ 2 :=
      mul_lt_mul_of_pos_right h7 (by positivity)
    have h3 : Real.exp 7 * (ε + 4) ^ 2 ≤ Real.exp 7 * (ε ^ 2 * Real.exp (4 / ε) ^ 2) :=
      mul_le_mul_of_nonneg_left hE2 (Real.exp_pos 7).le
    nlinarith
  have hA : 0 < Real.exp (8 / ε + 7) := Real.exp_pos _
  rw [Real.log_exp, Real.exp_neg]
  have h8 : (1 - -(8 / ε + 7)) = 8 * (1 + ε) / ε := by field_simp; ring
  rw [h8, ← div_eq_inv_mul, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `D(αp ‖ p) ≥ p(1 − α + α log α)`, from `log x ≥ 1 − 1/x` (proof of Lemma A.4). -/
private theorem appAux_klBern_ge {p α : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hα0 : 0 < α)
    (hα1 : α ≤ 1) : p * (1 - α + α * Real.log α) ≤ klBern (α * p) p := by
  unfold klBern
  have h1 : α * p / p = α := by field_simp
  rw [h1]
  have hq : 0 < 1 - α * p := by nlinarith
  have hq' : 0 < 1 - p := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hq hq')
  have h2 : (1 - α * p) * (1 - ((1 - α * p) / (1 - p))⁻¹) = p - α * p := by
    rw [inv_div]; field_simp; ring
  have h3 := mul_le_mul_of_nonneg_left hlog hq.le
  nlinarith

/-- The degree of `v` is the sum of the `n − 1` indicators of the edges at `v`. -/
private theorem appAux_degree_eq_sum {n : ℕ} (ω : EdgeVars n) (v : Fin n) :
    (degree (graphOfEdges ω) v : ℝ) = ∑ u : {u : Fin n // u ≠ v}, edgeInd s(v, u.1) ω := by
  classical
  have h1 : degree (graphOfEdges ω) v = nbrCount (graphOfEdges ω) Set.univ v := by
    unfold degree nbrCount
    congr 1
    ext u
    simp
  rw [h1, nbrCount_graphOfEdges]
  exact Finset.sum_subtype _ (fun u => by simp) (fun u => edgeInd s(v, u) ω)

/-- **Chernoff's bound for one degree** (proof of Lemma A.4): `d(v) ∼ Bin(n − 1, p)`, so
`P(d(v) ≤ αp(n − 1)) ≤ exp(−(n − 1) D(αp ‖ p)) ≤ exp(−p(n − 1)(1 − α + α log α))`. -/
private theorem appAux_degree_le {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (v : Fin n) :
    gnpProb n p (fun G => (degree G v : ℝ) ≤ α * p * ((n : ℝ) - 1)) ≤
      Real.exp (-(p * ((n : ℝ) - 1) * (1 - α + α * Real.log α))) := by
  classical
  have hX := isBernoulliFamily_edgesAt (n := n) hp0.le hp1.le v
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact v.elim0)
  have hcard : ((Finset.univ : Finset {u : Fin n // u ≠ v}).card : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.card_univ, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique,
      Nat.cast_sub hn, Nat.cast_one]
  rw [gnpProb_eq]
  have hset : {ω | (degree (graphOfEdges ω) v : ℝ) ≤ α * p * ((n : ℝ) - 1)} =
      {ω | ∑ u ∈ (Finset.univ : Finset {u : Fin n // u ≠ v}), edgeInd s(v, u.1) ω ≤
        (α * p) * ((Finset.univ : Finset {u : Fin n // u ≠ v}).card : ℝ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, appAux_degree_eq_sum, hcard]
  rw [hset]
  refine (hX.measureReal_sum_le_le_exp_klBern hp0 hp1 Finset.univ (by positivity)
    (by nlinarith)).trans ?_
  rw [hcard]
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  have h1 := appAux_klBern_ge hp0 hp1 hα0 hα1
  have h2 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have := mul_le_mul_of_nonneg_left h1 h2
  nlinarith

/-- **Lemma A.4** (`S:lem:degree-lower-bound`). Let `ε > 0`, `N_ε = 4/ε + 4` and
`α_ε = exp(−(8/ε + 7))`. With probability at least `1 − n^(−ε/2)`, a `G(n, p)` random graph with
`n ≥ N_ε` and `pn ≥ (1 + ε) log n` has minimum degree at least `α_ε p n`.

Proof (the paper's): Chernoff's bound `P(d(v) ≤ αp(n − 1)) ≤ exp(−(n − 1) D(αp ‖ p))` for
`d(v) ∼ Bin(n − 1, p)`, with `D(αp ‖ p) ≥ p(1 − α + α log α)`; `α` replaced by `αn/(n − 1)`; a
union bound over the `n` vertices, `e^(−T)` with `T ≥ T' log n`; and the numerics
`α_ε(1 − log α_ε) < ε/(4(1 + ε))`, `(1 + ε)/n ≤ ε/4`, so `T' ≥ ε/2`. (For `p = 1`, where the
relative-entropy form of Chernoff's bound, stated for `p < 1`, does not apply, `G(n, 1)` is the
complete graph, whose degrees are `n − 1 ≥ α_ε n`.) -/
theorem lemmaA_4 {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 4 / ε + 4 ≤ n) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) (hpn : (1 + ε) * Real.log n ≤ p * n) :
    1 - (n : ℝ) ^ (-(ε / 2)) ≤
      gnpProb n p (fun G => ∀ v, Real.exp (-(8 / ε + 7)) * p * n ≤ degree G v) := by
  classical
  set α : ℝ := Real.exp (-(8 / ε + 7)) with hα_def
  have h4ε : (0 : ℝ) < 4 / ε := by positivity
  have h8ε : (0 : ℝ) < 8 / ε := by positivity
  have hn4 : (4 : ℝ) < n := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hα0 : 0 < α := Real.exp_pos _
  have hnum : α * (1 - Real.log α) < ε / (4 * (1 + ε)) := appAux_alpha_numeric hε
  have hlogα : Real.log α = -(8 / ε + 7) := Real.log_exp _
  have hα_half : α ≤ 1 / 2 := by
    have h2 : α * (1 - Real.log α) ≥ α := by
      rw [hlogα]
      nlinarith
    have h3 : ε / (4 * (1 + ε)) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  rcases hp1.lt_or_eq with hp1' | hp1'
  swap
  · -- `p = 1`: `G(n, 1)` is the complete graph, whose degrees are `n − 1 ≥ α n`.
    subst hp1'
    have hunit : toUnit 1 = 1 := Subtype.ext (toUnit_coe zero_le_one le_rfl)
    have htop : ∀ v, α * 1 * n ≤ (degree (⊤ : SimpleGraph (Fin n)) v : ℝ) := by
      intro v
      have hdeg : degree (⊤ : SimpleGraph (Fin n)) v = n - 1 := by
        rw [degree, SimpleGraph.neighborSet_top, Set.ncard_eq_toFinset_card']
        simp only [Set.toFinset_compl, Set.toFinset_singleton]
        rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
      rw [hdeg, Nat.cast_sub (by exact_mod_cast (show (1 : ℝ) ≤ n by linarith)), Nat.cast_one]
      nlinarith
    unfold gnpProb
    rw [hunit, SimpleGraph.binomialRandom_one, measureReal_def,
      Measure.dirac_apply_of_mem (show (⊤ : SimpleGraph (Fin n)) ∈ {G | ∀ v, α * 1 * n ≤
        (degree G v : ℝ)} from htop)]
    have : 0 ≤ (n : ℝ) ^ (-(ε / 2)) := Real.rpow_nonneg hnpos.le _
    simp only [ENNReal.toReal_one]
    linarith
  -- `p < 1`. Replace `α` with `α n / (n − 1)` in the Chernoff bound for one degree.
  set α' : ℝ := α * n / (n - 1) with hα'_def
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  have hα'0 : 0 < α' := by positivity
  have hα'1 : α' ≤ 1 := by
    rw [hα'_def, div_le_one hn1]; nlinarith
  have hαα' : α ≤ α' := by
    rw [hα'_def, le_div_iff₀ hn1]; nlinarith
  -- `T' = (1 + ε)(1 − α + α log α − 1/n) − 1 ≥ ε/2`
  set c : ℝ := 1 - α + α * Real.log α - 1 / n with hc_def
  have hn_eps : (1 + ε) / n ≤ ε / 4 := by
    rw [div_le_iff₀ hnpos]
    have : 4 / ε * ε = 4 := by field_simp
    nlinarith
  have hT' : ε / 2 ≤ (1 + ε) * c - 1 := by
    have h1 : (1 + ε) * (α * (1 - Real.log α)) ≤ ε / 4 := by
      have := mul_lt_mul_of_pos_left hnum (show (0 : ℝ) < 1 + ε by linarith)
      have h2 : (1 + ε) * (ε / (4 * (1 + ε))) = ε / 4 := by field_simp
      linarith
    have h3 : (1 + ε) * c - 1 = ε - (1 + ε) * (α * (1 - Real.log α)) - (1 + ε) / n := by
      rw [hc_def]; field_simp; ring
    linarith
  have hc0 : 0 ≤ c := by nlinarith
  apply le_gnpProb_of_not_le
  calc gnpProb n p (fun G => ¬ ∀ v, α * p * n ≤ (degree G v : ℝ))
      ≤ gnpProb n p (fun G => ∃ v ∈ (Finset.univ : Finset (Fin n)),
          (degree G v : ℝ) ≤ α' * p * ((n : ℝ) - 1)) := by
        refine gnpProb_mono fun G hG => ?_
        simp only [not_forall, not_le] at hG
        obtain ⟨v, hv⟩ := hG
        refine ⟨v, Finset.mem_univ v, hv.le.trans (le_of_eq ?_)⟩
        rw [hα'_def]; field_simp
    _ ≤ ∑ v ∈ (Finset.univ : Finset (Fin n)),
          gnpProb n p (fun G => (degree G v : ℝ) ≤ α' * p * ((n : ℝ) - 1)) :=
        gnpProb_exists_le _ _
    _ ≤ ∑ _v ∈ (Finset.univ : Finset (Fin n)), Real.exp (-(p * n * c)) := by
        refine Finset.sum_le_sum fun v _ => (appAux_degree_le hp0 hp1' hα'0 hα'1 v).trans ?_
        apply Real.exp_le_exp.mpr
        apply neg_le_neg
        -- `p(n − 1)(1 − α' + α' log α') ≥ pn(1 − α + α log α − 1/n)`, as `log α' ≥ log α`
        have hlog : Real.log α ≤ Real.log α' := Real.log_le_log hα0 hαα'
        have hkey : ((n : ℝ) - 1) * α' = α * n := by rw [hα'_def]; field_simp
        have h1 : p * ((n : ℝ) - 1) * (1 - α' + α' * Real.log α') =
            p * ((n - 1) - α * n + α * n * Real.log α') := by
          have : p * ((n : ℝ) - 1) * (1 - α' + α' * Real.log α') =
              p * ((n - 1) - ((n : ℝ) - 1) * α' + ((n : ℝ) - 1) * α' * Real.log α') := by ring
          rw [this, hkey]
        have h2 : p * n * c = p * ((n - 1) - α * n + α * n * Real.log α) := by
          rw [hc_def]; field_simp; ring
        rw [h1, h2]
        have : α * n * Real.log α ≤ α * n * Real.log α' :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        nlinarith
    _ = n * Real.exp (-(p * n * c)) := by simp
    _ ≤ (n : ℝ) ^ (-(ε / 2)) := by
        -- `n e^{−pnc} ≤ e^{−T' log n} ≤ n^{−ε/2}`
        have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
        have h1 : (1 + ε) * Real.log n * c ≤ p * n * c := mul_le_mul_of_nonneg_right hpn hc0
        rw [Real.rpow_def_of_pos hnpos]
        calc (n : ℝ) * Real.exp (-(p * n * c))
            = Real.exp (Real.log n - p * n * c) := by
              rw [Real.exp_sub, Real.exp_log hnpos, div_eq_mul_inv, Real.exp_neg]
          _ ≤ Real.exp (Real.log n * -(ε / 2)) := by
              apply Real.exp_le_exp.mpr
              nlinarith

/-! ### Lemma A.5 -/

/-- Each pair of distinct elements of `W` comes from exactly two ordered pairs of `W.offDiag`. -/
private theorem appAux_sum_offDiag_eq {n : ℕ} (W : Finset (Fin n)) (g : Sym2 (Fin n) → ℝ) :
    ∑ x ∈ W.offDiag, g s(x.1, x.2) =
      2 * ∑ z ∈ W.offDiag.image (fun x => s(x.1, x.2)), g z := by
  classical
  rw [Finset.sum_comp (f := g) (g := fun x : Fin n × Fin n => s(x.1, x.2)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
  have hset : ({x ∈ W.offDiag | s(x.1, x.2) = s(a, b)} : Finset _) = {(a, b), (b, a)} := by
    ext ⟨x, y⟩
    rw [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert, Finset.mem_singleton]
    simp only [Sym2.eq_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨⟨ha, hb, hne⟩, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨⟨hb, ha, Ne.symm hne⟩, Or.inr ⟨rfl, rfl⟩⟩
  have hab' : (a, b) ≠ (b, a) := fun h => hne (Prod.mk.injEq _ _ _ _ ▸ h).1
  rw [hset, Finset.card_pair hab', nsmul_eq_mul]
  norm_num

/-- A sum over the ordered pairs of distinct elements of `W`. -/
private theorem appAux_sum_offDiag_eq_sum_erase {n : ℕ} (W : Finset (Fin n))
    (F : Fin n → Fin n → ℝ) :
    ∑ x ∈ W.offDiag, F x.1 x.2 = ∑ u ∈ W, ∑ v ∈ W.erase u, F u v := by
  classical
  have h1 : W.offDiag = (W ×ˢ W).filter (fun x => x.1 ≠ x.2) := by
    ext x
    simp [Finset.mem_offDiag, and_assoc]
  rw [h1, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_filter, Finset.filter_ne]

/-- `(u, v) ↦ {u, v}` is injective on `W × Wᶜ`. -/
private theorem appAux_injOn_prod_compl {n : ℕ} (W : Finset (Fin n)) :
    Set.InjOn (fun x : Fin n × Fin n => s(x.1, x.2)) ↑(W ×ˢ Wᶜ) := by
  rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_compl] at huv huv'
  simp only [Sym2.eq_iff] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd huv.1 huv'.2

/-- **`X = 2X₁ + X₂`** (proof of Lemma A.5): the sum of the degrees over `W` counts each pair
inside `W` twice and each pair between `W` and its complement once. -/
private theorem appAux_degSum_eq {n : ℕ} (ω : EdgeVars n) (W : Finset (Fin n)) :
    ∑ u ∈ W, (degree (graphOfEdges ω) u : ℝ) =
      2 * ∑ z ∈ W.offDiag.image (fun x => s(x.1, x.2)), edgeInd z ω +
        ∑ z ∈ (W ×ˢ Wᶜ).image (fun x => s(x.1, x.2)), edgeInd z ω := by
  classical
  -- `d(u) = d_W(u) + d_{Wᶜ}(u)`
  have hdeg : ∀ u ∈ W, (degree (graphOfEdges ω) u : ℝ) =
      ∑ v ∈ W.erase u, edgeInd s(u, v) ω + ∑ v ∈ Wᶜ, edgeInd s(u, v) ω := by
    intro u hu
    rw [← nbrCount_add_nbrCount_compl (G := graphOfEdges ω) (W : Set (Fin n)) u, Nat.cast_add,
      nbrCount_graphOfEdges, nbrCount_graphOfEdges]
    congr 1
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe, Finset.mem_erase]
      tauto
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_compl_iff, Finset.mem_coe,
        Finset.mem_compl]
      constructor
      · exact fun h => h.1
      · intro hv
        exact ⟨hv, fun h => hv (h ▸ hu)⟩
  rw [Finset.sum_congr rfl hdeg, Finset.sum_add_distrib]
  congr 1
  · -- the pairs inside `W`
    rw [← appAux_sum_offDiag_eq W (fun z => edgeInd z ω),
      appAux_sum_offDiag_eq_sum_erase W (fun u v => edgeInd s(u, v) ω)]
  · -- the pairs between `W` and `Wᶜ`
    rw [Finset.sum_image (appAux_injOn_prod_compl W), Finset.sum_product]

/-- The mgf of `c · 1_e` for an edge variable `e` of `G(n, p)`:
`E e^{s c 1_e} = p e^{sc} + 1 − p`. -/
private theorem appAux_mgf_edgeInd {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {z : Sym2 (Fin n)} (hz : ¬ z.IsDiag) (c s : ℝ) :
    mgf (fun ω => c * edgeInd z ω) (edgeLaw n p) s = p * Real.exp (s * c) + 1 - p := by
  have hB := isBernoulliFamily_edgeInd (n := n) hp0 hp1
  have h01 := hB.zero_or_one ⟨z, hz⟩
  have hmean : ∫ ω, edgeInd z ω ∂(edgeLaw n p) = p := hB.integral_eq ⟨z, hz⟩
  have hint : Integrable (fun ω => edgeInd z ω) (edgeLaw n p) := by
    refine Integrable.of_mem_Icc 0 1 (measurable_edgeInd z).aemeasurable (ae_of_all _ fun ω => ?_)
    rcases h01 ω with h | h <;> simp only at h <;> rw [h] <;> norm_num
  have hpt : ∀ ω, Real.exp (s * (c * edgeInd z ω)) =
      1 + (Real.exp (s * c) - 1) * edgeInd z ω := by
    intro ω
    rcases h01 ω with h | h <;> simp only at h <;> simp [h]
  unfold mgf
  simp_rw [hpt]
  rw [integral_add (integrable_const _) (hint.const_mul _), integral_const, integral_const_mul,
    hmean]
  simp only [probReal_univ, one_smul]
  ring

/-- **Chernoff's bound for `X = ∑_{u ∈ W} d(u)`** (proof of Lemma A.5). `X = 2X₁ + X₂`, where
`X₁ ∼ Bin(C(k, 2), p)` counts the pairs inside `W` and `X₂ ∼ Bin(k(n − k), p)` the pairs between
`W` and `Wᶜ` (`k = |W|`), and they are independent; so for `t ≥ 0`,
`P(X ≤ x) ≤ e^{tx} E e^{−tX} = e^{tx} E e^{−2tX₁} E e^{−tX₂}
  = e^{tx} (pe^{−2t} + 1 − p)^{C(k,2)} (pe^{−t} + 1 − p)^{k(n−k)}`. -/
private theorem appAux_degSum_chernoff {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (W : Finset (Fin n)) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    gnpProb n p (fun G => ∑ u ∈ W, (degree G u : ℝ) ≤ x) ≤
      Real.exp (t * x) * (p * Real.exp (-(2 * t)) + 1 - p) ^ (W.card.choose 2) *
        (p * Real.exp (-t) + 1 - p) ^ (W.card * (n - W.card)) := by
  classical
  obtain ⟨E₁, hE₁⟩ : ∃ E₁ : Finset (Sym2 (Fin n)),
      E₁ = W.offDiag.image (fun x => s(x.1, x.2)) := ⟨_, rfl⟩
  obtain ⟨E₂, hE₂⟩ : ∃ E₂ : Finset (Sym2 (Fin n)),
      E₂ = (W ×ˢ Wᶜ).image (fun x => s(x.1, x.2)) := ⟨_, rfl⟩
  have hdisj : Disjoint E₁ E₂ := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    rw [hE₁] at hz1
    rw [hE₂] at hz2
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hz1
    obtain ⟨⟨u, v⟩, huv, h⟩ := Finset.mem_image.mp hz2
    obtain ⟨ha, hb, _⟩ := Finset.mem_offDiag.mp hab
    simp only [Finset.mem_product, Finset.mem_compl] at huv
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huv.2 hb
    · exact huv.2 ha
  have hdiag : ∀ z ∈ E₁ ∪ E₂, ¬ z.IsDiag := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rw [hE₁] at hz
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
      exact Sym2.mk_isDiag_iff.not.mpr (Finset.mem_offDiag.mp hab).2.2
    · rw [hE₂] at hz
      obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hz
      simp only [Finset.mem_product, Finset.mem_compl] at huv
      intro hd
      have h := Sym2.mk_isDiag_iff.mp hd
      simp only at h
      exact huv.2 (h ▸ huv.1)
  have hcard₁ : E₁.card = W.card.choose 2 := by
    rw [hE₁]
    exact Sym2.card_image_offDiag W
  have hcard₂ : E₂.card = W.card * (n - W.card) := by
    rw [hE₂, Finset.card_image_of_injOn (appAux_injOn_prod_compl W), Finset.card_product,
      Finset.card_compl, Fintype.card_fin]
  -- `X = ∑_{z ∈ E₁ ∪ E₂} c_z 1_z` with `c = 2` on `E₁` and `c = 1` on `E₂`.
  let c : Sym2 (Fin n) → ℝ := fun z => if z ∈ E₁ then 2 else 1
  let Y : Sym2 (Fin n) → EdgeVars n → ℝ := fun z ω => c z * edgeInd z ω
  have hX : ∀ ω, ∑ u ∈ W, (degree (graphOfEdges ω) u : ℝ) = (∑ z ∈ E₁ ∪ E₂, Y z) ω := by
    intro ω
    rw [appAux_degSum_eq, Finset.sum_apply, Finset.sum_union hdisj, Finset.mul_sum, ← hE₁,
      ← hE₂]
    congr 1
    · refine Finset.sum_congr rfl fun z hz => ?_
      simp [Y, c, hz]
    · refine Finset.sum_congr rfl fun z hz => ?_
      simp [Y, c, Finset.disjoint_right.mp hdisj hz]
  have hmeas : ∀ z, Measurable (Y z) := fun z => measurable_const.mul (measurable_edgeInd z)
  have hind : iIndepFun Y (edgeLaw n p) :=
    (iIndepFun_edgeInd n p).comp (fun z x => c z * x) (fun z => measurable_const.mul measurable_id)
  have hY0 : ∀ z ω, 0 ≤ Y z ω := by
    intro z ω
    have hc : 0 ≤ c z := by simp only [c]; split_ifs <;> norm_num
    have he : 0 ≤ edgeInd z ω := by unfold edgeInd; split_ifs <;> norm_num
    exact mul_nonneg hc he
  rw [gnpProb_eq]
  have hset : {ω | ∑ u ∈ W, (degree (graphOfEdges ω) u : ℝ) ≤ x} =
      {ω | (∑ z ∈ E₁ ∪ E₂, Y z) ω ≤ x} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hX]
  rw [hset]
  have hint : Integrable (fun ω => Real.exp (-t * (∑ z ∈ E₁ ∪ E₂, Y z) ω)) (edgeLaw n p) := by
    refine Integrable.of_bound ?_ 1 (ae_of_all _ fun ω => ?_)
    · have hm : Measurable (fun ω => ∑ z ∈ E₁ ∪ E₂, Y z ω) :=
        Finset.measurable_sum _ fun z _ => hmeas z
      simp only [Finset.sum_apply]
      exact (hm.const_mul (-t)).exp.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have h0 : 0 ≤ (∑ z ∈ E₁ ∪ E₂, Y z) ω := by
        rw [Finset.sum_apply]
        exact Finset.sum_nonneg fun z _ => hY0 z ω
      calc Real.exp (-t * (∑ z ∈ E₁ ∪ E₂, Y z) ω) ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr (by nlinarith)
        _ = 1 := Real.exp_zero
  refine (measure_le_le_exp_mul_mgf x (by linarith : -t ≤ 0) hint).trans (le_of_eq ?_)
  rw [hind.mgf_sum hmeas, Finset.prod_union hdisj]
  have h₁ : ∏ z ∈ E₁, mgf (Y z) (edgeLaw n p) (-t) =
      (p * Real.exp (-(2 * t)) + 1 - p) ^ E₁.card := by
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun z hz => ?_
    rw [appAux_mgf_edgeInd hp0 hp1 (hdiag z (Finset.mem_union_left _ hz))]
    simp only [c, hz, ↓reduceIte]
    ring_nf
  have h₂ : ∏ z ∈ E₂, mgf (Y z) (edgeLaw n p) (-t) = (p * Real.exp (-t) + 1 - p) ^ E₂.card := by
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun z hz => ?_
    rw [appAux_mgf_edgeInd hp0 hp1 (hdiag z (Finset.mem_union_right _ hz))]
    simp only [c, Finset.disjoint_right.mp hdisj hz, ↓reduceIte, mul_one]
  rw [h₁, h₂, hcard₁, hcard₂, neg_neg]
  ring

/-- **The exponent at `t* = log((1 − pε)/(ε(1 − p)))`** (proof of Lemma A.5). With
`L(t) = log(pe^{−t} + 1 − p)` and `f(t) = tεp + L(t)`, the exponent of the Chernoff bound for the
threshold `εpnk` is
`t εpnk + C(k,2) L(2t) + k(n − k) L(t) = k(n − 1) f(t) + C(k,2)(f(2t) − 2f(t)) + tεpk`;
at `t*`, `f(t*) = −D(pε ‖ p) ≤ −p(1 − ε + ε log ε)`,
`f(2t*) − 2f(t*) = log((1 − 2pε + pε²)/(1 − p)) ≤ p/(1 − p)` and `t* ≤ −log ε + p/(1 − p)`. -/
private theorem appAux_exponent_le {n k p ε : ℝ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hp0 : 0 < p)
    (hp1 : p < 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    Real.log ((1 - p * ε) / (ε * (1 - p))) * (ε * p * n * k) +
        k * (k - 1) / 2 *
          Real.log (p * Real.exp (-(2 * Real.log ((1 - p * ε) / (ε * (1 - p))))) + 1 - p) +
        k * (n - k) * Real.log (p * Real.exp (-Real.log ((1 - p * ε) / (ε * (1 - p)))) + 1 - p) ≤
      k * (-(n - 1) * (p * (1 - ε + ε * Real.log ε)) + (k - 1) / 2 * (p / (1 - p)) +
        ε * p * (-Real.log ε + p / (1 - p))) := by
  set t := Real.log ((1 - p * ε) / (ε * (1 - p))) with ht
  have h1p : 0 < 1 - p := by linarith
  have hpε : 0 < 1 - p * ε := by nlinarith
  have hq : 0 < 1 - 2 * p * ε + p * ε ^ 2 := by nlinarith
  have hy : 0 < (1 - p * ε) / (ε * (1 - p)) := by positivity
  have het : Real.exp (-t) = ε * (1 - p) / (1 - p * ε) := by
    rw [Real.exp_neg, ht, Real.exp_log hy, inv_div]
  have het2 : Real.exp (-(2 * t)) = (ε * (1 - p) / (1 - p * ε)) ^ 2 := by
    rw [show -(2 * t) = -t + -t by ring, Real.exp_add, het]
    ring
  -- `a = log(1 − p)`, `b = log(1 − pε)`, `c = log ε`, `d = log(1 − 2pε + pε²)`
  have hta : t = Real.log (1 - p * ε) - Real.log ε - Real.log (1 - p) := by
    rw [ht, Real.log_div hpε.ne' (by positivity), Real.log_mul hε0.ne' h1p.ne']
    ring
  have hL1 : Real.log (p * Real.exp (-t) + 1 - p) = Real.log (1 - p) - Real.log (1 - p * ε) := by
    rw [het, show p * (ε * (1 - p) / (1 - p * ε)) + 1 - p = (1 - p) / (1 - p * ε) by
      field_simp; ring, Real.log_div h1p.ne' hpε.ne']
  have hL2 : Real.log (p * Real.exp (-(2 * t)) + 1 - p) =
      Real.log (1 - p) + Real.log (1 - 2 * p * ε + p * ε ^ 2) - 2 * Real.log (1 - p * ε) := by
    rw [het2, show p * (ε * (1 - p) / (1 - p * ε)) ^ 2 + 1 - p =
        (1 - p) * (1 - 2 * p * ε + p * ε ^ 2) / (1 - p * ε) ^ 2 by field_simp; ring,
      Real.log_div (by positivity) (by positivity), Real.log_mul h1p.ne' hq.ne', Real.log_pow]
    push_cast
    ring
  have hkl : klBern (ε * p) p =
      ε * p * Real.log ε + (1 - ε * p) * (Real.log (1 - p * ε) - Real.log (1 - p)) := by
    unfold klBern
    rw [show ε * p / p = ε by field_simp, show 1 - ε * p = 1 - p * ε by ring,
      Real.log_div hpε.ne' h1p.ne']
  -- the three estimates
  have hD := appAux_klBern_ge hp0 hp1 hε0 hε1.le
  have hb : Real.log (1 - p * ε) ≤ 0 := Real.log_nonpos hpε.le (by nlinarith)
  have hpe2 : 0 ≤ p * ε * (2 - ε) := mul_nonneg (mul_pos hp0 hε0).le (by linarith)
  have hd : Real.log (1 - 2 * p * ε + p * ε ^ 2) ≤ 0 :=
    Real.log_nonpos hq.le (by nlinarith)
  have ha : -Real.log (1 - p) ≤ p / (1 - p) := by
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr h1p)
    rw [Real.log_inv] at this
    have h2 : (1 - p)⁻¹ - 1 = p / (1 - p) := by field_simp; ring
    linarith
  have hft : t * (ε * p) + Real.log (p * Real.exp (-t) + 1 - p) = -klBern (ε * p) p := by
    rw [hL1, hkl, hta]
    ring
  have hΔ : Real.log (p * Real.exp (-(2 * t)) + 1 - p) - 2 * Real.log (p * Real.exp (-t) + 1 - p) ≤
      p / (1 - p) := by
    rw [hL1, hL2]
    linarith
  have htle : t ≤ -Real.log ε + p / (1 - p) := by
    rw [hta]
    linarith
  have hsplit : t * (ε * p * n * k) + k * (k - 1) / 2 * Real.log (p * Real.exp (-(2 * t)) + 1 - p) +
      k * (n - k) * Real.log (p * Real.exp (-t) + 1 - p) =
      k * (n - 1) * (t * (ε * p) + Real.log (p * Real.exp (-t) + 1 - p)) +
        k * (k - 1) / 2 * (Real.log (p * Real.exp (-(2 * t)) + 1 - p) -
          2 * Real.log (p * Real.exp (-t) + 1 - p)) + t * (ε * p * k) := by
    ring
  rw [hsplit, hft]
  have hkn : 0 ≤ k * (n - 1) := by nlinarith
  have hkk : 0 ≤ k * (k - 1) / 2 := by nlinarith
  have hepk : 0 ≤ ε * p * k := by positivity
  have e1 := mul_le_mul_of_nonneg_left (neg_le_neg hD) hkn
  have e2 := mul_le_mul_of_nonneg_left hΔ hkk
  have e3 := mul_le_mul_of_nonneg_right htle hepk
  nlinarith

/-- `C(n, k) ≤ exp(n H(k/n)) ≤ exp(k(1 + log n − log k))`, i.e. the estimate `h(x) ≥ x log x − x`
of `h(x) = x log x + (1 − x) log(1 − x) = −H(x)` (proof of Lemma A.5). -/
private theorem appAux_choose_le {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n.choose k : ℝ) ≤ Real.exp (k * (1 + Real.log n - Real.log k)) := by
  refine (Nat.choose_le_exp_mul_binEntropy n k).trans (Real.exp_le_exp.mpr ?_)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hn : (0 : ℝ) < n := by
    have : (k : ℝ) ≤ n := by exact_mod_cast hkn
    linarith
  have hx1 : (k : ℝ) / n ≤ 1 := by
    rw [div_le_one hn]
    exact_mod_cast hkn
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def]
  dsimp only
  have h1 : (n : ℝ) * (-((k : ℝ) / n) * Real.log ((k : ℝ) / n)) =
      k * (Real.log n - Real.log k) := by
    rw [Real.log_div hk'.ne' hn.ne']
    field_simp
    ring
  have h2 : (n : ℝ) * (-(1 - (k : ℝ) / n) * Real.log (1 - (k : ℝ) / n)) ≤ k := by
    rcases eq_or_lt_of_le hx1 with h | h
    · rw [h]
      simp only [sub_self, neg_zero, zero_mul, mul_zero]
      exact hk'.le
    · have h1x : 0 < 1 - (k : ℝ) / n := by linarith
      have hlog := Real.one_sub_inv_le_log_of_pos h1x
      have h3 : -(1 - (k : ℝ) / n) * Real.log (1 - (k : ℝ) / n) ≤ (k : ℝ) / n := by
        calc -(1 - (k : ℝ) / n) * Real.log (1 - (k : ℝ) / n)
            ≤ -(1 - (k : ℝ) / n) * (1 - (1 - (k : ℝ) / n)⁻¹) :=
              mul_le_mul_of_nonpos_left hlog (by linarith)
          _ = -(1 - (k : ℝ) / n) + (1 - (k : ℝ) / n) * (1 - (k : ℝ) / n)⁻¹ := by ring
          _ = (k : ℝ) / n := by rw [mul_inv_cancel₀ h1x.ne']; ring
      calc (n : ℝ) * (-(1 - (k : ℝ) / n) * Real.log (1 - (k : ℝ) / n)) ≤ n * ((k : ℝ) / n) :=
            mul_le_mul_of_nonneg_left h3 hn.le
        _ = k := by field_simp
  rw [mul_add]
  linarith

/-- **From `k`-sets to larger sets** (filling a gap of the proof of Lemma A.5, which only treats
`|U| = k`): if every `k`-subset `W` of `U` (`k ≥ 1`) has `∑_W f ≥ ck`, then `∑_U f ≥ c|U|`
whenever `|U| ≥ k`. (Induction on `|U|`: remove an element `u₀` of `U` where `f` is maximal; by
induction the others have average at least `c`, and `f(u₀)` is at least their average.) -/
private theorem appAux_le_sum_of_card_eq {α : Type*} [DecidableEq α] (f : α → ℝ) (c : ℝ)
    {k : ℕ} (hk : 1 ≤ k) (U : Finset α) (hkU : k ≤ U.card)
    (h : ∀ W ⊆ U, W.card = k → c * k ≤ ∑ u ∈ W, f u) : c * U.card ≤ ∑ u ∈ U, f u := by
  obtain ⟨m, hm⟩ : ∃ m, U.card = k + m := ⟨U.card - k, by omega⟩
  clear hkU
  induction m generalizing U with
  | zero =>
    have := h U (subset_refl U) (by omega)
    rw [hm]
    simpa using this
  | succ m ih =>
    have hne : U.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨u₀, hu₀, hmax⟩ := Finset.exists_max_image U f hne
    have hcard' : (U.erase u₀).card = k + m := by
      rw [Finset.card_erase_of_mem hu₀]
      omega
    have ih' := ih (U.erase u₀)
      (fun W hW hWk => h W (hW.trans (Finset.erase_subset _ _)) hWk) hcard'
    have hsum : ∑ u ∈ U, f u = f u₀ + ∑ u ∈ U.erase u₀, f u := (Finset.add_sum_erase U f hu₀).symm
    have hle : ∑ u ∈ U.erase u₀, f u ≤ (U.erase u₀).card * f u₀ := by
      have : ∑ u ∈ U.erase u₀, f u ≤ ∑ _u ∈ U.erase u₀, f u₀ :=
        Finset.sum_le_sum (fun u hu => hmax u (Finset.mem_of_mem_erase hu))
      simpa [Finset.sum_const, nsmul_eq_mul] using this
    rw [hcard'] at ih' hle
    have hpos : (0 : ℝ) < ((k + m : ℕ) : ℝ) := by
      have : 1 ≤ k + m := by omega
      exact_mod_cast this
    have hc : c ≤ f u₀ := by
      by_contra hlt
      push Not at hlt
      nlinarith
    rw [hsum, hm]
    push_cast at ih' hpos ⊢
    nlinarith

/-- The threshold `N(λ)` of Lemma A.5: eventually `log n ≤ n^r / 5` (`r > 0`). -/
private theorem appAux_eventually_log_le {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Real.log n ≤ (n : ℝ) ^ r / 5 := by
  have h := (isLittleO_log_rpow_atTop hr).bound (by norm_num : (0 : ℝ) < 1 / 5)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually h)
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] at this
  linarith [le_abs_self (Real.log n)]

/-- The numerics at the end of the proof of Lemma A.5 (the paper's `O(·)` terms made explicit):
with `B` the bracket of `appAux_exponent_le`, `1 + log n − log k + B ≤ −(δ/2) log n` once
`pn = (1 − λ) log n`, `p ≤ 1/5`, `kp ≤ 2/5`, `log k ≥ (λ + δ) log n`, `ε log(e/ε) ≤ δ/4` and
`δ log n ≥ 8`. Here `L = log n`, and `ε log(e/ε) = ε − ε log ε`. -/
private theorem appAux_final_numeric {n k p ε δ lam L : ℝ} (hL : 0 ≤ L) (hlam : 0 < lam)
    (hδ : 0 < δ) (hδlam : δ ≤ (1 - lam) / 2) (hδL : 8 ≤ δ * L) (hε : 0 < ε) (hε1 : ε < 1)
    (hεlog : ε - ε * Real.log ε ≤ δ / 4) (hp0 : 0 < p) (hp15 : p ≤ 1 / 5)
    (hpn : p * n = (1 - lam) * L) (hk1 : 1 ≤ k) (hkp : k * p ≤ 2 / 5)
    (hlogk : (lam + δ) * L ≤ Real.log k) :
    1 + L - Real.log k + (-(n - 1) * (p * (1 - ε + ε * Real.log ε)) + (k - 1) / 2 * (p / (1 - p)) +
      ε * p * (-Real.log ε + p / (1 - p))) ≤ -(δ / 2) * L := by
  have hlogε : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1.le
  have ha : ε * Real.log ε ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε.le hlogε
  have hεa0 : 0 ≤ ε - ε * Real.log ε := by linarith
  have hlam' : 0 < 1 - lam := by linarith
  -- `−(n − 1)pA ≤ −(1 − λ) log n + (δ/4) log n + p`, with `A = 1 − ε log(e/ε)`
  have t1 : -(n - 1) * (p * (1 - ε + ε * Real.log ε)) ≤ -((1 - lam) * L) + δ / 4 * L + p := by
    have e : -(n - 1) * (p * (1 - ε + ε * Real.log ε)) =
        -((1 - lam) * L) + (1 - lam) * L * (ε - ε * Real.log ε) +
          p * (1 - ε + ε * Real.log ε) := by
      rw [← hpn]
      ring
    rw [e]
    have h1 : (1 - lam) * (ε - ε * Real.log ε) ≤ δ / 4 := by
      nlinarith [mul_nonneg hlam.le hεa0]
    have h2 : (1 - lam) * L * (ε - ε * Real.log ε) ≤ δ / 4 * L := by nlinarith
    have h3 : p * (1 - ε + ε * Real.log ε) ≤ p := by nlinarith
    linarith
  -- `p/(1 − p) ≤ (5/4) p`
  have hp1' : p / (1 - p) ≤ 5 / 4 * p := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hpp : 0 ≤ p / (1 - p) := div_nonneg hp0.le (by linarith)
  have t2 : (k - 1) / 2 * (p / (1 - p)) ≤ k * p := by
    have := mul_le_mul_of_nonneg_left hp1' (show (0 : ℝ) ≤ (k - 1) / 2 by linarith)
    nlinarith
  have t3 : ε * p * (-Real.log ε + p / (1 - p)) ≤ p / 8 + p / 4 := by
    have h1 : -(ε * Real.log ε) ≤ 1 / 8 := by linarith
    have h2 : ε * p * (-Real.log ε) = p * (-(ε * Real.log ε)) := by ring
    have h3 : ε * p * (p / (1 - p)) ≤ p / 4 := by
      have : ε * (p / (1 - p)) ≤ 1 / 4 := by nlinarith
      nlinarith
    nlinarith
  nlinarith

/-- **Lemma A.5** (`S:lem:subcon-avg-deg`). Consider `G(n, p)` with `p = (1 − λ) n⁻¹ log n`. For
`0 < δ < 1 − λ` and `0 < ε < 1` with `ε log(e/ε) ≤ δ/4`, with probability at least
`1 − n^(−δ n^(λ+δ) / 2)`, every set `U` of at least `n^(λ+δ)` vertices has average degree at least
`ε p n`.

Deviation (hypotheses the paper's proof uses): the proof neglects `O(·)` terms that are small only
for `n` large, and Theorem 3.1 applies the lemma with `δ` and `ε` depending on `n`. The statement
therefore holds for `n ≥ N(λ)`, uniformly in `δ ≤ (1 − λ)/2` and `ε`, provided `δ log n ≥ 8` (the
proof's last step needs `δ log n` bounded below).

Proof (the paper's): for a set `W` of `k = ⌈n^(λ+δ)⌉` vertices, `X = ∑_{u ∈ W} d(u) = 2X₁ + X₂`
with independent `X₁ ∼ Bin(C(k, 2), p)` and `X₂ ∼ Bin(k(n − k), p)`; Chernoff's bound at
`t* = log((1 − pε)/(ε(1 − p)))`, where `f(t*) = −D(pε ‖ p)` and
`f(2t*) − 2f(t*) = log((1 − 2pε + pε²)/(1 − p)) = O(p)`, gives `exp(−k[(n − 1) D(pε ‖ p) − O(pk)])`;
a union bound over the `C(n, k) ≤ exp(n H(k/n))` sets and the estimates of `D(pε ‖ p)` and of the
binary entropy give `exp(−δ k log n / 2)`. Every `O(·)` is explicit here: `N(λ)` is such that
`log n ≤ n^((1−λ)/2)/5` for `n ≥ N(λ)` (`appAux_eventually_log_le`), which gives `p ≤ 1/5` and
`pk ≤ 2/5`; the estimates are used in their exact one-sided forms
`D(pε ‖ p) ≥ p(1 − ε + ε log ε)` and `n H(k/n) ≤ k(1 + log n − log k)`.

Departure from the paper: the paper bounds `P(X ≤ ε E X)`, `E X = pk(n − 1)`, while a small
average degree is the event `X < εpnk`. The same Chernoff bound is applied at the threshold
`εpnk = ε E X + εpk`, which adds `t* εpk = O(pk log(1/ε))` to the exponent, absorbed with the
paper's `O(pk)` terms (`appAux_exponent_le`).

Departure from the paper (a gap filled): the paper only treats sets of exactly `⌈n^(λ+δ)⌉` vertices. A larger set with a small
average degree contains such a set with a small average degree: removing a vertex of maximal
degree does not increase the average (`appAux_le_sum_of_card_eq`). -/
theorem lemmaA_5 {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ δ ε : ℝ, 0 < δ → δ ≤ (1 - lam) / 2 → 8 ≤ δ * Real.log n → 0 < ε →
      ε < 1 → ε * Real.log (Real.exp 1 / ε) ≤ δ / 4 →
      1 - (n : ℝ) ^ (-(δ * (n : ℝ) ^ (lam + δ) / 2)) ≤
        gnpProb n ((1 - lam) * Real.log n / n) (fun G => ∀ U : Set (Fin n),
          (n : ℝ) ^ (lam + δ) ≤ U.ncard →
            ε * ((1 - lam) * Real.log n / n) * n * U.ncard ≤ ∑ᶠ u ∈ U, (degree G u : ℝ)) := by
  classical
  obtain ⟨N, hN⟩ := appAux_eventually_log_le (r := (1 - lam) / 2) (by linarith)
  refine ⟨N, fun n hn δ ε hδ hδlam hδlog hε hε1 hεlog => ?_⟩
  have hlogn : 0 < Real.log n := by
    by_contra h
    push Not at h
    nlinarith
  have hn1 : (1 : ℝ) < n := by
    by_contra h
    push Not at h
    have : Real.log n ≤ 0 := Real.log_nonpos (Nat.cast_nonneg n) h
    linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogle : Real.log n ≤ (n : ℝ) ^ ((1 - lam) / 2) / 5 := hN n hn
  -- `p = (1 − λ) log n / n ≤ log n / n ≤ 1/5`
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (1 - lam) * Real.log n / n := ⟨_, rfl⟩
  rw [← hp]
  have hlam' : 0 < 1 - lam := by linarith
  have hp0 : 0 < p := by
    rw [hp]
    positivity
  have hpn : p * n = (1 - lam) * Real.log n := by
    rw [hp]
    field_simp
  have hpl : p ≤ Real.log n / n := by
    rw [hp]
    exact div_le_div_of_nonneg_right (by nlinarith) hnpos.le
  have hnr : 0 < (n : ℝ) ^ ((1 - lam) / 2) := Real.rpow_pos_of_pos hnpos _
  have hrn : (n : ℝ) ^ ((1 - lam) / 2) ≤ n := by
    calc (n : ℝ) ^ ((1 - lam) / 2) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1.le (by linarith)
      _ = n := Real.rpow_one _
  have hlogn_n : Real.log n / n ≤ 1 / 5 := by
    rw [div_le_iff₀ hnpos]
    linarith
  have hp15 : p ≤ 1 / 5 := hpl.trans hlogn_n
  -- `k = ⌈n^(λ+δ)⌉ ≤ n^(λ+δ) + 1 ≤ n^(1 − (1−λ)/2) + 1`, so `kp ≤ 2/5`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌈(n : ℝ) ^ (lam + δ)⌉₊ := ⟨_, rfl⟩
  have hnlam : 0 < (n : ℝ) ^ (lam + δ) := Real.rpow_pos_of_pos hnpos _
  have hkge : (n : ℝ) ^ (lam + δ) ≤ k := by
    rw [hk]
    exact Nat.le_ceil _
  have hk1 : 1 ≤ k := by
    rw [hk]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr hnlam))
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkle : (k : ℝ) ≤ (n : ℝ) ^ (lam + δ) + 1 := by
    rw [hk]
    exact (Nat.ceil_lt_add_one hnlam.le).le
  have hkn : k ≤ n := by
    rw [hk]
    apply Nat.ceil_le.mpr
    calc (n : ℝ) ^ (lam + δ) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1.le (by linarith)
      _ = n := Real.rpow_one _
  have hkp : (k : ℝ) * p ≤ 2 / 5 := by
    have h0 : (n : ℝ) ^ (lam + δ) ≤ (n : ℝ) ^ (1 - (1 - lam) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hn1.le (by linarith)
    have h1 : (n : ℝ) ^ (1 - (1 - lam) / 2) = n / (n : ℝ) ^ ((1 - lam) / 2) := by
      rw [Real.rpow_sub hnpos, Real.rpow_one]
    have h2 : (n : ℝ) ^ (1 - (1 - lam) / 2) * (Real.log n / n) ≤ 1 / 5 := by
      rw [h1, show (n : ℝ) / (n : ℝ) ^ ((1 - lam) / 2) * (Real.log n / n) =
        Real.log n / (n : ℝ) ^ ((1 - lam) / 2) by field_simp, div_le_iff₀ hnr]
      linarith
    calc (k : ℝ) * p ≤ ((n : ℝ) ^ (1 - (1 - lam) / 2) + 1) * (Real.log n / n) :=
          mul_le_mul (by linarith) hpl hp0.le (by positivity)
      _ = (n : ℝ) ^ (1 - (1 - lam) / 2) * (Real.log n / n) + Real.log n / n := by ring
      _ ≤ 2 / 5 := by linarith
  have hlogk : (lam + δ) * Real.log n ≤ Real.log k := by
    rw [← Real.log_rpow hnpos]
    exact Real.log_le_log hnlam hkge
  have hεlog' : ε - ε * Real.log ε ≤ δ / 4 := by
    rw [Real.log_div (Real.exp_pos 1).ne' hε.ne', Real.log_exp] at hεlog
    linarith
  -- `t* = log((1 − pε)/(ε(1 − p))) ≥ 0`
  have ht0 : 0 ≤ Real.log ((1 - p * ε) / (ε * (1 - p))) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by nlinarith)]
    nlinarith
  apply le_gnpProb_of_not_le
  calc gnpProb n p (fun G => ¬ ∀ U : Set (Fin n), (n : ℝ) ^ (lam + δ) ≤ U.ncard →
          ε * p * n * U.ncard ≤ ∑ᶠ u ∈ U, (degree G u : ℝ))
      ≤ gnpProb n p (fun G => ∃ W ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
          ∑ u ∈ W, (degree G u : ℝ) ≤ ε * p * n * k) := by
        -- a set `U` with `|U| ≥ n^(λ+δ)` and a small average degree contains a `k`-set with
        -- a small average degree
        refine gnpProb_mono fun G hG => ?_
        by_contra hW
        push Not at hW
        apply hG
        intro U hU
        rw [finsum_mem_eq_toFinset_sum, Set.ncard_eq_toFinset_card']
        have hkU : k ≤ U.toFinset.card := by
          rw [← Set.ncard_eq_toFinset_card', hk]
          exact Nat.ceil_le.mpr hU
        exact appAux_le_sum_of_card_eq (fun u => (degree G u : ℝ)) (ε * p * n) hk1 U.toFinset hkU
          (fun W _ hWk => (hW W (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hWk⟩)).le)
    _ ≤ ∑ W ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
          gnpProb n p (fun G => ∑ u ∈ W, (degree G u : ℝ) ≤ ε * p * n * k) :=
        gnpProb_exists_le _ _
    _ ≤ ∑ _W ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
          Real.exp (k * (-(n - 1) * (p * (1 - ε + ε * Real.log ε)) +
            (k - 1) / 2 * (p / (1 - p)) + ε * p * (-Real.log ε + p / (1 - p)))) := by
        refine Finset.sum_le_sum fun W hW => ?_
        have hWk : W.card = k := (Finset.mem_powersetCard.mp hW).2
        refine (appAux_degSum_chernoff hp0.le (by linarith) W ht0 (ε * p * n * k)).trans ?_
        rw [hWk]
        set t := Real.log ((1 - p * ε) / (ε * (1 - p))) with ht
        have hY1 : 0 < p * Real.exp (-t) + 1 - p := by
          have := Real.exp_pos (-t)
          nlinarith
        have hY2 : 0 < p * Real.exp (-(2 * t)) + 1 - p := by
          have := Real.exp_pos (-(2 * t))
          nlinarith
        have hpow1 : (p * Real.exp (-t) + 1 - p) ^ (k * (n - k)) =
            Real.exp (((k * (n - k) : ℕ) : ℝ) * Real.log (p * Real.exp (-t) + 1 - p)) := by
          rw [Real.exp_nat_mul, Real.exp_log hY1]
        have hpow2 : (p * Real.exp (-(2 * t)) + 1 - p) ^ (k.choose 2) =
            Real.exp (((k.choose 2 : ℕ) : ℝ) * Real.log (p * Real.exp (-(2 * t)) + 1 - p)) := by
          rw [Real.exp_nat_mul, Real.exp_log hY2]
        rw [hpow1, hpow2, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hcast : ((k * (n - k) : ℕ) : ℝ) = k * (n - k) := by
          rw [Nat.cast_mul, Nat.cast_sub hkn]
        rw [Nat.cast_choose_two, hcast]
        exact appAux_exponent_le hn1.le hk1' hp0 (by linarith) hε hε1
    _ = n.choose k * Real.exp (k * (-(n - 1) * (p * (1 - ε + ε * Real.log ε)) +
            (k - 1) / 2 * (p / (1 - p)) + ε * p * (-Real.log ε + p / (1 - p)))) := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ ≤ Real.exp (k * (1 + Real.log n - Real.log k)) *
          Real.exp (k * (-(n - 1) * (p * (1 - ε + ε * Real.log ε)) +
            (k - 1) / 2 * (p / (1 - p)) + ε * p * (-Real.log ε + p / (1 - p)))) :=
        mul_le_mul_of_nonneg_right (appAux_choose_le hk1 hkn) (Real.exp_pos _).le
    _ ≤ (n : ℝ) ^ (-(δ * (n : ℝ) ^ (lam + δ) / 2)) := by
        rw [← Real.exp_add, Real.rpow_def_of_pos hnpos]
        apply Real.exp_le_exp.mpr
        have hper := appAux_final_numeric hlogn.le hlam hδ hδlam hδlog hε hε1 hεlog' hp0 hp15 hpn
          hk1' hkp hlogk
        have hk0 : (0 : ℝ) ≤ k := by positivity
        have h1 := mul_le_mul_of_nonneg_left hper hk0
        have h2 : (k : ℝ) * (-(δ / 2) * Real.log n) ≤
            (n : ℝ) ^ (lam + δ) * (-(δ / 2) * Real.log n) :=
          mul_le_mul_of_nonpos_right hkge (by nlinarith)
        nlinarith

end PowerOfFew.Sparse

end
