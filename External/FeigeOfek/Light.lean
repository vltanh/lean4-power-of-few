module

public import External.FeigeOfek.Defs
public import Basic.Probability.WeightedBernoulli
public import Basic.Analysis.GridNet

/-!
# Feige and Ofek's bound for the light pairs

For `x, y` in the grid net, the light part of `xᵀ (A − E A) y` (the pairs `u ≠ v` with
`|xᵤ y_v| ≤ √d / n`, `d = pn`) is a weighted sum `∑ a_{uv} (X_{uv} − p)`, over the unordered
pairs `{u, v}`, of the independent edge indicators `X_{uv}` (`SimpleGraph.edgeInd` under
`SimpleGraph.edgeLaw`), with `a_{uv} = xᵤ y_v [(u, v) light] + x_v yᵤ [(v, u) light]`, so
`|a_{uv}| ≤ 2√d / n` and `∑ a_{uv}² ≤ 2`. The exponential-moment bound with `θ = n / (2√d)`
(`IsBernoulliFamily.integral_exp_mul_sum_le`) gives `P(|light| > 21 √d) ≤ 2 e^(−10 n)`, and the net
has at most `(33 e)ⁿ ≤ e^(4.5 n)` points, so a union bound over the pairs of points gives the
bound below (Feige–Ofek 2005, Section 2.2; Chin–Rao–Vu 2015, the light pairs).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open SimpleGraph (EdgeVars OffDiag edgeLaw graphOfEdges edgeInd adj_graphOfEdges
  isBernoulliFamily_edgeInd)

noncomputable section

namespace External.FeigeOfek

/-! ### Sums over the pairs of distinct vertices -/

/-- A double sum over the ordered pairs `u ≠ v` is the sum over `offDiag`. -/
private theorem fo5Aux_sum_ite_ne {n : ℕ} (f : Fin n × Fin n → ℝ) :
    ∑ u, ∑ v, (if u ≠ v then f (u, v) else 0) =
      ∑ q ∈ (Finset.univ : Finset (Fin n)).offDiag, f q := by
  classical
  have h : (Finset.univ : Finset (Fin n)).offDiag =
      (Finset.univ ×ˢ Finset.univ).filter (fun q : Fin n × Fin n => q.1 ≠ q.2) := by
    ext q
    simp
  rw [h, Finset.sum_filter, Finset.sum_product]

/-- Each pair of distinct vertices comes from exactly two ordered pairs (the argument of
`appAux_sum_offDiag` in `PowerOfFew/Sparse/MatrixNormDerivation.lean`). -/
private theorem fo5Aux_sum_offDiag {n : ℕ} (g : Sym2 (Fin n) → ℝ) :
    ∑ x ∈ (Finset.univ : Finset (Fin n)).offDiag, g s(x.1, x.2) = 2 * ∑ z : OffDiag n, g z.1 := by
  classical
  have h1 : ∑ x ∈ (Finset.univ : Finset (Fin n)).offDiag, g s(x.1, x.2) =
      ∑ x ∈ (Finset.univ : Finset (Fin n)).offDiag, g (Sym2.mk.uncurry x) := rfl
  rw [h1, Finset.sum_comp]
  have hfib : ∀ z ∈ (Finset.univ : Finset (Fin n)).offDiag.image Sym2.mk.uncurry,
      ({x ∈ (Finset.univ : Finset (Fin n)).offDiag | Sym2.mk.uncurry x = z} : Finset _).card
        = 2 := by
    intro z hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    have hne : a ≠ b := (Finset.mem_offDiag.mp hab).2.2
    have hset : ({x ∈ (Finset.univ : Finset (Fin n)).offDiag | Sym2.mk.uncurry x =
        Sym2.mk.uncurry (a, b)} : Finset _) = {(a, b), (b, a)} := by
      ext ⟨x, y⟩
      rw [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert, Finset.mem_singleton]
      simp only [Finset.mem_univ, true_and, Function.uncurry_apply_pair, Sym2.eq_iff,
        Prod.mk.injEq]
      constructor
      · rintro ⟨_, h⟩
        exact h
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨hne, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨Ne.symm hne, Or.inr ⟨rfl, rfl⟩⟩
    rw [hset, Finset.card_pair]
    intro h
    exact hne (Prod.mk.injEq _ _ _ _ ▸ h).1
  rw [Finset.sum_congr rfl fun z hz => by rw [hfib z hz], Finset.sum_nsmul, nsmul_eq_mul,
    Nat.cast_ofNat]
  congr 1
  rw [← Sym2.filter_image_mk_not_isDiag, Finset.univ_product_univ]
  refine Finset.sum_subtype _ (fun z => ?_) (fun z => g z)
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  intro _
  obtain ⟨⟨a, b⟩, rfl⟩ := Quot.exists_rep z
  exact ⟨(a, b), rfl⟩

/-- The sum of `f u v` over the ordered pairs `u ≠ v` is the sum, over the unordered pairs
`{u, v}` of distinct vertices, of `f u v + f v u`. -/
private theorem fo5Aux_sum_lift {n : ℕ} (f : Fin n → Fin n → ℝ) :
    ∑ u, ∑ v, (if u ≠ v then f u v else 0) =
      ∑ z : OffDiag n, Sym2.lift ⟨fun u v => f u v + f v u, fun _ _ => add_comm _ _⟩ z.1 := by
  set g : Sym2 (Fin n) → ℝ := Sym2.lift ⟨fun u v => f u v + f v u, fun _ _ => add_comm _ _⟩
    with hg
  -- The sum of `f v u` over the pairs `u ≠ v` is the same sum.
  have h1 : ∑ u, ∑ v, (if u ≠ v then f v u else 0) = ∑ u, ∑ v, (if u ≠ v then f u v else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab, Ne.symm hab]
  have h2 : ∑ u, ∑ v, (if u ≠ v then f u v else 0) + ∑ u, ∑ v, (if u ≠ v then f v u else 0) =
      ∑ u, ∑ v, (if u ≠ v then g s(u, v) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hg, Sym2.lift_mk]
    split_ifs <;> simp
  have h3 := fo5Aux_sum_ite_ne (n := n) (fun q => g s(q.1, q.2))
  have h4 := fo5Aux_sum_offDiag g
  simp only at h3
  rw [h1] at h2
  linarith

/-! ### The weights of the light pairs -/

/-- The light weight of the ordered pair `(u, v)`: `xᵤ y_v` if `|xᵤ y_v| ≤ r`, and `0`
otherwise. -/
private def fo5Aux_c {n : ℕ} (r : ℝ) (x y : Fin n → ℝ) (u v : Fin n) : ℝ :=
  if |x u * y v| ≤ r then x u * y v else 0

/-- The weight of the unordered pair `{u, v}`: `a_{uv} = c(u, v) + c(v, u)`. -/
private def fo5Aux_a {n : ℕ} (r : ℝ) (x y : Fin n → ℝ) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun u v => fo5Aux_c r x y u v + fo5Aux_c r x y v u, fun _ _ => add_comm _ _⟩

private theorem fo5Aux_abs_c_le {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (x y : Fin n → ℝ) (u v : Fin n) :
    |fo5Aux_c r x y u v| ≤ r := by
  unfold fo5Aux_c
  split_ifs with h
  · exact h
  · simpa using hr

/-- `|a_{uv}| ≤ 2r`. -/
private theorem fo5Aux_abs_a_le {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (x y : Fin n → ℝ)
    (z : Sym2 (Fin n)) : |fo5Aux_a r x y z| ≤ 2 * r := by
  induction z using Sym2.ind with
  | h u v =>
    rw [fo5Aux_a, Sym2.lift_mk]
    have h1 := fo5Aux_abs_c_le hr x y u v
    have h2 := fo5Aux_abs_c_le hr x y v u
    calc |fo5Aux_c r x y u v + fo5Aux_c r x y v u|
        ≤ |fo5Aux_c r x y u v| + |fo5Aux_c r x y v u| := abs_add_le _ _
      _ ≤ 2 * r := by linarith

/-- `∑ a_{uv}² ≤ 2 ∑_{u ≠ v} xᵤ² y_v² ≤ 2` for `x, y` in the unit ball. -/
private theorem fo5Aux_sum_sq_a_le {n : ℕ} (r : ℝ) {x y : Fin n → ℝ} (hx : ∑ i, x i ^ 2 ≤ 1)
    (hy : ∑ i, y i ^ 2 ≤ 1) : ∑ z : OffDiag n, fo5Aux_a r x y z.1 ^ 2 ≤ 2 := by
  set b : Sym2 (Fin n) → ℝ := Sym2.lift ⟨fun u v => fo5Aux_c r x y u v ^ 2 +
    fo5Aux_c r x y v u ^ 2, fun _ _ => add_comm _ _⟩ with hb
  -- `(c + c')² ≤ 2 (c² + c'²)`
  have h1 : ∀ z : Sym2 (Fin n), fo5Aux_a r x y z ^ 2 ≤ 2 * b z := by
    refine Sym2.ind fun u v => ?_
    rw [fo5Aux_a, Sym2.lift_mk, hb, Sym2.lift_mk]
    nlinarith [sq_nonneg (fo5Aux_c r x y u v - fo5Aux_c r x y v u)]
  have h2 : ∑ u, ∑ v, (if u ≠ v then fo5Aux_c r x y u v ^ 2 else 0) = ∑ z : OffDiag n, b z.1 :=
    fo5Aux_sum_lift (fun u v => fo5Aux_c r x y u v ^ 2)
  have h3 : ∑ u, ∑ v, (if u ≠ v then fo5Aux_c r x y u v ^ 2 else 0) ≤
      ∑ u, ∑ v, x u ^ 2 * y v ^ 2 := by
    refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
    split_ifs
    · unfold fo5Aux_c
      split_ifs
      · rw [mul_pow]
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        positivity
    · positivity
  have h4 : ∑ u, ∑ v, x u ^ 2 * y v ^ 2 = (∑ u, x u ^ 2) * ∑ v, y v ^ 2 :=
    (Finset.sum_mul_sum _ _ _ _).symm
  have hx0 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  have hy0 : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (y i)
  have h5 : (∑ u, x u ^ 2) * ∑ v, y v ^ 2 ≤ 1 := by nlinarith
  calc ∑ z : OffDiag n, fo5Aux_a r x y z.1 ^ 2 ≤ ∑ z : OffDiag n, 2 * b z.1 :=
        Finset.sum_le_sum fun z _ => h1 z.1
    _ = 2 * ∑ z : OffDiag n, b z.1 := by rw [Finset.mul_sum]
    _ ≤ 2 := by linarith

/-! ### The light part as a weighted sum of the edge indicators -/

open Classical in
/-- For `u ≠ v`, the entry `(u, v)` of the adjacency matrix of `graphOfEdges ω` is the edge
indicator of `{u, v}`. -/
private theorem fo5Aux_adjMatrix {n : ℕ} {ω : EdgeVars n} {u v : Fin n} (huv : u ≠ v) :
    (graphOfEdges ω).adjMatrix ℝ u v = edgeInd s(u, v) ω := by
  unfold edgeInd
  rw [SimpleGraph.adjMatrix_apply]
  by_cases hω : ω s(u, v)
  · have hadj : (graphOfEdges ω).Adj u v := adj_graphOfEdges.mpr ⟨huv, hω⟩
    simp only [hω, hadj, ↓reduceIte]
  · have hadj : ¬ (graphOfEdges ω).Adj u v := fun h => hω (adj_graphOfEdges.mp h).2
    simp only [hω, hadj, ↓reduceIte]

/-- **Step 1.** The light part of `xᵀ (A − E A) y` is `∑_{u ≠ v unordered} a_{uv} (X_{uv} − p)`. -/
private theorem fo5Aux_lightSum_eq {n : ℕ} (p d : ℝ) (x y : Fin n → ℝ) (ω : EdgeVars n) :
    lightSum (graphOfEdges ω) p d x y =
      ∑ z : OffDiag n, fo5Aux_a (Real.sqrt d / n) x y z.1 * (edgeInd z.1 ω - p) := by
  have h1 : lightSum (graphOfEdges ω) p d x y =
      ∑ u, ∑ v, (if u ≠ v then
        fo5Aux_c (Real.sqrt d / n) x y u v * (edgeInd s(u, v) ω - p) else 0) := by
    unfold lightSum
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    by_cases huv : u = v
    · simp [huv]
    · rw [fo5Aux_adjMatrix huv]
      unfold fo5Aux_c
      by_cases hl : |x u * y v| ≤ Real.sqrt d / n
      · rw [ite_eq_left ⟨huv, hl⟩, ite_eq_left huv, ite_eq_left hl]
        ring
      · rw [ite_eq_right (fun h => hl h.2), ite_eq_left huv, ite_eq_right hl, zero_mul]
  have h2 : ∀ z : Sym2 (Fin n),
      Sym2.lift ⟨fun u v => fo5Aux_c (Real.sqrt d / n) x y u v * (edgeInd s(u, v) ω - p) +
        fo5Aux_c (Real.sqrt d / n) x y v u * (edgeInd s(v, u) ω - p), fun _ _ => add_comm _ _⟩ z
        = fo5Aux_a (Real.sqrt d / n) x y z * (edgeInd z ω - p) := by
    refine Sym2.ind fun u v => ?_
    rw [Sym2.lift_mk, fo5Aux_a, Sym2.lift_mk]
    dsimp only
    rw [Sym2.eq_swap (a := v) (b := u)]
    ring
  rw [h1, fo5Aux_sum_lift]
  exact Finset.sum_congr rfl fun z _ => h2 z.1

/-! ### One pair of points of the net -/

/-- **Steps 2 and 3.** For `x, y` in the unit ball, `P(|light| > 21 √(pn)) ≤ 2 e^(−10 n)`. -/
private theorem fo5Aux_pair {n : ℕ} {p : ℝ} (hn : 1 ≤ n) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {x y : Fin n → ℝ} (hx : ∑ i, x i ^ 2 ≤ 1) (hy : ∑ i, y i ^ 2 ≤ 1) :
    prob n p (fun G => 21 * Real.sqrt (p * n) < |lightSum G p (p * n) x y|) ≤
      2 * Real.exp (-(10 * n)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < p * n := mul_pos hp0 hnpos
  have hsd : 0 < Real.sqrt (p * n) := Real.sqrt_pos.mpr hd
  have hsq : Real.sqrt (p * n) ^ 2 = p * n := Real.sq_sqrt hd.le
  have hr0 : 0 ≤ Real.sqrt (p * n) / n := by positivity
  -- the weights and `θ = n / (2√d)`
  set a : OffDiag n → ℝ := fun z => fo5Aux_a (Real.sqrt (p * n) / n) x y z.1 with ha
  set θ : ℝ := n / (2 * Real.sqrt (p * n)) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθa : ∀ z ∈ (Finset.univ : Finset (OffDiag n)), θ * |a z| ≤ 1 := by
    intro z _
    have h := fo5Aux_abs_a_le hr0 x y z.1
    calc θ * |a z| ≤ θ * (2 * (Real.sqrt (p * n) / n)) := mul_le_mul_of_nonneg_left h hθ0
      _ = 1 := by
        rw [hθ]
        field_simp
  have hθa' : ∀ z ∈ (Finset.univ : Finset (OffDiag n)), θ * |(fun z => -a z) z| ≤ 1 := by
    intro z hz
    simpa only [abs_neg] using hθa z hz
  have hS : ∑ z, a z ^ 2 ≤ 2 := fo5Aux_sum_sq_a_le _ hx hy
  have hS' : ∑ z, (fun z => -a z) z ^ 2 ≤ 2 := by simpa only [neg_sq] using hS
  have hpθ : p * θ ^ 2 = n / 4 := by
    rw [hθ, div_pow, mul_pow, hsq]
    field_simp
    ring
  have hθt : θ * (21 * Real.sqrt (p * n)) = 21 * n / 2 := by
    rw [hθ]
    field_simp
  have hX := isBernoulliFamily_edgeInd (n := n) hp0.le hp1
  have h1 := hX.measureReal_le_sum_mul_le hp0.le hp1 Finset.univ a hθ0 hθa (21 * Real.sqrt (p * n))
  have h2 := hX.measureReal_le_sum_mul_le hp0.le hp1 Finset.univ (fun z => -a z) hθ0 hθa'
    (21 * Real.sqrt (p * n))
  have he1 : p * θ ^ 2 * ∑ z, a z ^ 2 - θ * (21 * Real.sqrt (p * n)) ≤ -(10 * n) := by
    rw [hpθ, hθt]
    nlinarith
  have he2 : p * θ ^ 2 * ∑ z, (fun z => -a z) z ^ 2 - θ * (21 * Real.sqrt (p * n)) ≤
      -(10 * n) := by
    rw [hpθ, hθt]
    nlinarith
  rw [prob_eq]
  calc (edgeLaw n p).real {ω | 21 * Real.sqrt (p * n) < |lightSum (graphOfEdges ω) p (p * n) x y|}
      ≤ (edgeLaw n p).real ({ω | 21 * Real.sqrt (p * n) ≤ ∑ z, a z * (edgeInd z.1 ω - p)} ∪
          {ω | 21 * Real.sqrt (p * n) ≤ ∑ z, (fun z => -a z) z * (edgeInd z.1 ω - p)}) := by
        refine measureReal_mono (fun ω hω => ?_)
        simp only [Set.mem_ofPred_eq] at hω
        rw [fo5Aux_lightSum_eq] at hω
        rcases lt_abs.mp hω with h | h
        · exact Or.inl h.le
        · right
          simp only [Set.mem_ofPred_eq, neg_mul, Finset.sum_neg_distrib]
          exact h.le
    _ ≤ (edgeLaw n p).real {ω | 21 * Real.sqrt (p * n) ≤ ∑ z, a z * (edgeInd z.1 ω - p)} +
          (edgeLaw n p).real
            {ω | 21 * Real.sqrt (p * n) ≤ ∑ z, (fun z => -a z) z * (edgeInd z.1 ω - p)} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-(10 * n)) + Real.exp (-(10 * n)) :=
        add_le_add (h1.trans (Real.exp_le_exp.mpr he1)) (h2.trans (Real.exp_le_exp.mpr he2))
    _ = 2 * Real.exp (-(10 * n)) := by ring

/-! ### The union bound over the net -/

/-- `1089 ≤ e⁷` (`e⁷ ≈ 1096.6`). -/
private theorem fo5Aux_e7 : (1089 : ℝ) ≤ Real.exp 7 := by
  have h := Real.exp_one_gt_d9
  have h7 : Real.exp 7 = Real.exp 1 ^ 7 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h7]
  calc (1089 : ℝ) ≤ 2.7182818283 ^ 7 := by norm_num
    _ ≤ Real.exp 1 ^ 7 := by gcongr

/-- **Step 4, the arithmetic.** `(33 e)^(2n) · 2 e^(−10 n) ≤ 2 e^(−n)`, as `(33 e)² ≤ e⁹`. -/
private theorem fo5Aux_final (n : ℕ) :
    (33 * Real.exp 1) ^ n * ((33 * Real.exp 1) ^ n * (2 * Real.exp (-(10 * n)))) ≤
      2 * Real.exp (-n) := by
  have h1 : (33 * Real.exp 1) ^ 2 ≤ Real.exp 9 := by
    have h9 : Real.exp 9 = Real.exp 7 * Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
    rw [h9, mul_pow]
    have h7 := fo5Aux_e7
    have h0 : 0 ≤ Real.exp 1 ^ 2 := by positivity
    nlinarith
  have h2 : (33 * Real.exp 1) ^ n * (33 * Real.exp 1) ^ n ≤ Real.exp 9 ^ n := by
    rw [← mul_pow, ← sq]
    exact pow_le_pow_left₀ (by positivity) h1 n
  have h3 : Real.exp 9 ^ n * Real.exp (-(10 * n)) = Real.exp (-n) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc (33 * Real.exp 1) ^ n * ((33 * Real.exp 1) ^ n * (2 * Real.exp (-(10 * n))))
      = 2 * ((33 * Real.exp 1) ^ n * (33 * Real.exp 1) ^ n * Real.exp (-(10 * n))) := by ring
    _ ≤ 2 * (Real.exp 9 ^ n * Real.exp (-(10 * n))) := by gcongr
    _ = 2 * Real.exp (-n) := by rw [h3]

/-- **Feige–Ofek, the light pairs.** With probability at least `1 − 2e^(−n)`, every pair `x, y` of
points of the grid net satisfies `|lightSum G p (pn) x y| ≤ 21 √(pn)`. -/
theorem lightSum_le {n : ℕ} {p : ℝ} (hn : 1 ≤ n) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    prob n p (fun G => ∃ x ∈ gridNet n, ∃ y ∈ gridNet n,
      21 * Real.sqrt (p * n) < |lightSum G p (p * n) x y|) ≤ 2 * Real.exp (-n) := by
  have hU := prob_exists_le (n := n) (p := p) (gridNet n)
    (fun x G => ∃ y ∈ gridNet n, 21 * Real.sqrt (p * n) < |lightSum G p (p * n) x y|)
  refine hU.trans ?_
  have hcard := card_gridNet_le n
  have hc0 : (0 : ℝ) ≤ (gridNet n).card := Nat.cast_nonneg _
  calc ∑ x ∈ gridNet n, prob n p
        (fun G => ∃ y ∈ gridNet n, 21 * Real.sqrt (p * n) < |lightSum G p (p * n) x y|)
      ≤ ∑ x ∈ gridNet n, ∑ y ∈ gridNet n,
          prob n p (fun G => 21 * Real.sqrt (p * n) < |lightSum G p (p * n) x y|) :=
        Finset.sum_le_sum fun x _ => prob_exists_le (gridNet n)
          (fun y G => 21 * Real.sqrt (p * n) < |lightSum G p (p * n) x y|)
    _ ≤ ∑ x ∈ gridNet n, ∑ y ∈ gridNet n, 2 * Real.exp (-(10 * n)) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy =>
          fo5Aux_pair hn hp0 hp1 (sum_sq_le_one_of_mem_gridNet hx)
            (sum_sq_le_one_of_mem_gridNet hy)
    _ = (gridNet n).card * ((gridNet n).card * (2 * Real.exp (-(10 * n)))) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (33 * Real.exp 1) ^ n * ((33 * Real.exp 1) ^ n * (2 * Real.exp (-(10 * n)))) := by
        gcongr
    _ ≤ 2 * Real.exp (-n) := fo5Aux_final n

end External.FeigeOfek
