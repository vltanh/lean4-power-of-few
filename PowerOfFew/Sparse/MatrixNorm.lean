module

public import PowerOfFew.Model.Gnp
public import PowerOfFew.External.RandomMatrix.RandomMatrix
public import PowerOfFew.External.FeigeOfek.FeigeOfek

/-!
# Sparse paper, Appendix A: the spectral norm of `A − E A`

Lemma A.7 of the sparse paper. The paper derives it from two cited results: Theorem 3.2 of
Benaych-Georges–Bordenave–Knowles for the expectation (`BBKTheorem3_2`) and Theorem 6.10 of
Boucheron–Lugosi–Massart for the concentration (`BLMTheorem6_10`). That derivation is formalized
here, with the two results as hypotheses (`lemmaA_7_of_bbk_blm`). The library proves Lemma A.7
itself by Feige and Ofek's argument (`lemmaA_7`, from `PowerOfFew.FeigeOfek.feigeOfek`), so no
result of the library assumes the two cited results.

Reading: the paper quotes the first with `d = p(1 − p)(n − 1)` and `η = √(log n)/min{√d, n^0.1}`;
the cited theorem has `d = p(n − 1)` (the maximal expected degree) and
`q = √d ∧ n^(1/10) κ^(-1/9)`, `κ = n/(n − 1)`. The difference only changes constants.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-! ### The spectral norm -/

/-- The spectral norm is at most the Frobenius norm (Cauchy–Schwarz, row by row). -/
private theorem appAux_specNorm_le_frobenius {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    specNorm M ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) := by
  unfold specNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  rw [← Real.sqrt_sq (norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) M x)),
    ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have : (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) M x) i = ∑ j, M i j * x j := by
    simp [Matrix.mulVec, dotProduct]
  rw [this]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

private theorem appAux_specNorm_add_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    specNorm (A + B) ≤ specNorm A + specNorm B := by
  unfold specNorm; rw [map_add]; exact norm_add_le _ _

private theorem appAux_specNorm_smul {n : ℕ} (r : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    specNorm (r • A) = |r| * specNorm A := by
  unfold specNorm; rw [map_smul, norm_smul, Real.norm_eq_abs]

private theorem appAux_abs_specNorm_sub_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    |specNorm A - specNorm B| ≤ specNorm (A - B) := by
  unfold specNorm; rw [map_sub]; exact abs_norm_sub_norm_le _ _

/-! ### The symmetric matrix of the edge variables -/

/-- The coordinates `x : Fin K → ℝ` of the pairs of distinct vertices (numbered by `e`), extended
by `0` to the diagonal. -/
private def appAux_ext {n K : ℕ} (e : OffDiag n ≃ Fin K) (x : Fin K → ℝ) (z : Sym2 (Fin n)) : ℝ :=
  if h : z.IsDiag then 0 else x (e ⟨z, h⟩)

/-- `Z(x)`: the symmetric matrix with zero diagonal whose `(u, v)` entry, `u ≠ v`, is the
coordinate of `x` at the pair `{u, v}`. -/
private def appAux_symMat {n K : ℕ} (e : OffDiag n ≃ Fin K) (x : Fin K → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun u v => appAux_ext e x s(u, v)

private theorem appAux_symMat_sub {n K : ℕ} (e : OffDiag n ≃ Fin K) (x y : Fin K → ℝ) :
    appAux_symMat e (x - y) = appAux_symMat e x - appAux_symMat e y := by
  ext u v
  simp only [appAux_symMat, appAux_ext, Matrix.of_apply, Matrix.sub_apply, Pi.sub_apply]
  split_ifs <;> simp

/-- Each pair of distinct vertices comes from exactly two ordered pairs. -/
private theorem appAux_sum_offDiag {n : ℕ} (g : Sym2 (Fin n) → ℝ) :
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

/-- `‖Z(x)‖_F² = 2 ∑ⱼ xⱼ²`: each coordinate appears twice in `Z(x)`. -/
private theorem appAux_frobenius_symMat {n K : ℕ} (e : OffDiag n ≃ Fin K) (x : Fin K → ℝ) :
    ∑ u, ∑ v, appAux_symMat e x u v ^ 2 = 2 * ∑ j, x j ^ 2 := by
  classical
  rw [← Finset.sum_product' (f := fun u v => appAux_symMat e x u v ^ 2),
    ← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag _)]
  have hdiag : ∑ y ∈ (Finset.univ : Finset (Fin n)).diag, appAux_symMat e x y.1 y.2 ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun y hy => ?_
    have hy' : y.1 = y.2 := (Finset.mem_diag.mp hy).2
    simp [appAux_symMat, appAux_ext, hy']
  rw [hdiag, zero_add]
  have := appAux_sum_offDiag (n := n) (fun z => appAux_ext e x z ^ 2)
  simp only [appAux_symMat, Matrix.of_apply]
  rw [this]
  congr 1
  rw [← e.sum_comp (fun j => x j ^ 2)]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [appAux_ext, z.2]

/-! ### The function of the concentration step -/

/-- `f(x) = 2^(−1/2) ‖Z(x) − E A‖`, the function to which the paper applies Theorem 6.10 of
Boucheron–Lugosi–Massart. -/
private def appAux_f {n K : ℕ} (e : OffDiag n ≃ Fin K) (p : ℝ) (x : Fin K → ℝ) : ℝ :=
  (Real.sqrt 2)⁻¹ * specNorm (appAux_symMat e x - meanAdj n p)

/-- `f` is separately convex: it is a norm of an affine function of each coordinate. -/
private theorem appAux_f_convex {n K : ℕ} (e : OffDiag n ≃ Fin K) (p : ℝ) (x : Fin K → ℝ)
    (i : Fin K) : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) fun s => appAux_f e p (Function.update x i s) := by
  refine ⟨convex_Icc 0 1, fun s₁ _ s₂ _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, appAux_f]
  set y := Function.update x i s₁
  set z := Function.update x i s₂
  have hupd : Function.update x i (a * s₁ + b * s₂) = a • y + b • z := by
    ext j
    by_cases hj : j = i
    · subst hj; simp [y, z]
    · simp only [y, z, Function.update_of_ne hj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← add_mul, hab, one_mul]
  have hmat : appAux_symMat e (a • y + b • z) - meanAdj n p =
      a • (appAux_symMat e y - meanAdj n p) + b • (appAux_symMat e z - meanAdj n p) := by
    ext u v
    simp only [appAux_symMat, appAux_ext, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
    have hm : meanAdj n p u v = a * meanAdj n p u v + b * meanAdj n p u v := by
      rw [← add_mul, hab, one_mul]
    split_ifs <;> linarith
  rw [hupd, hmat]
  have h1 := appAux_specNorm_add_le (a • (appAux_symMat e y - meanAdj n p))
    (b • (appAux_symMat e z - meanAdj n p))
  rw [appAux_specNorm_smul, appAux_specNorm_smul, abs_of_nonneg ha, abs_of_nonneg hb] at h1
  have h2 : 0 ≤ (Real.sqrt 2)⁻¹ := by positivity
  calc (Real.sqrt 2)⁻¹ * specNorm (a • (appAux_symMat e y - meanAdj n p) +
        b • (appAux_symMat e z - meanAdj n p))
      ≤ (Real.sqrt 2)⁻¹ * (a * specNorm (appAux_symMat e y - meanAdj n p) +
          b * specNorm (appAux_symMat e z - meanAdj n p)) := mul_le_mul_of_nonneg_left h1 h2
    _ = a * ((Real.sqrt 2)⁻¹ * specNorm (appAux_symMat e y - meanAdj n p)) +
          b * ((Real.sqrt 2)⁻¹ * specNorm (appAux_symMat e z - meanAdj n p)) := by ring

/-- `f` is `1`-Lipschitz: `‖Z(x) − Z(y)‖ ≤ ‖Z(x − y)‖_F = √2 ‖x − y‖`. -/
private theorem appAux_f_lipschitz {n K : ℕ} (e : OffDiag n ≃ Fin K) (p : ℝ)
    (x y : Fin K → ℝ) :
    |appAux_f e p x - appAux_f e p y| ≤ Real.sqrt (∑ j, (x j - y j) ^ 2) := by
  unfold appAux_f
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hs2)]
  have h1 := appAux_abs_specNorm_sub_le (appAux_symMat e x - meanAdj n p)
    (appAux_symMat e y - meanAdj n p)
  rw [sub_sub_sub_cancel_right, ← appAux_symMat_sub] at h1
  have h2 := appAux_specNorm_le_frobenius (appAux_symMat e (x - y))
  rw [appAux_frobenius_symMat, Real.sqrt_mul (by norm_num)] at h2
  simp only [Pi.sub_apply] at h2
  calc (Real.sqrt 2)⁻¹ * |specNorm (appAux_symMat e x - meanAdj n p) -
        specNorm (appAux_symMat e y - meanAdj n p)|
      ≤ (Real.sqrt 2)⁻¹ * (Real.sqrt 2 * Real.sqrt (∑ j, (x j - y j) ^ 2)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = Real.sqrt (∑ j, (x j - y j) ^ 2) := by field_simp

/-- `Z` evaluated at the edge indicators is the adjacency matrix. -/
private theorem appAux_symMat_edgeInd {n K : ℕ} (e : OffDiag n ≃ Fin K) (ω : EdgeVars n) :
    appAux_symMat e (fun j => edgeInd (e.symm j).1 ω) = adjMat (graphOfEdges ω) := by
  ext u v
  simp only [appAux_symMat, appAux_ext, Matrix.of_apply, adjMat]
  by_cases huv : u = v
  · subst huv
    simp
  · have hd : ¬ (s(u, v)).IsDiag := Sym2.mk_isDiag_iff.not.mpr huv
    simp only [hd, ↓reduceDIte, Equiv.symm_apply_apply]
    unfold edgeInd
    by_cases hω : ω s(u, v)
    · have hadj : (graphOfEdges ω).Adj u v := adj_graphOfEdges.mpr ⟨huv, hω⟩
      simp only [hω, hadj, ↓reduceIte]
    · have hadj : ¬ (graphOfEdges ω).Adj u v := fun h => hω (adj_graphOfEdges.mp h).2
      simp only [hω, hadj, ↓reduceIte]

/-! ### The three steps of the proof of Lemma A.7 -/

/-- Small `n`: `‖A − E A‖ ≤ ‖A − E A‖_F ≤ n`, as the entries of `A − E A` lie in `[−1, 1]`. -/
private theorem appAux_specNorm_le_card {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (G : SimpleGraph (Fin n)) : specNorm (adjMat G - meanAdj n p) ≤ n := by
  have hentry : ∀ u v, (adjMat G - meanAdj n p) u v ^ 2 ≤ 1 := by
    intro u v
    simp only [Matrix.sub_apply, adjMat, meanAdj, Matrix.of_apply]
    split_ifs <;> nlinarith
  have h2 : ∑ u, ∑ v, (adjMat G - meanAdj n p) u v ^ 2 ≤ (n : ℝ) ^ 2 := by
    calc ∑ u, ∑ v, (adjMat G - meanAdj n p) u v ^ 2
        ≤ ∑ _u : Fin n, ∑ _v : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hentry u v
      _ = (n : ℝ) ^ 2 := by simp [sq]
  refine (appAux_specNorm_le_frobenius _).trans ?_
  rw [← Real.sqrt_sq (Nat.cast_nonneg n)]
  exact Real.sqrt_le_sqrt h2

/-- The parameters of Theorem 3.2 of BBK for `G(n, p)` with `pn ≥ c log n`, `n ≥ 1024` and
`log n ≥ 2/c`: `q ≥ 1`, and `η = √(log n)/q ≤ √(2/c) + 5` (if `q = √d`, `η² = log n / d ≤ 2/c`;
if `q = n^(1/10) κ^(−1/9) ≥ n^(1/10)/2`, then `η ≤ 2√5` as `log n ≤ 5 n^(1/5)`). -/
private theorem appAux_bbk_params {c : ℝ} (hc : 0 < c) {n : ℕ} {p : ℝ} (hp0 : 0 < p)
    (hpn : c * Real.log n ≤ p * n) (hp1 : p ≤ 1) (hn : (1024 : ℝ) ≤ n)
    (hlogn : 2 / c ≤ Real.log n) :
    1 ≤ min (Real.sqrt (p * (n - 1))) ((n : ℝ) ^ (1 / 10 : ℝ) * (p / (p * (n - 1) / n)) ^
        (-(1 / 9 : ℝ))) ∧
      Real.sqrt (Real.log n) / min (Real.sqrt (p * (n - 1))) ((n : ℝ) ^ (1 / 10 : ℝ) *
        (p / (p * (n - 1) / n)) ^ (-(1 / 9 : ℝ))) ≤ Real.sqrt (2 / c) + 5 := by
  have hnpos : (0 : ℝ) < n := by linarith
  have hclog : 2 ≤ c * Real.log n := by
    rw [div_le_iff₀ hc] at hlogn
    linarith
  have hd1 : 1 ≤ p * (n - 1) := by nlinarith
  have hd2 : p * n ≤ 2 * (p * (n - 1)) := by nlinarith
  have hκ_eq : p / (p * (n - 1) / n) = n / (n - 1) := by
    have : (n : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  rw [hκ_eq]
  have hκ1 : 1 ≤ (n : ℝ) / (n - 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hκ2 : (n : ℝ) / (n - 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hn10 : 2 ≤ (n : ℝ) ^ (1 / 10 : ℝ) := by
    have h10 : (1 / 10 : ℝ) = (10 : ℝ)⁻¹ := by norm_num
    have h1024 : (2 : ℝ) ^ (10 : ℝ) = 1024 := by
      rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    rw [h10, Real.le_rpow_inv_iff_of_pos (by norm_num) hnpos.le (by norm_num), h1024]
    exact hn
  have hκ9 : 1 / 2 ≤ ((n : ℝ) / (n - 1)) ^ (-(1 / 9 : ℝ)) := by
    rw [Real.rpow_neg (by linarith)]
    have h1 : ((n : ℝ) / (n - 1)) ^ (1 / 9 : ℝ) ≤ 2 :=
      (Real.rpow_le_rpow_of_exponent_le hκ1 (by norm_num : (1 / 9 : ℝ) ≤ 1)).trans
        (by rw [Real.rpow_one]; exact hκ2)
    have h2 : 0 < ((n : ℝ) / (n - 1)) ^ (1 / 9 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    rw [one_div]
    exact inv_anti₀ h2 h1
  have hq₂half : (n : ℝ) ^ (1 / 10 : ℝ) / 2 ≤
      (n : ℝ) ^ (1 / 10 : ℝ) * ((n : ℝ) / (n - 1)) ^ (-(1 / 9 : ℝ)) := by
    have := Real.rpow_nonneg hnpos.le (1 / 10 : ℝ)
    nlinarith
  have hsqd : 1 ≤ Real.sqrt (p * (n - 1)) := Real.one_le_sqrt.mpr hd1
  refine ⟨le_min hsqd (by linarith), ?_⟩
  rcases min_cases (Real.sqrt (p * (n - 1)))
      ((n : ℝ) ^ (1 / 10 : ℝ) * ((n : ℝ) / (n - 1)) ^ (-(1 / 9 : ℝ))) with ⟨hqd, _⟩ | ⟨hqq, _⟩
  · -- `q = √d`: `η² = log n / d ≤ 2/c`.
    rw [hqd]
    have hle : Real.sqrt (Real.log n) / Real.sqrt (p * (n - 1)) ≤ Real.sqrt (2 / c) := by
      rw [div_le_iff₀ (by linarith), ← Real.sqrt_mul (by positivity)]
      apply Real.sqrt_le_sqrt
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      nlinarith
    linarith
  · -- `q = n^(1/10) κ^(−1/9) ≥ n^(1/10)/2` and `log n ≤ 5 n^(1/5)`: `η ≤ 2√5 ≤ 5`.
    rw [hqq]
    have hlog5 : Real.log n ≤ 5 * (n : ℝ) ^ (1 / 5 : ℝ) := by
      have := Real.log_le_rpow_div hnpos.le (by norm_num : (0 : ℝ) < 1 / 5)
      linarith [show (n : ℝ) ^ (1 / 5 : ℝ) / (1 / 5) = 5 * (n : ℝ) ^ (1 / 5 : ℝ) by ring]
    have hsq : Real.sqrt ((n : ℝ) ^ (1 / 5 : ℝ)) = (n : ℝ) ^ (1 / 10 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hnpos.le]
      norm_num
    have hsqrt : Real.sqrt (Real.log n) ≤ Real.sqrt 5 * (n : ℝ) ^ (1 / 10 : ℝ) := by
      rw [← hsq, ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt hlog5
    have hs5 : Real.sqrt 5 ≤ 5 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have hle : Real.sqrt (Real.log n) /
        ((n : ℝ) ^ (1 / 10 : ℝ) * ((n : ℝ) / (n - 1)) ^ (-(1 / 9 : ℝ))) ≤ 5 := by
      rw [div_le_iff₀ (by linarith)]
      have := Real.rpow_nonneg hnpos.le (1 / 10 : ℝ)
      nlinarith
    have : 0 ≤ Real.sqrt (2 / c) := Real.sqrt_nonneg _
    linarith

/-- The arithmetic after Theorem 3.2 of BBK: `E/√d ≤ 2 + Cη/√(1 ∨ log η)` with `0 ≤ η ≤ M` and
`d ≤ pn` give `E ≤ (2 + C M)√(pn)`. -/
private theorem appAux_expectation_arith {E d η M CB x : ℝ} (hCB : 0 < CB) (hd : 0 < d)
    (hdx : d ≤ x) (hη0 : 0 ≤ η) (hηM : η ≤ M)
    (hB : E / Real.sqrt d ≤ 2 + CB * η / Real.sqrt (max 1 (Real.log η))) :
    E ≤ (2 + CB * M) * Real.sqrt x := by
  have hsqd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have h1 : CB * η / Real.sqrt (max 1 (Real.log η)) ≤ CB * η :=
    div_le_self (by positivity) (Real.one_le_sqrt.mpr (le_max_left _ _))
  have h2 : CB * η ≤ CB * M := mul_le_mul_of_nonneg_left hηM hCB.le
  rw [div_le_iff₀ hsqd] at hB
  have h3 : E ≤ (2 + CB * M) * Real.sqrt d := by nlinarith
  have h4 : Real.sqrt d ≤ Real.sqrt x := Real.sqrt_le_sqrt hdx
  have h5 : 0 ≤ 2 + CB * M := by nlinarith
  nlinarith

/-- **The concentration step** (Theorem 6.10 of BLM, as the paper applies it): for the convex
`1`-Lipschitz function `f(x) = 2^(−1/2) ‖Z(x) − E A‖` of the `n(n − 1)/2` edge indicators,
`P(‖A − E A‖ > E‖A − E A‖ + √2 t) ≤ e^(−t²/2)`. -/
private theorem appAux_concentration (hBLM : BLMTheorem6_10) {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) {t : ℝ} (ht : 0 < t) :
    (edgeLaw n p).real {ω | gnpExp n p (fun G => specNorm (adjMat G - meanAdj n p)) +
        Real.sqrt 2 * t < specNorm (adjMat (graphOfEdges ω) - meanAdj n p)} ≤
      Real.exp (-t ^ 2 / 2) := by
  obtain ⟨K, ⟨e⟩⟩ : ∃ K : ℕ, Nonempty (OffDiag n ≃ Fin K) := ⟨_, ⟨Fintype.equivFin _⟩⟩
  have hBern := (isBernoulliFamily_edgeInd (n := n) hp0 hp1).comp e.symm.injective
  have hconc := hBLM (EdgeVars n) (edgeLaw n p) K (fun j => edgeInd (e.symm j).1) (appAux_f e p)
    hBern.measurable hBern.indep
    (fun j ω => by
      rcases hBern.zero_or_one j ω with h | h <;> simp only [h] <;> norm_num)
    (fun x i _ => appAux_f_convex e p x i) (fun x y _ _ => appAux_f_lipschitz e p x y) t ht
  have hfX : ∀ ω, appAux_f e p (fun j => edgeInd (e.symm j).1 ω) =
      (Real.sqrt 2)⁻¹ * specNorm (adjMat (graphOfEdges ω) - meanAdj n p) := by
    intro ω
    simp only [appAux_f, appAux_symMat_edgeInd]
  have hEf : ∫ ω, appAux_f e p (fun j => edgeInd (e.symm j).1 ω) ∂(edgeLaw n p) =
      (Real.sqrt 2)⁻¹ * gnpExp n p (fun G => specNorm (adjMat G - meanAdj n p)) := by
    simp_rw [hfX]
    rw [integral_const_mul, gnpExp_eq]
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  refine le_trans (measureReal_mono fun ω hω => ?_) hconc
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [hEf, hfX]
  have h3 : (Real.sqrt 2)⁻¹ * gnpExp n p (fun G => specNorm (adjMat G - meanAdj n p)) + t =
      (Real.sqrt 2)⁻¹ * (gnpExp n p (fun G => specNorm (adjMat G - meanAdj n p)) +
        Real.sqrt 2 * t) := by
    field_simp
  rw [h3]
  exact mul_lt_mul_of_pos_left hω (inv_pos.mpr hs2)

/-- **The paper's proof of Lemma A.7**, from its two cited results as hypotheses: if Theorem 3.2
of Benaych-Georges–Bordenave–Knowles and Theorem 6.10 of Boucheron–Lugosi–Massart hold, then
for `c, a > 0` and `pn ≥ c log n`, with probability at least `1 − n^(−a)`,
`‖A − E A‖_op ≤ C_{c,a} √(pn)`. The library's `lemmaA_7` is proved by Feige and Ofek's argument
instead; this theorem checks the paper's derivation.

Proof (the paper's): Theorem 3.2 of BBK bounds `E‖A − E A‖ ≤ (2 + Cη)√d ≤ (2 + C M_c)√(pn)`,
and Theorem 6.10 of BLM for the convex `1`-Lipschitz function `x ↦ 2^(−1/2) ‖Z(x) − E A‖` of the
`n(n − 1)/2` edge indicators (`Z(x)` the symmetric matrix with zero diagonal and entries `x`)
gives `P(‖A − E A‖ > E‖A − E A‖ + √2 t) ≤ e^(−t²/2)`, i.e. the paper's `e^(−t'²/4)` with
`t' = √2 t`.

Departures from the paper (minimal repairs):
* the paper takes `t' = 2√(apn)`, which gives `e^(−apn) ≤ n^(−a)` only when `pn ≥ log n`, i.e.
  `c ≥ 1`. Here `t' = 2√(a log n) ≤ 2√(a/c) √(pn)`, so `C_{c,a} = 2 + C M_c + 2√(a/c)`;
* the paper's `η ≤ c^(−1/2)` ignores the branch `n^(1/10) κ^(−1/9)` of the minimum `q` (and the
  factor `(n − 1)/n` in `d`): here `η ≤ M_c = √(2/c) + 5` (`appAux_bbk_params`);
* Theorem 3.2 of BBK needs `q ≥ 1`, which holds for `n ≥ N(c) = max(1024, ⌈e^(2/c)⌉)`; for
  `2 ≤ n < N(c)`, `‖A − E A‖ ≤ ‖A − E A‖_F ≤ n` and `√(pn) ≥ √(c log 2)`, so the constant
  `N(c)/√(c log 2)` covers these `n` (and `n ≤ 1` is trivial). -/
theorem lemmaA_7_of_bbk_blm (hBBK : BBKTheorem3_2) (hBLM : BLMTheorem6_10) {c a : ℝ}
    (hc : 0 < c) (ha : 0 < a) :
    ∃ C : ℝ, ∀ (n : ℕ) (p : ℝ), 0 < p → p ≤ 1 → c * Real.log n ≤ p * n →
      1 - (n : ℝ) ^ (-a) ≤
        gnpProb n p (fun G => specNorm (adjMat G - meanAdj n p) ≤ C * Real.sqrt (p * n)) := by
  obtain ⟨CB, hCB, hBBK⟩ := hBBK
  -- The threshold `N(c)` from which Theorem 3.2 of BBK applies, and the two constants.
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, N₀ = max 1024 ⌈Real.exp (2 / c)⌉₊ := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 2 + CB * (Real.sqrt (2 / c) + 5) + 2 * Real.sqrt (a / c) :=
    ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = N₀ / Real.sqrt (c * Real.log 2) := ⟨_, rfl⟩
  refine ⟨max C₁ C₂, fun n p hp0 hp1 hpn => ?_⟩
  have hsure : (∀ G : SimpleGraph (Fin n),
      specNorm (adjMat G - meanAdj n p) ≤ max C₁ C₂ * Real.sqrt (p * n)) →
      1 - (n : ℝ) ^ (-a) ≤
        gnpProb n p (fun G => specNorm (adjMat G - meanAdj n p) ≤
          max C₁ C₂ * Real.sqrt (p * n)) := by
    intro h
    have h1 := gnpProb_mono (n := n) (p := p) (P := fun _ => True) (fun G _ => h G)
    rw [gnpProb_true] at h1
    have : 0 ≤ (n : ℝ) ^ (-a) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    linarith
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · -- `n ≤ 1`
    interval_cases n
    · apply hsure
      intro G
      have h := appAux_specNorm_le_card hp0.le hp1 G
      simpa using h
    · simp only [Nat.cast_one, Real.one_rpow, sub_self]
      exact gnpProb_nonneg _
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := by linarith
  rcases Nat.lt_or_ge n N₀ with hnN | hnN
  · -- `2 ≤ n < N(c)`: `‖A − E A‖ ≤ n < N(c) ≤ C₂ √(pn)`, surely.
    apply hsure
    intro G
    have hlog2 : c * Real.log 2 ≤ p * n :=
      (mul_le_mul_of_nonneg_left (Real.log_le_log two_pos hn2') hc.le).trans hpn
    have hpos : 0 < Real.sqrt (c * Real.log 2) :=
      Real.sqrt_pos.mpr (mul_pos hc (Real.log_pos one_lt_two))
    have h4 : (N₀ : ℝ) ≤ C₂ * Real.sqrt (p * n) := by
      rw [hC₂, div_mul_eq_mul_div, le_div_iff₀ hpos]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlog2) (Nat.cast_nonneg _)
    calc specNorm (adjMat G - meanAdj n p) ≤ n := appAux_specNorm_le_card hp0.le hp1 G
      _ ≤ N₀ := by exact_mod_cast hnN.le
      _ ≤ C₂ * Real.sqrt (p * n) := h4
      _ ≤ max C₁ C₂ * Real.sqrt (p * n) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
  -- `n ≥ N(c)`.
  have hn : (N₀ : ℝ) ≤ n := by exact_mod_cast hnN
  have hN1 : (1024 : ℝ) ≤ N₀ := by
    rw [hN₀]
    exact_mod_cast le_max_left 1024 ⌈Real.exp (2 / c)⌉₊
  have hN2 : Real.exp (2 / c) ≤ N₀ := by
    refine (Nat.le_ceil _).trans ?_
    rw [hN₀]
    exact_mod_cast le_max_right 1024 ⌈Real.exp (2 / c)⌉₊
  have hlogn : 2 / c ≤ Real.log n := by
    rw [← Real.log_exp (2 / c)]
    exact Real.log_le_log (Real.exp_pos _) (hN2.trans hn)
  have hlogpos : 0 < Real.log n := lt_of_lt_of_le (by positivity) hlogn
  -- Theorem 3.2 of BBK: `E‖A − E A‖ ≤ (2 + C M_c)√(pn)`.
  obtain ⟨hq1, hηM⟩ := appAux_bbk_params hc hp0 hpn hp1 (hN1.trans hn) hlogn
  have hB := hBBK n p hp0 hp1 hq1
  have hd0 : 0 < p * ((n : ℝ) - 1) := by nlinarith
  have hdx : p * ((n : ℝ) - 1) ≤ p * n := by nlinarith
  have hη0 : 0 ≤ Real.sqrt (Real.log n) / min (Real.sqrt (p * (n - 1)))
      ((n : ℝ) ^ (1 / 10 : ℝ) * (p / (p * (n - 1) / n)) ^ (-(1 / 9 : ℝ))) :=
    div_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hE : gnpExp n p (fun G => specNorm (adjMat G - meanAdj n p)) ≤
      (2 + CB * (Real.sqrt (2 / c) + 5)) * Real.sqrt (p * n) :=
    appAux_expectation_arith hCB hd0 hdx hη0 hηM hB
  -- Theorem 6.10 of BLM with `t = √(2a log n)`: `√2 t = 2√(a log n) ≤ 2√(a/c) √(pn)`.
  have ht : 0 < Real.sqrt (2 * a * Real.log n) := Real.sqrt_pos.mpr (by positivity)
  have hconc := appAux_concentration (n := n) hBLM hp0.le hp1 ht
  have hst : Real.sqrt 2 * Real.sqrt (2 * a * Real.log n) ≤
      2 * Real.sqrt (a / c) * Real.sqrt (p * n) := by
    have h1 : Real.sqrt 2 * Real.sqrt (2 * a * Real.log n) = 2 * Real.sqrt (a * Real.log n) := by
      rw [← Real.sqrt_mul (by norm_num),
        show 2 * (2 * a * Real.log n) = 2 ^ 2 * (a * Real.log n) by ring,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [h1, mul_assoc, ← Real.sqrt_mul (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.sqrt_le_sqrt
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith
  apply le_gnpProb_of_not_le
  rw [gnpProb_eq]
  refine le_trans (measureReal_mono fun ω hω => ?_) (hconc.trans (le_of_eq ?_))
  · simp only [Set.mem_ofPred_eq, not_le] at hω ⊢
    have h1 : C₁ * Real.sqrt (p * n) ≤ max C₁ C₂ * Real.sqrt (p * n) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    have h2 : C₁ * Real.sqrt (p * n) = (2 + CB * (Real.sqrt (2 / c) + 5)) * Real.sqrt (p * n) +
        2 * Real.sqrt (a / c) * Real.sqrt (p * n) := by
      rw [hC₁]; ring
    linarith
  · rw [Real.sq_sqrt (by positivity), Real.rpow_def_of_pos hnpos]
    congr 1
    ring

/-- **Lemma A.7** (`S:lem:matrix-norm-bound`). Let `c, a > 0` be constants and assume
`pn ≥ c log n`. With probability at least `1 − n^(−a)`, the adjacency matrix `A` of
`G ∼ G(n, p)` satisfies `‖A − E A‖_op ≤ C_{c,a} √(pn)`, for a constant `C_{c,a}` depending only
on `c` and `a`.

Departure from the paper (the whole argument, at the author's request): the paper derives the
bound from Theorem 3.2 of Benaych-Georges–Bordenave–Knowles (the expectation) and Theorem 6.10 of
Boucheron–Lugosi–Massart (Talagrand's concentration inequality); that derivation is
`lemmaA_7_of_bbk_blm`, with the two results as hypotheses. Their proofs need mathematics that Lean
lacks (a moment method for the non-backtracking matrix with an Ihara–Bass type formula; the entropy
method for separately convex Lipschitz functions), so the formalization proves the bound by Feige
and Ofek's argument (`PowerOfFew.FeigeOfek.feigeOfek`: a net of the unit ball, the light pairs by
an exponential-moment bound, the heavy pairs by bounded degrees and discrepancy, all from Chernoff
bounds). -/
theorem lemmaA_7 {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ∃ C : ℝ, ∀ (n : ℕ) (p : ℝ), 0 < p → p ≤ 1 → c * Real.log n ≤ p * n →
      1 - (n : ℝ) ^ (-a) ≤
        gnpProb n p (fun G => specNorm (adjMat G - meanAdj n p) ≤ C * Real.sqrt (p * n)) :=
  FeigeOfek.feigeOfek hc ha

end PowerOfFew.Sparse

end
