module

public import PowerOfFew.Model.Gnp
public import PowerOfFew.Model.Majority
public import PowerOfFew.Model.EdgeConditioning
public import Basic.Combinatorics.Choose
public import Basic.Analysis.SpecialFunctions.CubeRoot

/-!
# Sparse paper, Section 2.3: Step 2, the second day

Lemmas 2.3 and 2.4 of the sparse paper.

Corrections and deviations (recorded in `REPORT.md`):

* The paper defines `F(d, x, y) = dx(1 − y/2 − (3/2) y^(1/3)(1 − y)^(2/3)) + 2h(x)`, but its proof
  of Lemma 2.3 ends with `2h` of the *source* fraction (the second argument), and Lemma 2.4
  expands `F(pn, b, b₁)` with `2h(b₁)`. The definition here, `F d x y = … + 2 h y`, is that
  reading (an obvious misprint).
* Lemma 2.3 assumes `b₁ ≤ 1/2 − 7/n`, but its proof uses `b₁ ≤ 1/2 − 2/√n` ("by hypothesis") and
  `n` large enough (`n ≥ 163` makes its case `x < 1/9` work). The statement takes those
  hypotheses; Lemma 2.4 inherits them as `2√p ≤ a` and `b ≤ b₁` (decision of the user: state the
  hypotheses the paper's argument uses).

Proofs. Lemma 2.3 follows the paper's Chernoff argument step by step (`x = b₁`, `y = b₂`): for
`|B| = ⌊xn⌋` and `|S| = ⌊yn⌋ + 1`, `S` Blue tomorrow implies `δ(S) ≤ 0`, where
`δ(S) = ∑_{v ∈ S} δ(v) = ∑_{\{u, v\}} X(u, v) 1_{u ∼ v}` (`sparseAux_delta_eq`); then
`P(δ(S) ≤ 0) ≤ E e^{−tδ(S)} ≤ exp(p ∑ (e^{−tX(u,v)} − 1))` (`sparseAux_prob_subset_le`), the sum
is `(1 − e^{−t}) f(|S ∩ R|)` (Table 1, `sparseAux_sum_exp_X`), `f ≤ T` for a nice `t`
(`sparseAux_f_le_T`), `t_x = log(1/x − 1)/3` is nice (`sparseAux_tx_nice`) with
`g_x(t_x) = −(1 − x/2 − (3/2) x^(1/3) (1 − x)^(2/3))` (`sparseAux_g_tx`), and a double union bound
with `C(n, k) ≤ e^{−n h(k/n)}`. Two small repairs, both documented at the helper concerned:
`T − f(0)` has an extra nonnegative term `(xn − ⌊xn⌋) e^t` that the paper's formula omits, and the
case `x ≥ 1/9` of the niceness of `t_x` needs `2x(e^{2t_x} + e^{t_x} + 1)² ≤ 98/9 < 16` (the
paper's bounds `e^{t_x} ≤ 2`, `2x ≤ 1` only give `49`, and it then writes `7`). Lemma 2.4 is Lemma
2.3 with `b₂ = b` and `b₁ = 1/2 − a/√(pn)`, the "routine Taylor expansion"
(`Real.one_sub_two_mul_sq_div_three_le`) and `h ≥ −log 2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Sparse

/-- `h(x) = x log x + (1 − x) log(1 − x)` (sparse paper, equation (5)). -/
def h (x : ℝ) : ℝ := x * Real.log x + (1 - x) * Real.log (1 - x)

/-- `F(d, x, y) = d x (1 − y/2 − (3/2) y^(1/3) (1 − y)^(2/3)) + 2 h(y)`: the paper's equation (6),
with `2h(y)` (the source fraction) in place of the printed `2h(x)`, as its proof and Lemma 2.4
use. -/
def F (d x y : ℝ) : ℝ :=
  d * x * (1 - y / 2 - 3 / 2 * y ^ (1 / 3 : ℝ) * (1 - y) ^ (2 / 3 : ℝ)) + 2 * h y

/-! ### Helpers for the proof of Lemma 2.3 -/

/-- The unordered pairs of distinct vertices, as a `Finset`. -/
abbrev sparseAux_offDiag (n : ℕ) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter fun e => ¬ e.IsDiag

/-- Summing a symmetric function over the unordered pairs of distinct vertices counts each pair
once; over the ordered pairs `(a, b)`, `a ≠ b`, it counts each pair twice. -/
theorem sparseAux_two_mul_sum_offDiag {n : ℕ} (φ : Fin n → Fin n → ℝ)
    (hφ : ∀ a b, φ a b = φ b a) (ψ : Sym2 (Fin n) → ℝ) (hψ : ∀ a b, ψ s(a, b) = φ a b) :
    2 * ∑ e ∈ sparseAux_offDiag n, ψ e = ∑ a, ∑ b, if a = b then 0 else φ a b := by
  classical
  have h1 : ∑ e ∈ sparseAux_offDiag n, ψ e =
      ∑ i ∈ (Finset.univ : Finset (Fin n)).offDiag with i.1 < i.2, φ i.1 i.2 := by
    rw [sparseAux_offDiag, ← Finset.sym2_univ, Finset.sum_sym2_filter_not_isDiag]
    simp only [hψ]
  have h2 : ∑ a, ∑ b, (if a = b then 0 else φ a b) =
      ∑ i ∈ (Finset.univ : Finset (Fin n)).offDiag, φ i.1 i.2 := by
    have hoff : (Finset.univ : Finset (Fin n)).offDiag =
        (Finset.univ ×ˢ Finset.univ).filter fun i : Fin n × Fin n => i.1 ≠ i.2 := by
      ext i; simp [Finset.mem_offDiag]
    rw [← Finset.sum_product' (f := fun a b => if a = b then 0 else φ a b), hoff,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i.1 = i.2 <;> simp [h]
  have h3 : ∑ i ∈ (Finset.univ : Finset (Fin n)).offDiag with ¬ i.1 < i.2, φ i.1 i.2 =
      ∑ i ∈ (Finset.univ : Finset (Fin n)).offDiag with i.1 < i.2, φ i.1 i.2 := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and, not_lt,
        Prod.fst_swap, Prod.snd_swap] at hi ⊢
      exact ⟨fun h => hi.1 h.symm, lt_of_le_of_ne hi.2 (fun h => hi.1 h.symm)⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and, not_lt,
        Prod.fst_swap, Prod.snd_swap] at hi ⊢
      exact ⟨fun h => hi.1 h.symm, hi.2.le⟩
    · intro i _
      simp only [Prod.fst_swap, Prod.snd_swap]
      exact hφ _ _
  rw [h1, h2, ← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n)).offDiag
    (fun i : Fin n × Fin n => i.1 < i.2) (fun i => φ i.1 i.2), h3]
  ring

/-- The colour sign `ℓ(u)` of the paper: `1` for Red (`u ∉ B`), `−1` for Blue (`u ∈ B`). -/
def sparseAux_sign {n : ℕ} (B : Finset (Fin n)) (u : Fin n) : ℝ := if u ∈ B then -1 else 1

/-- The indicator `χ_S(u)`. -/
def sparseAux_ind {n : ℕ} (S : Finset (Fin n)) (u : Fin n) : ℝ := if u ∈ S then 1 else 0

/-- The coefficient `X(u, v) = ℓ(u) χ_S(v) + ℓ(v) χ_S(u)` of the edge `uv` in `δ(S)` (the paper's
Table 1). -/
def sparseAux_X {n : ℕ} (B S : Finset (Fin n)) (u v : Fin n) : ℝ :=
  sparseAux_sign B u * sparseAux_ind S v + sparseAux_sign B v * sparseAux_ind S u

theorem sparseAux_X_comm {n : ℕ} (B S : Finset (Fin n)) (u v : Fin n) :
    sparseAux_X B S u v = sparseAux_X B S v u := by
  unfold sparseAux_X; ring

/-- `X` as a function of the unordered pair `{u, v}`. -/
def sparseAux_coef {n : ℕ} (B S : Finset (Fin n)) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨sparseAux_X B S, sparseAux_X_comm B S⟩

/-- `δ(S) = ∑_{v ∈ S} δ(v) = ∑_{\{u, v\}} X(u, v) 1_{u ∼ v}`, where `δ(v)` is the number of Red
neighbours of `v` minus the number of its Blue neighbours (the paper's computation of `δ(S)` in the
proof of Lemma 2.3). -/
theorem sparseAux_delta_eq {n : ℕ} (B S : Finset (Fin n)) (ω : EdgeVars n) :
    ∑ v ∈ S, ((nbrCount (graphOfEdges ω) (↑B : Set (Fin n))ᶜ v : ℝ) -
        nbrCount (graphOfEdges ω) (↑B : Set (Fin n)) v) =
      ∑ e ∈ sparseAux_offDiag n, sparseAux_coef B S e * edgeInd e ω := by
  classical
  -- `δ(v) = ∑_{u ≠ v} ℓ(u) 1_{u ∼ v}`.
  have hv : ∀ v, ((nbrCount (graphOfEdges ω) (↑B : Set (Fin n))ᶜ v : ℝ) -
      nbrCount (graphOfEdges ω) (↑B : Set (Fin n)) v) =
        ∑ u, if v = u then 0 else sparseAux_sign B u * edgeInd s(v, u) ω := by
    intro v
    rw [nbrCount_graphOfEdges, nbrCount_graphOfEdges, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases huv : v = u
    · subst huv; simp
    · by_cases hu : u ∈ B
      · simp [huv, hu, Ne.symm huv, sparseAux_sign]
      · simp [huv, hu, Ne.symm huv, sparseAux_sign]
  have hS : ∀ F : Fin n → ℝ, ∑ v ∈ S, F v = ∑ v, sparseAux_ind S v * F v := by
    intro F
    simp only [sparseAux_ind, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  set G : Fin n → Fin n → ℝ := fun a b =>
    if a = b then 0 else sparseAux_ind S a * sparseAux_sign B b * edgeInd s(a, b) ω with hG
  have hL : ∑ v ∈ S, ((nbrCount (graphOfEdges ω) (↑B : Set (Fin n))ᶜ v : ℝ) -
      nbrCount (graphOfEdges ω) (↑B : Set (Fin n)) v) = ∑ a, ∑ b, G a b := by
    rw [hS]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : a = b
    · simp [hG, hab]
    · simp only [hG, hab, ite_false]; ring
  have h2 := sparseAux_two_mul_sum_offDiag (fun a b => sparseAux_X B S a b * edgeInd s(a, b) ω)
    (fun a b => by rw [sparseAux_X_comm, Sym2.eq_swap])
    (fun e => sparseAux_coef B S e * edgeInd e ω) (fun a b => rfl)
  have hpt : ∀ a b, (if a = b then 0 else sparseAux_X B S a b * edgeInd s(a, b) ω) =
      G b a + G a b := by
    intro a b
    by_cases hab : a = b
    · simp [hG, hab]
    · have hba : b ≠ a := Ne.symm hab
      simp only [hG, hab, hba, ite_false, sparseAux_X]
      rw [Sym2.eq_swap (a := b)]; ring
  have h3 : ∑ a, ∑ b, (if a = b then 0 else sparseAux_X B S a b * edgeInd s(a, b) ω) =
      2 * ∑ a, ∑ b, G a b := by
    simp only [hpt, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun a b => G b a)]
    ring
  rw [hL]
  linarith [h2, h3]

/-- The Chernoff step of Lemma 2.3 for fixed `B` (the Blue set today) and `S`: for every `t > 0`,
`P(E(B, S)) ≤ P(δ(S) ≤ 0) ≤ E e^{−t δ(S)} = ∏_{u ≠ v} (1 − p + p e^{−t X(u,v)})
  ≤ exp(p ∑_{u ≠ v} (e^{−t X(u,v)} − 1))`
(the paper takes logarithms and uses `log(1 + z) ≤ z`; here `1 + z ≤ e^z`). -/
theorem sparseAux_prob_subset_le {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (B S : Finset (Fin n)) {t : ℝ} (ht : 0 < t) :
    gnpProb n p (fun G => (S : Set (Fin n)) ⊆ majorityStep G B) ≤
      Real.exp (p * ∑ e ∈ sparseAux_offDiag n, (Real.exp (-t * sparseAux_coef B S e) - 1)) := by
  classical
  rw [gnpProb_eq]
  set μ := edgeLaw n p with hμ
  set Z : Sym2 (Fin n) → EdgeVars n → ℝ := fun e ω => sparseAux_coef B S e * edgeInd e ω
    with hZ
  set δ : EdgeVars n → ℝ := ∑ e ∈ sparseAux_offDiag n, Z e with hδ
  have hδω : ∀ ω, δ ω = ∑ e ∈ sparseAux_offDiag n, sparseAux_coef B S e * edgeInd e ω := by
    intro ω; simp [hδ, hZ, Finset.sum_apply]
  -- `E(B, S)` implies `δ(S) ≤ 0`.
  have hsub : {ω | (S : Set (Fin n)) ⊆ majorityStep (graphOfEdges ω) ↑B} ⊆ {ω | δ ω ≤ 0} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hδω, ← sparseAux_delta_eq]
    apply Finset.sum_nonpos
    intro v hv
    have hmem := hω (Finset.mem_coe.mpr hv)
    have hle : nbrCount (graphOfEdges ω) (↑B : Set (Fin n))ᶜ v ≤
        nbrCount (graphOfEdges ω) (↑B : Set (Fin n)) v := by
      rcases hmem with h | h
      · exact h.le
      · exact h.1.le
    have hle' : (nbrCount (graphOfEdges ω) (↑B : Set (Fin n))ᶜ v : ℝ) ≤
        nbrCount (graphOfEdges ω) (↑B : Set (Fin n)) v := by exact_mod_cast hle
    linarith
  -- The summands `X(u, v) 1_{u ∼ v}` are independent.
  have hind : iIndepFun Z μ :=
    (iIndepFun_edgeInd n p).comp (fun e (w : ℝ) => sparseAux_coef B S e * w)
      (fun e => measurable_const.mul measurable_id)
  have hmeasZ : ∀ e, Measurable (Z e) := fun e => (measurable_edgeInd e).const_mul _
  -- Chernoff: `P(δ(S) ≤ 0) ≤ E e^{−t δ(S)}`.
  have h1 : μ.real {ω | δ ω ≤ 0} ≤ mgf δ μ (-t) := by
    have h := measure_le_le_exp_mul_mgf (X := δ) (μ := μ) (t := -t) 0 (neg_nonpos.mpr ht.le)
      Integrable.of_finite
    rwa [mul_zero, Real.exp_zero, one_mul] at h
  have h2 : mgf δ μ (-t) = ∏ e ∈ sparseAux_offDiag n, mgf (Z e) μ (-t) := hind.mgf_sum hmeasZ _
  -- `E e^{−t X(u,v) 1_{u ∼ v}} = 1 − p + p e^{−t X(u,v)}`.
  have h3 : ∀ e ∈ sparseAux_offDiag n,
      mgf (Z e) μ (-t) = 1 + p * (Real.exp (-t * sparseAux_coef B S e) - 1) := by
    intro e he
    have hdiag : ¬ e.IsDiag := (Finset.mem_filter.mp he).2
    have hp : ∫ ω, edgeInd e ω ∂μ = p :=
      (isBernoulliFamily_edgeInd (n := n) hp0.le hp1.le).integral_eq ⟨e, hdiag⟩
    have hpt : ∀ ω, Real.exp (-t * Z e ω) =
        1 + (Real.exp (-t * sparseAux_coef B S e) - 1) * edgeInd e ω := by
      intro ω; simp only [hZ, edgeInd]; split_ifs <;> simp
    simp only [mgf, hpt]
    rw [integral_add (integrable_const _) Integrable.of_finite, integral_const_mul, hp]
    simp; ring
  -- `1 + z ≤ e^z`.
  calc μ.real {ω | (S : Set (Fin n)) ⊆ majorityStep (graphOfEdges ω) ↑B}
      ≤ μ.real {ω | δ ω ≤ 0} := measureReal_mono hsub
    _ ≤ ∏ e ∈ sparseAux_offDiag n, (1 + p * (Real.exp (-t * sparseAux_coef B S e) - 1)) := by
      rw [← Finset.prod_congr rfl h3, ← h2]; exact h1
    _ ≤ ∏ e ∈ sparseAux_offDiag n, Real.exp (p * (Real.exp (-t * sparseAux_coef B S e) - 1)) := by
      refine Finset.prod_le_prod₀ (fun e _ => ?_) (fun e _ => ?_)
      · have := Real.exp_pos (-t * sparseAux_coef B S e)
        nlinarith
      · linarith [Real.add_one_le_exp (p * (Real.exp (-t * sparseAux_coef B S e) - 1))]
    _ = Real.exp (p * ∑ e ∈ sparseAux_offDiag n, (Real.exp (-t * sparseAux_coef B S e) - 1)) := by
      rw [← Real.exp_sum, Finset.mul_sum]

/-- The paper's quadratic `f` in the proof of Lemma 2.3, with `E = e^t`, `C(m, 2) = m(m − 1)/2`,
`s = |S|`, `r = |R|`, `β = |B|`:
`f(x) = C(s − x, 2) e^t (e^t + 1) − C(x, 2)(e^{−t} + 1) − s(r − x) + s(β − s + x) e^t`. -/
def sparseAux_f (E s r β x : ℝ) : ℝ :=
  (s - x) * (s - x - 1) / 2 * (E * (E + 1)) - x * (x - 1) / 2 * (E⁻¹ + 1) - s * (r - x) +
    s * (β - s + x) * E

/-- The values of `e^{−t X(a, b)} − 1` (the paper's Table 1), as a polynomial in the indicators
of `a, b ∈ S` and `a, b ∈ B`. -/
theorem sparseAux_exp_X_sub_one {n : ℕ} (B S : Finset (Fin n)) (t : ℝ) (a b : Fin n) :
    Real.exp (-t * sparseAux_X B S a b) - 1 =
      (Real.exp (-t * 2) - 1) * ((sparseAux_ind S a * (1 - sparseAux_ind B a)) *
          (sparseAux_ind S b * (1 - sparseAux_ind B b))) +
        (Real.exp (-t * (-2)) - 1) * ((sparseAux_ind S a * sparseAux_ind B a) *
          (sparseAux_ind S b * sparseAux_ind B b)) +
        (Real.exp (-t * 1) - 1) * (sparseAux_ind S a *
          ((1 - sparseAux_ind S b) * (1 - sparseAux_ind B b))) +
        (Real.exp (-t * (-1)) - 1) * (sparseAux_ind S a *
          ((1 - sparseAux_ind S b) * sparseAux_ind B b)) +
        (Real.exp (-t * 1) - 1) * (((1 - sparseAux_ind S a) * (1 - sparseAux_ind B a)) *
          sparseAux_ind S b) +
        (Real.exp (-t * (-1)) - 1) * (((1 - sparseAux_ind S a) * sparseAux_ind B a) *
          sparseAux_ind S b) := by
  unfold sparseAux_X sparseAux_sign sparseAux_ind
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> by_cases ha' : a ∈ B <;> by_cases hb' : b ∈ B <;>
    simp [ha, hb, ha', hb'] <;> norm_num

/-- The diagonal values: `e^{−t X(a, a)} − 1`. -/
theorem sparseAux_exp_X_diag {n : ℕ} (B S : Finset (Fin n)) (t : ℝ) (a : Fin n) :
    Real.exp (-t * sparseAux_X B S a a) - 1 =
      (Real.exp (-t * 2) - 1) * (sparseAux_ind S a * (1 - sparseAux_ind B a)) +
        (Real.exp (-t * (-2)) - 1) * (sparseAux_ind S a * sparseAux_ind B a) := by
  unfold sparseAux_X sparseAux_sign sparseAux_ind
  by_cases ha : a ∈ S <;> by_cases ha' : a ∈ B <;> simp [ha, ha'] <;> norm_num

theorem sparseAux_sum_sum_mul {n : ℕ} (c : ℝ) (f g : Fin n → ℝ) :
    ∑ a, ∑ b, c * (f a * g b) = c * ((∑ a, f a) * (∑ b, g b)) := by
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]

/-- The paper's equation (difS-bound-2) together with `∑ = (1 − e^{−t}) f(|S ∩ R|)`:
`∑_{\{u,v\}} (e^{−t X(u, v)} − 1) = (1 − e^{−t}) f(|S ∩ R|)`. -/
theorem sparseAux_sum_exp_X {n : ℕ} (B S : Finset (Fin n)) (t : ℝ) :
    ∑ e ∈ sparseAux_offDiag n, (Real.exp (-t * sparseAux_coef B S e) - 1) =
      (1 - Real.exp (-t)) * sparseAux_f (Real.exp t) S.card (n - B.card) B.card
        (S \ B).card := by
  classical
  set E := Real.exp t with hE
  have hEpos : 0 < E := Real.exp_pos t
  have hE1 : Real.exp (-t * 1) = E⁻¹ := by rw [mul_one, Real.exp_neg]
  have hEm1 : Real.exp (-t * (-1)) = E := by rw [mul_neg_one, neg_neg]
  have hE2 : Real.exp (-t * 2) = E⁻¹ ^ 2 := by
    rw [show -t * 2 = -t + -t by ring, Real.exp_add, Real.exp_neg]; ring
  have hEm2 : Real.exp (-t * (-2)) = E ^ 2 := by
    rw [show -t * (-2) = t + t by ring, Real.exp_add]; ring
  set σ := sparseAux_ind S with hσ
  set β := sparseAux_ind B with hβ
  -- the sums of the indicators
  have hsum : ∀ T : Finset (Fin n), ∑ a, sparseAux_ind T a = T.card := by
    intro T; simp [sparseAux_ind]
  have hsS : ∑ a, σ a = S.card := hsum S
  have hsB : ∑ a, β a = B.card := hsum B
  have hσβ : ∑ a, σ a * β a = (S ∩ B).card := by
    rw [← hsum (S ∩ B)]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hσ, hβ, sparseAux_ind, Finset.mem_inter]
    by_cases ha : a ∈ S <;> by_cases hb : a ∈ B <;> simp [ha, hb]
  have hcardS : ((S \ B).card : ℝ) + (S ∩ B).card = S.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter S B
  -- the four class sums
  have hA : ∑ a, σ a * (1 - β a) = (S \ B).card := by
    have : ∀ a, σ a * (1 - β a) = σ a - σ a * β a := fun a => by ring
    simp only [this, Finset.sum_sub_distrib, hsS, hσβ]; linarith
  have hNR : ∑ a, (1 - σ a) * (1 - β a) = (n - B.card) - (S \ B).card := by
    have : ∀ a, (1 - σ a) * (1 - β a) = 1 - β a - σ a * (1 - β a) := fun a => by ring
    simp only [this, Finset.sum_sub_distrib, hsB, hA, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hNB : ∑ a, (1 - σ a) * β a = B.card - (S ∩ B).card := by
    have : ∀ a, (1 - σ a) * β a = β a - σ a * β a := fun a => by ring
    simp only [this, Finset.sum_sub_distrib, hsB, hσβ]
  -- the full double sum
  have hfull : ∑ a, ∑ b, (Real.exp (-t * sparseAux_X B S a b) - 1) =
      (E⁻¹ ^ 2 - 1) * ((∑ a, σ a * (1 - β a)) * (∑ b, σ b * (1 - β b))) +
        (E ^ 2 - 1) * ((∑ a, σ a * β a) * (∑ b, σ b * β b)) +
        (E⁻¹ - 1) * ((∑ a, σ a) * (∑ b, (1 - σ b) * (1 - β b))) +
        (E - 1) * ((∑ a, σ a) * (∑ b, (1 - σ b) * β b)) +
        (E⁻¹ - 1) * ((∑ a, (1 - σ a) * (1 - β a)) * (∑ b, σ b)) +
        (E - 1) * ((∑ a, (1 - σ a) * β a) * (∑ b, σ b)) := by
    simp only [sparseAux_exp_X_sub_one, Finset.sum_add_distrib, sparseAux_sum_sum_mul, hE1, hEm1,
      hE2, hEm2]
    rfl
  -- the diagonal
  have hdiag : ∑ a, (Real.exp (-t * sparseAux_X B S a a) - 1) =
      (E⁻¹ ^ 2 - 1) * ∑ a, σ a * (1 - β a) + (E ^ 2 - 1) * ∑ a, σ a * β a := by
    simp only [sparseAux_exp_X_diag, Finset.sum_add_distrib, ← Finset.mul_sum, hE2, hEm2]
    rfl
  have h2 := sparseAux_two_mul_sum_offDiag (fun a b => Real.exp (-t * sparseAux_X B S a b) - 1)
    (fun a b => by rw [sparseAux_X_comm]) (fun e => Real.exp (-t * sparseAux_coef B S e) - 1)
    (fun a b => rfl)
  have hsplit : ∀ a, ∑ b, (if a = b then (0 : ℝ) else Real.exp (-t * sparseAux_X B S a b) - 1) =
      ∑ b, (Real.exp (-t * sparseAux_X B S a b) - 1) - (Real.exp (-t * sparseAux_X B S a a) - 1) := by
    intro a
    have : ∀ b, (if a = b then (0 : ℝ) else Real.exp (-t * sparseAux_X B S a b) - 1) =
        (Real.exp (-t * sparseAux_X B S a b) - 1) -
          (if a = b then Real.exp (-t * sparseAux_X B S a b) - 1 else 0) := by
      intro b; split_ifs with h <;> simp [h]
    rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simp
  have h2' : 2 * ∑ e ∈ sparseAux_offDiag n, (Real.exp (-t * sparseAux_coef B S e) - 1) =
      ∑ a, ∑ b, (Real.exp (-t * sparseAux_X B S a b) - 1) -
        ∑ a, (Real.exp (-t * sparseAux_X B S a a) - 1) := by
    rw [h2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => hsplit a
  rw [hfull, hdiag, hA, hσβ, hNR, hNB, hsS] at h2'
  have hSB : ((S ∩ B).card : ℝ) = S.card - (S \ B).card := by linarith
  rw [hSB] at h2'
  rw [Real.exp_neg, ← hE]
  unfold sparseAux_f
  field_simp
  field_simp at h2'
  linear_combination h2'

/-- The convexity step and the two endpoint estimates in the proof of Lemma 2.3. Let
`|B| = β = ⌊xn⌋`, `|S| = s = ⌊yn⌋ + 1` with `0 ≤ y ≤ x`, and `E = e^t > 1`. Then
`T − f(0) = s(e^t + (xn − ⌊xn⌋)(1 + e^t) + (xn − ⌊yn⌋) e^t (e^t − 1)/2) > 0` (the paper drops the
term `(xn − ⌊xn⌋) e^t`, which is `≥ 0`),
`T − f(s) = s((xn e^t − ⌊yn⌋ e^{−t})(e^t − 1)/2 + (xn − ⌊xn⌋)(e^t + 1) − 1)
  ≥ (1/2) s (xn (e^t − 1)² − 2)`,
and, `f` being a convex quadratic, `f(a) ≤ max{f(0), f(s)} ≤ T` for `a ∈ [0, s]` when `t` is
nice (`xn (e^t − 1)² ≥ 2`). Here `T = (1/2) s n (x(e^{2t} + e^t + 2) − 2)`. -/
theorem sparseAux_f_le_T {n : ℕ} {x y E β s a : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (hE : 1 < E)
    (hβ : β = ⌊x * n⌋₊) (hs : s = ⌊y * n⌋₊ + 1) (ha0 : 0 ≤ a) (has : a ≤ s)
    (hnice : 2 ≤ x * n * (E - 1) ^ 2) :
    sparseAux_f E s (n - β) β a ≤ 1 / 2 * s * n * (x * (E ^ 2 + E + 2) - 2) := by
  have hE0 : 0 < E := by linarith
  have hEinv : E⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hE.le
  have hEinv0 : 0 < E⁻¹ := inv_pos.mpr hE0
  have hxn0 : 0 ≤ x * n := mul_nonneg (hy.trans hxy) (Nat.cast_nonneg n)
  have hβx : β ≤ x * n := by rw [hβ]; exact Nat.floor_le hxn0
  have hsx : s - 1 ≤ x * n := by
    have : (⌊y * n⌋₊ : ℝ) ≤ y * n := Nat.floor_le (mul_nonneg hy (Nat.cast_nonneg n))
    have : y * n ≤ x * n := mul_le_mul_of_nonneg_right hxy (Nat.cast_nonneg n)
    rw [hs]; linarith
  have hs1 : 1 ≤ s := by rw [hs]; have := Nat.cast_nonneg (α := ℝ) ⌊y * n⌋₊; linarith
  have hs0 : 0 < s := by linarith
  set T := 1 / 2 * s * n * (x * (E ^ 2 + E + 2) - 2) with hT
  -- `T − f(0) > 0`
  have hT0 : T - sparseAux_f E s (n - β) β 0 =
      s * (E + (x * n - β) * (1 + E) + (x * n - (s - 1)) * E * (E - 1) / 2) := by
    rw [hT]; unfold sparseAux_f; ring
  have hf0 : sparseAux_f E s (n - β) β 0 ≤ T := by
    have : 0 ≤ s * (E + (x * n - β) * (1 + E) + (x * n - (s - 1)) * E * (E - 1) / 2) := by
      have h1 : 0 ≤ (x * n - β) * (1 + E) := mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ (x * n - (s - 1)) * E * (E - 1) / 2 := by
        have := mul_nonneg (mul_nonneg (sub_nonneg.mpr hsx) hE0.le) (sub_nonneg.mpr hE.le)
        linarith
      positivity
    linarith
  -- `T − f(s) ≥ (1/2) s (xn (e^t − 1)² − 2) ≥ 0`
  have hTs : T - sparseAux_f E s (n - β) β s =
      s * ((x * n * E - (s - 1) * E⁻¹) * (E - 1) / 2 + (x * n - β) * (E + 1) - 1) := by
    rw [hT]; unfold sparseAux_f; field_simp; ring
  have hfs : sparseAux_f E s (n - β) β s ≤ T := by
    have h1 : x * n * (E - 1) ^ 2 / 2 ≤ (x * n * E - (s - 1) * E⁻¹) * (E - 1) / 2 := by
      have : x * n * (E - 1) ≤ x * n * E - (s - 1) * E⁻¹ := by
        have : (s - 1) * E⁻¹ ≤ x * n * E⁻¹ := mul_le_mul_of_nonneg_right hsx hEinv0.le
        nlinarith
      have := mul_le_mul_of_nonneg_right this (sub_nonneg.mpr hE.le)
      nlinarith
    have h2 : 0 ≤ (x * n - β) * (E + 1) := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ s * ((x * n * E - (s - 1) * E⁻¹) * (E - 1) / 2 + (x * n - β) * (E + 1) - 1) :=
      mul_nonneg hs0.le (by linarith)
    linarith
  -- convexity: `f(a) = (1 − a/s) f(0) + (a/s) f(s) + α a (a − s)` with `α ≥ 0`
  set α := (E * (E + 1) - (E⁻¹ + 1)) / 2 with hα
  have hα0 : 0 ≤ α := by rw [hα]; nlinarith
  have hconv : sparseAux_f E s (n - β) β a =
      (1 - a / s) * sparseAux_f E s (n - β) β 0 + a / s * sparseAux_f E s (n - β) β s +
        α * (a * (a - s)) := by
    rw [hα]; unfold sparseAux_f; field_simp; ring
  have hw0 : 0 ≤ 1 - a / s := by rw [sub_nonneg, div_le_one hs0]; exact has
  have hw1 : 0 ≤ a / s := div_nonneg ha0 hs0.le
  have hq : α * (a * (a - s)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hα0 (mul_nonpos_of_nonneg_of_nonpos ha0 (by linarith))
  rw [hconv]
  nlinarith [mul_le_mul_of_nonneg_left hf0 hw0, mul_le_mul_of_nonneg_left hfs hw1]

/-- `t_x = log(1/x − 1)/3` satisfies `e^{3 t_x} = 1/x − 1`. -/
theorem sparseAux_exp_tx_pow {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Real.exp (Real.log (1 / x - 1) / 3) ^ 3 = 1 / x - 1 := by
  have hpos : 0 < 1 / x - 1 := by rw [sub_pos, lt_div_iff₀ hx0]; linarith
  rw [← Real.exp_nat_mul]
  push_cast
  rw [show (3 : ℝ) * (Real.log (1 / x - 1) / 3) = Real.log (1 / x - 1) by ring, Real.exp_log hpos]

/-- `t_x` is nice: `xn (e^{t_x} − 1)² ≥ 2`, via `n(1 − 2x)² ≥ 2x(e^{2t_x} + e^{t_x} + 1)²`
(the paper's two cases `x < 1/9`, where `n ≥ 163` gives `xn³ ≥ n² ≥ (1458/49)³`, and `x ≥ 1/9`).

Repair of an arithmetic slip in the case `x ≥ 1/9`: the paper bounds `e^{t_x} ≤ 2` and `2x ≤ 1`,
which only give `2x(e^{2t_x} + e^{t_x} + 1)² ≤ 49`, and then asks for `n(1 − 2x)² ≥ 7`. Using
`x = 1/(1 + e^{3t_x})` as well gives `2x(e^{2t_x} + e^{t_x} + 1)² ≤ 98/9 < 16 ≤ n(1 − 2x)²`. -/
theorem sparseAux_tx_nice {n : ℕ} (hn : 163 ≤ n) {x : ℝ} (hxn : 1 ≤ x * n)
    (hx1 : x ≤ 1 / 2 - 2 / Real.sqrt n) {E : ℝ} (hE0 : 0 < E) (hE3 : E ^ 3 = 1 / x - 1) :
    2 ≤ x * n * (E - 1) ^ 2 := by
  have hn163 : (163 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hx0 : 0 < x := by
    by_contra h; push Not at h; nlinarith
  have hxhalf : x < 1 / 2 := by
    have : 0 < 2 / Real.sqrt n := by positivity
    linarith
  have hxE : x * (1 + E ^ 3) = 1 := by rw [hE3]; field_simp; ring
  have hE1 : 1 ≤ E := by
    by_contra h; push Not at h
    have : E ^ 3 < 1 := by
      calc E ^ 3 < 1 ^ 3 := by gcongr
        _ = 1 := one_pow 3
    have : 1 < 1 / x - 1 := by rw [lt_sub_iff_add_lt, lt_div_iff₀ hx0]; linarith
    linarith
  -- `n(1 − 2x)² ≥ 2x(E² + E + 1)²`
  have key : 2 * x * (E ^ 2 + E + 1) ^ 2 ≤ n * (1 - 2 * x) ^ 2 := by
    rcases lt_or_ge x (1 / 9) with hx9 | hx9
    · -- `x < 1/9`: `E² + E + 1 ≤ 3E²`, `(xE⁴)³ ≤ 1/x ≤ n`, `1458 xE⁴ ≤ 49 n`.
      have h3 : E ^ 2 + E + 1 ≤ 3 * E ^ 2 := by nlinarith
      set w := x * E ^ 4 with hw
      have hw0 : 0 ≤ w := by positivity
      have hw3 : w ^ 3 ≤ n := by
        have h1 : w ^ 3 = x ^ 3 * (E ^ 3) ^ 4 := by rw [hw]; ring
        have h2 : (E ^ 3) ^ 4 ≤ (1 / x) ^ 4 := by
          rw [hE3]; gcongr
          · rw [sub_nonneg, le_div_iff₀ hx0]; linarith
          · linarith
        have h4 : x ^ 3 * (1 / x) ^ 4 = 1 / x := by field_simp
        have h5 : 1 / x ≤ n := by rw [div_le_iff₀ hx0]; linarith
        calc w ^ 3 = x ^ 3 * (E ^ 3) ^ 4 := h1
          _ ≤ x ^ 3 * (1 / x) ^ 4 := by gcongr
          _ = 1 / x := h4
          _ ≤ n := h5
      have hw49 : 1458 * w ≤ 49 * n := by
        have hn2 : (1458 : ℝ) ^ 3 ≤ 49 ^ 3 * (n : ℝ) ^ 2 := by nlinarith
        have : (1458 * w) ^ 3 ≤ (49 * (n : ℝ)) ^ 3 := by
          calc (1458 * w) ^ 3 = (1458 : ℝ) ^ 3 * w ^ 3 := by ring
            _ ≤ (1458 : ℝ) ^ 3 * n := by gcongr
            _ ≤ 49 ^ 3 * (n : ℝ) ^ 2 * n := by nlinarith
            _ = (49 * (n : ℝ)) ^ 3 := by ring
        exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) this
      have h79 : 49 / 81 ≤ (1 - 2 * x) ^ 2 := by nlinarith
      calc 2 * x * (E ^ 2 + E + 1) ^ 2 ≤ 2 * x * (3 * E ^ 2) ^ 2 := by
            gcongr
        _ = 18 * w := by rw [hw]; ring
        _ ≤ n * (49 / 81) := by linarith
        _ ≤ n * (1 - 2 * x) ^ 2 := by gcongr
    · -- `x ≥ 1/9`: `E ≤ 2`, and `2x(E² + E + 1)² = 2(E² + E + 1)²/(1 + E³) ≤ 16 ≤ n(1 − 2x)²`.
      have hE2 : E ≤ 2 := by
        by_contra h; push Not at h
        have : (8 : ℝ) < E ^ 3 := by
          calc (8 : ℝ) = 2 ^ 3 := by norm_num
            _ < E ^ 3 := by gcongr
        have : 1 / x - 1 ≤ 8 := by rw [sub_le_iff_le_add, div_le_iff₀ hx0]; linarith
        linarith
      have h16 : 2 * x * (E ^ 2 + E + 1) ^ 2 ≤ 16 := by
        have hx' : x = 1 / (1 + E ^ 3) := by field_simp; linarith
        have h' : 2 * x * (E ^ 2 + E + 1) ^ 2 = 2 * (E ^ 2 + E + 1) ^ 2 / (1 + E ^ 3) := by
          rw [hx']; field_simp
        rw [h', div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hE1) (sub_nonneg.mpr hE2)]
      have hgap : 4 / Real.sqrt n ≤ 1 - 2 * x := by
        have : 1 - 2 * x ≥ 1 - 2 * (1 / 2 - 2 / Real.sqrt n) := by linarith
        linarith [show 1 - 2 * (1 / 2 - 2 / Real.sqrt n) = 4 / Real.sqrt n by ring]
      have h16' : 16 ≤ n * (1 - 2 * x) ^ 2 := by
        have h1 : (4 / Real.sqrt n) ^ 2 ≤ (1 - 2 * x) ^ 2 := by
          gcongr
        have h2 : (4 / Real.sqrt n) ^ 2 = 16 / n := by
          rw [div_pow, Real.sq_sqrt hn0.le]; norm_num
        rw [h2] at h1
        rw [div_le_iff₀ hn0] at h1
        linarith
      linarith
  -- `xn(E − 1)²(E² + E + 1)² = n(1 − 2x)²/x ≥ 2(E² + E + 1)²`
  have hsum : 0 < E ^ 2 + E + 1 := by positivity
  have hid : x * n * (E - 1) ^ 2 * (E ^ 2 + E + 1) ^ 2 * x = n * (1 - 2 * x) ^ 2 := by
    have : (E - 1) * (E ^ 2 + E + 1) = E ^ 3 - 1 := by ring
    calc x * n * (E - 1) ^ 2 * (E ^ 2 + E + 1) ^ 2 * x = n * (x * (E ^ 3 - 1)) ^ 2 := by
          rw [← this]; ring
      _ = n * (1 - 2 * x) ^ 2 := by rw [hE3]; field_simp; ring
  by_contra hlt; push Not at hlt
  have : x * n * (E - 1) ^ 2 * (E ^ 2 + E + 1) ^ 2 * x < 2 * (E ^ 2 + E + 1) ^ 2 * x := by
    have := mul_lt_mul_of_pos_right hlt (pow_pos hsum 2)
    exact mul_lt_mul_of_pos_right this hx0
  nlinarith

/-- `g_x(t_x) = −(1 − x/2 − (3/2) x^{1/3} (1 − x)^{2/3})`, where
`g_x(t) = (1 − e^{−t})(x(e^{2t} + e^t + 2)/2 − 1)` and `E = e^{t_x}`. -/
theorem sparseAux_g_tx {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {E : ℝ} (hE0 : 0 < E)
    (hE3 : E ^ 3 = 1 / x - 1) :
    (1 - E⁻¹) * (x * (E ^ 2 + E + 2) / 2 - 1) =
      -(1 - x / 2 - 3 / 2 * x ^ (1 / 3 : ℝ) * (1 - x) ^ (2 / 3 : ℝ)) := by
  have hxE : x * (1 + E ^ 3) = 1 := by rw [hE3]; field_simp; ring
  -- `x^{1/3} (1 − x)^{2/3} = x E²`: both are nonnegative with cube `x (1 − x)²`.
  have hq : x ^ (1 / 3 : ℝ) * (1 - x) ^ (2 / 3 : ℝ) = x * E ^ 2 := by
    have h1x : 0 ≤ 1 - x := by linarith
    have hcube1 : (x ^ (1 / 3 : ℝ) * (1 - x) ^ (2 / 3 : ℝ)) ^ 3 = x * (1 - x) ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le,
        ← Real.rpow_mul h1x]
      norm_num
    have hcube2 : (x * E ^ 2) ^ 3 = x * (1 - x) ^ 2 := by
      have : (x * E ^ 2) ^ 3 = x ^ 3 * (E ^ 3) ^ 2 := by ring
      rw [this, hE3]; field_simp
    have h0 : 0 ≤ x ^ (1 / 3 : ℝ) * (1 - x) ^ (2 / 3 : ℝ) := by positivity
    have h0' : 0 ≤ x * E ^ 2 := by positivity
    exact (pow_left_inj₀ h0 h0' (by norm_num : (3 : ℕ) ≠ 0)).mp (hcube1.trans hcube2.symm)
  rw [mul_assoc (3 / 2 : ℝ), hq]
  field_simp
  linear_combination (-2) * hxE


/-! ### The function `h` -/

/-- `h = −H`, where `H` is Mathlib's binary entropy (in nats). -/
theorem sparseAux_h_eq (x : ℝ) : h x = -Real.binEntropy x := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def]
  unfold h; beta_reduce; ring

/-- `h` is decreasing on `[0, 1/2]`. -/
theorem sparseAux_h_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) : h b ≤ h a := by
  rw [sparseAux_h_eq, sparseAux_h_eq, neg_le_neg_iff]
  exact Real.binEntropy_strictMonoOn.monotoneOn ⟨ha, by linarith⟩ ⟨ha.trans hab, by linarith⟩ hab

/-- `h` is convex, so `h(y + ε) ≥ h(y) + ε h'(y)` with `h'(y) = log(y/(1 − y))`. -/
theorem sparseAux_h_tangent {y ε : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (hε : 0 < ε)
    (hyε : y + ε ≤ 1) : h y + ε * Real.log (y / (1 - y)) ≤ h (y + ε) := by
  have hc := Real.strictConcave_binEntropy.concaveOn
  have hd := Real.hasDerivAt_binEntropy hy0.ne' hy1.ne
  have hsl := hc.slope_le_of_hasDerivAt ⟨hy0.le, hy1.le⟩ ⟨by linarith, hyε⟩
    (by linarith : y < y + ε) hd
  rw [slope_def_field, show y + ε - y = ε by ring, div_le_iff₀ hε] at hsl
  rw [sparseAux_h_eq, sparseAux_h_eq, Real.log_div hy0.ne' (by linarith : (1 - y) ≠ 0)]
  nlinarith

/-- The "routine Stirling bound" `C(n, k) ≤ e^{−n h(k/n)}`. -/
theorem sparseAux_choose_le (n k : ℕ) : (n.choose k : ℝ) ≤ Real.exp (-(n * h (k / n))) := by
  rw [sparseAux_h_eq, mul_neg, neg_neg]; exact Nat.choose_le_exp_mul_binEntropy n k

/-- The double union bound of the paper:
`C(n, ⌊xn⌋) C(n, ⌊yn⌋ + 1) ≤ e^{−n(h(x) + h(y + 1/n))} ≤ ((1 − y)/y) e^{−n(h(x) + h(y))}
  ≤ (1/y) e^{−2n h(x)}`. -/
theorem sparseAux_choose_mul_le {n : ℕ} (hn : 0 < n) {x y : ℝ} (hy : 0 < y) (hxy : y ≤ x)
    (hx : x + 1 / n ≤ 1 / 2) :
    (n.choose ⌊x * n⌋₊ : ℝ) * n.choose (⌊y * n⌋₊ + 1) ≤ y⁻¹ * Real.exp (-(2 * n * h x)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < x := lt_of_lt_of_le hy hxy
  have hxn0 : 0 ≤ x * n := by positivity
  have hyn0 : 0 ≤ y * n := by positivity
  have hεpos : (0 : ℝ) < 1 / n := by positivity
  -- `h(⌊xn⌋/n) ≥ h(x)`
  have h1 : h x ≤ h ((⌊x * n⌋₊ : ℕ) / n) := by
    apply sparseAux_h_anti (by positivity)
    · rw [div_le_iff₀ hn0]; exact Nat.floor_le hxn0
    · linarith
  -- `h((⌊yn⌋ + 1)/n) ≥ h(y + 1/n)`
  have h2 : h (y + 1 / n) ≤ h (((⌊y * n⌋₊ + 1 : ℕ) : ℝ) / n) := by
    apply sparseAux_h_anti (by positivity)
    · rw [div_le_iff₀ hn0]; push_cast
      have := Nat.floor_le hyn0
      rw [add_mul, div_mul_cancel₀ _ hn0.ne']; linarith
    · linarith
  -- convexity: `h(y + 1/n) ≥ h(y) + (1/n) log(y/(1 − y))`
  have hy1 : y < 1 := by linarith
  have h3 := sparseAux_h_tangent hy hy1 hεpos (by linarith)
  -- monotonicity: `h(y) ≥ h(x)`
  have h4 : h x ≤ h y := sparseAux_h_anti hy.le hxy (by linarith)
  have hlog : Real.exp (-Real.log (y / (1 - y))) = (1 - y) / y := by
    rw [Real.exp_neg, Real.exp_log (by apply div_pos hy; linarith), inv_div]
  calc (n.choose ⌊x * n⌋₊ : ℝ) * n.choose (⌊y * n⌋₊ + 1)
      ≤ Real.exp (-(n * h ((⌊x * n⌋₊ : ℕ) / n))) *
          Real.exp (-(n * h (((⌊y * n⌋₊ + 1 : ℕ) : ℝ) / n))) := by
        gcongr
        · exact sparseAux_choose_le n _
        · exact sparseAux_choose_le n _
    _ ≤ Real.exp (-(n * h x)) * Real.exp (-(n * h (y + 1 / n))) := by
        gcongr
    _ ≤ Real.exp (-(n * h x)) * Real.exp (-(n * h y) - Real.log (y / (1 - y))) := by
        gcongr
        have : (n : ℝ) * (h y + 1 / n * Real.log (y / (1 - y))) ≤ n * h (y + 1 / n) :=
          mul_le_mul_of_nonneg_left h3 hn0.le
        rw [mul_add, ← mul_assoc, mul_one_div_cancel hn0.ne', one_mul] at this
        linarith
    _ = (1 - y) / y * (Real.exp (-(n * h x)) * Real.exp (-(n * h y))) := by
        rw [sub_eq_add_neg, Real.exp_add, hlog]; ring
    _ ≤ y⁻¹ * (Real.exp (-(n * h x)) * Real.exp (-(n * h x))) := by
        gcongr
        rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr hy]
    _ = y⁻¹ * Real.exp (-(2 * n * h x)) := by
        rw [← Real.exp_add]; ring_nf

/-- **Lemma 2.3** (`S:lem:hypo-blue-bound`). For `0 < b₂ ≤ b₁ ≤ 1/2 − 2/√n` and `n ≥ 163`,
`G ∼ G(n, p)` is such that for every colouring with at most `b₁ n` Blue vertices, at most `b₂ n`
vertices are Blue the next day, except with probability at most `b₂⁻¹ exp(−n F(pn, b₂, b₁))`.

Deviation: the printed hypothesis is `0 ≤ b₂ ≤ b₁ ≤ 1/2 − 7/n` with no condition on `n`; see the
module docstring. `b₂ > 0` because the bound divides by `b₂`. -/
theorem lemma2_3 {n : ℕ} (hn : 163 ≤ n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {b₁ b₂ : ℝ}
    (hb₂ : 0 < b₂) (hb : b₂ ≤ b₁) (hb₁ : b₁ ≤ 1 / 2 - 2 / Real.sqrt n) :
    1 - b₂⁻¹ * Real.exp (-(n * F (p * n) b₂ b₁)) ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
      (B.ncard : ℝ) ≤ b₁ * n → ((majorityStep G B).ncard : ℝ) ≤ b₂ * n) := by
  classical
  -- The paper's notation: `x = b₁` (Blue fraction today), `y = b₂` (Blue fraction tomorrow).
  have hn163 : (163 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hx0 : 0 < b₁ := lt_of_lt_of_le hb₂ hb
  have hxhalf : b₁ < 1 / 2 := by
    have : 0 < 2 / Real.sqrt n := by positivity
    linarith
  have hbound0 : 0 ≤ b₂⁻¹ * Real.exp (-(n * F (p * n) b₂ b₁)) := by positivity
  -- If `⌊xn⌋ = 0`, the only admissible Blue set is empty, and it stays empty.
  by_cases hk0 : ⌊b₁ * n⌋₊ = 0
  · have hall : ∀ G : SimpleGraph (Fin n), ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ b₁ * n →
        ((majorityStep G B).ncard : ℝ) ≤ b₂ * n := by
      intro G B hB
      have hB0 : B.ncard = 0 := by
        have : B.ncard ≤ ⌊b₁ * n⌋₊ := Nat.le_floor hB
        omega
      rw [(Set.ncard_eq_zero (Set.toFinite B)).mp hB0, majorityStep_empty, Set.ncard_empty,
        Nat.cast_zero]
      positivity
    calc 1 - b₂⁻¹ * Real.exp (-(n * F (p * n) b₂ b₁)) ≤ 1 := by linarith
      _ = gnpProb n p (fun _ => True) := gnpProb_true.symm
      _ ≤ _ := gnpProb_mono fun G _ => hall G
  have hxn : 1 ≤ b₁ * n := by
    have h1 : 1 ≤ ⌊b₁ * n⌋₊ := Nat.one_le_iff_ne_zero.mpr hk0
    have h2 : ((⌊b₁ * n⌋₊ : ℕ) : ℝ) ≤ b₁ * n := Nat.floor_le (by positivity)
    have h3 : (1 : ℝ) ≤ ⌊b₁ * n⌋₊ := by exact_mod_cast h1
    linarith
  -- `t = t_x = log(1/x − 1)/3`, `E = e^t`.
  set t := Real.log (1 / b₁ - 1) / 3 with ht
  set E := Real.exp t with hE
  have hE0 : 0 < E := Real.exp_pos t
  have hE3 : E ^ 3 = 1 / b₁ - 1 := sparseAux_exp_tx_pow hx0 (by linarith)
  have hE1 : 1 < E := by
    by_contra hcon; push Not at hcon
    have : E ^ 3 ≤ 1 := by
      calc E ^ 3 ≤ 1 ^ 3 := by gcongr
        _ = 1 := one_pow 3
    have : 1 < 1 / b₁ - 1 := by rw [lt_sub_iff_add_lt, lt_div_iff₀ hx0]; linarith
    linarith
  have htpos : 0 < t := by rw [← Real.one_lt_exp_iff]; exact hE1
  have hnice := sparseAux_tx_nice hn hxn hb₁ hE0 hE3
  -- `g(x) = 1 − x/2 − (3/2) x^{1/3} (1 − x)^{2/3} ≥ 0` and `g_x(t_x) = −g(x)`.
  set g := 1 - b₁ / 2 - 3 / 2 * b₁ ^ (1 / 3 : ℝ) * (1 - b₁) ^ (2 / 3 : ℝ) with hg
  have hg0 : 0 ≤ g := le_trans (by positivity)
    (Real.one_sub_two_mul_sq_div_three_le hx0.le hxhalf.le)
  have hgt := sparseAux_g_tx hx0 (by linarith) hE0 hE3
  -- `P(E(B, S)) ≤ exp(−p n |S| g(x)) ≤ exp(−p n² y g(x))` for `|B| = ⌊xn⌋`, `|S| = ⌊yn⌋ + 1`.
  have hpair : ∀ B S : Finset (Fin n), B.card = ⌊b₁ * n⌋₊ → S.card = ⌊b₂ * n⌋₊ + 1 →
      gnpProb n p (fun G => (S : Set (Fin n)) ⊆ majorityStep G B) ≤
        Real.exp (-(p * n * (b₂ * n) * g)) := by
    intro B S hB hS
    have h1 := sparseAux_prob_subset_le hp0 hp1 B S htpos
    rw [sparseAux_sum_exp_X] at h1
    have hSB : ((S \ B).card : ℝ) ≤ S.card := by
      exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    have hfT := sparseAux_f_le_T (n := n) (x := b₁) (y := b₂) (E := E) (β := B.card)
      (s := S.card) (a := (S \ B).card) hb₂.le hb hE1 (by rw [hB]) (by rw [hS]; push_cast; ring)
      (Nat.cast_nonneg _) hSB hnice
    have hcoef : 0 ≤ p * (1 - Real.exp (-t)) := by
      apply mul_nonneg hp0.le
      rw [sub_nonneg, Real.exp_neg]; exact inv_le_one_of_one_le₀ hE1.le
    have hSy : b₂ * n ≤ S.card := by
      rw [hS]; push_cast
      have := Nat.lt_floor_add_one (b₂ * n)
      linarith
    calc gnpProb n p (fun G => (S : Set (Fin n)) ⊆ majorityStep G B)
        ≤ Real.exp (p * ((1 - Real.exp (-t)) *
            sparseAux_f E S.card (n - B.card) B.card (S \ B).card)) := h1
      _ ≤ Real.exp (p * (1 - Real.exp (-t)) *
            (1 / 2 * S.card * n * (b₁ * (E ^ 2 + E + 2) - 2))) := by
          rw [← mul_assoc]
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hfT hcoef)
      _ = Real.exp (-(p * n * S.card * g)) := by
          congr 1
          rw [Real.exp_neg, ← hE]
          have : (1 - E⁻¹) * (b₁ * (E ^ 2 + E + 2) / 2 - 1) = -g := hgt
          linear_combination (p * n * S.card) * this
      _ ≤ Real.exp (-(p * n * (b₂ * n) * g)) := by
          gcongr
  -- The union bound over `B ∈ C(V, ⌊xn⌋)` and `S ∈ C(V, ⌊yn⌋ + 1)`.
  set Pairs := (Finset.univ.powersetCard ⌊b₁ * n⌋₊ : Finset (Finset (Fin n))) ×ˢ
    (Finset.univ.powersetCard (⌊b₂ * n⌋₊ + 1) : Finset (Finset (Fin n))) with hPairs
  have hbad : ∀ G : SimpleGraph (Fin n), ¬ (∀ B : Set (Fin n), (B.ncard : ℝ) ≤ b₁ * n →
      ((majorityStep G B).ncard : ℝ) ≤ b₂ * n) →
        ∃ BS ∈ Pairs, (BS.2 : Set (Fin n)) ⊆ majorityStep G BS.1 := by
    intro G hG
    push Not at hG
    obtain ⟨B', hB', hbig⟩ := hG
    -- enlarge the Blue set to exactly `⌊xn⌋` vertices (majority dynamics is monotone)
    have hcard' : B'.toFinset.card ≤ ⌊b₁ * n⌋₊ := by
      rw [← Set.ncard_eq_toFinset_card']; exact Nat.le_floor hB'
    have hkn : ⌊b₁ * n⌋₊ ≤ (Finset.univ : Finset (Fin n)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      apply Nat.floor_le_of_le
      nlinarith
    obtain ⟨B, hB'B, -, hBcard⟩ :=
      Finset.exists_subsuperset_card_eq (Finset.subset_univ B'.toFinset) hcard' hkn
    have hsubB : B' ⊆ (B : Set (Fin n)) := by
      intro v hv; exact hB'B (Set.mem_toFinset.mpr hv)
    have hmono := majorityStep_mono G hsubB
    -- at least `⌊yn⌋ + 1` vertices are Blue tomorrow; pick `S` among them
    have hM : ⌊b₂ * n⌋₊ + 1 ≤ (majorityStep G B).toFinset.card := by
      rw [← Set.ncard_eq_toFinset_card']
      have h1 : (majorityStep G B').ncard ≤ (majorityStep G B).ncard :=
        Set.ncard_le_ncard hmono
      have h2 : ⌊b₂ * n⌋₊ < (majorityStep G B').ncard :=
        (Nat.floor_lt (by positivity)).mpr hbig
      omega
    obtain ⟨S, hSM, hScard⟩ := Finset.exists_subset_card_eq hM
    refine ⟨(B, S), Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, hBcard⟩, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hScard⟩⟩, ?_⟩
    intro v hv
    exact Set.mem_toFinset.mp (hSM (Finset.mem_coe.mp hv))
  have hchoose := sparseAux_choose_mul_le (n := n) (by omega) hb₂ hb (x := b₁) (by
    have : 1 / (n : ℝ) ≤ 2 / Real.sqrt n := by
      rw [div_le_div_iff₀ hn0 hsqrt]
      have : Real.sqrt n ≤ n := by
        rw [Real.sqrt_le_left (by positivity)]; nlinarith
      linarith
    linarith)
  apply le_gnpProb_of_not_le
  calc gnpProb n p (fun G => ¬ ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ b₁ * n →
        ((majorityStep G B).ncard : ℝ) ≤ b₂ * n)
      ≤ gnpProb n p (fun G => ∃ BS ∈ Pairs, (BS.2 : Set (Fin n)) ⊆ majorityStep G BS.1) :=
        gnpProb_mono hbad
    _ ≤ ∑ BS ∈ Pairs, gnpProb n p (fun G => (BS.2 : Set (Fin n)) ⊆ majorityStep G BS.1) :=
        gnpProb_exists_le Pairs _
    _ ≤ ∑ BS ∈ Pairs, Real.exp (-(p * n * (b₂ * n) * g)) := by
        refine Finset.sum_le_sum fun BS hBS => ?_
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hBS
        exact hpair BS.1 BS.2 (Finset.mem_powersetCard.mp h1).2 (Finset.mem_powersetCard.mp h2).2
    _ = ((n.choose ⌊b₁ * n⌋₊ : ℝ) * n.choose (⌊b₂ * n⌋₊ + 1)) *
          Real.exp (-(p * n * (b₂ * n) * g)) := by
        rw [Finset.sum_const, hPairs, Finset.card_product, Finset.card_powersetCard,
          Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
    _ ≤ (b₂⁻¹ * Real.exp (-(2 * n * h b₁))) * Real.exp (-(p * n * (b₂ * n) * g)) := by
        gcongr
    _ = b₂⁻¹ * Real.exp (-(n * F (p * n) b₂ b₁)) := by
        rw [mul_assoc, ← Real.exp_add]
        unfold F
        rw [← hg]
        ring_nf

/-- **Lemma 2.4** (`S:lem:step2`). For `a > 0` and `b ∈ (0, 1/2)` with `b a² > 3 (log 2) / 2`: if
`|B₁| ≤ n/2 − a n / √(pn)`, then `|B₂| ≤ b n` with probability at least `1 − e^(−Ω(n))`, whichever
vertices are Blue on day 1.

Reading: `e^(−Ω(n))` is `exp(−κ n)` for some `κ > 0` depending on `a` and `b`, for `n` large.
Deviation (hypotheses of Lemma 2.3 as its proof uses them): `2√p ≤ a`, so that
`b₁ = 1/2 − a/√(pn) ≤ 1/2 − 2/√n`, and `b ≤ b₁`. -/
theorem lemma2_4 {a b : ℝ} (ha : 0 < a) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hab : 3 * Real.log 2 / 2 < b * a ^ 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ p : ℝ, 0 < p → p < 1 → 2 * Real.sqrt p ≤ a →
      b ≤ 1 / 2 - a / Real.sqrt (p * n) →
      1 - Real.exp (-(κ * n)) ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
        (B.ncard : ℝ) ≤ n / 2 - a * n / Real.sqrt (p * n) →
          ((majorityStep G B).ncard : ℝ) ≤ b * n) := by
  -- `κ₀ = (4/3) a² b − 2 log 2 > 0` and `κ = κ₀ / 2`.
  set κ₀ := 4 / 3 * a ^ 2 * b - 2 * Real.log 2 with hκ₀
  have hκ₀pos : 0 < κ₀ := by rw [hκ₀]; nlinarith
  refine ⟨κ₀ / 2, by positivity, max 163 ⌈2 * Real.log b⁻¹ / κ₀⌉₊, ?_⟩
  intro n hn p hp0 hp1 ha2 hbb
  have hn163 : 163 ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : (0 : ℝ) < n := by
    have : (163 : ℝ) ≤ n := by exact_mod_cast hn163
    linarith
  have hnN : 2 * Real.log b⁻¹ / κ₀ ≤ n :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hn)
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hspn : Real.sqrt (p * n) = Real.sqrt p * Real.sqrt n := Real.sqrt_mul hp0.le n
  set b₁ := 1 / 2 - a / Real.sqrt (p * n) with hb₁def
  -- `b₁ ≤ 1/2 − 2/√n` because `a ≥ 2√p`
  have hb₁ : b₁ ≤ 1 / 2 - 2 / Real.sqrt n := by
    have : 2 / Real.sqrt n ≤ a / Real.sqrt (p * n) := by
      rw [hspn, div_le_div_iff₀ hsn (by positivity)]
      nlinarith
    rw [hb₁def]; linarith
  have h23 := lemma2_3 hn163 hp0 hp1 hb0 hbb hb₁
  -- `F(pn, b, b₁) ≥ (4/3) a² b − 2 log 2`
  have hF : κ₀ ≤ F (p * n) b b₁ := by
    have hb₁0 : 0 ≤ b₁ := le_trans hb0.le hbb
    have hb₁half : b₁ ≤ 1 / 2 := by
      have : 0 ≤ a / Real.sqrt (p * n) := by positivity
      rw [hb₁def]; linarith
    have hT := Real.one_sub_two_mul_sq_div_three_le hb₁0 hb₁half
    have hsq : (1 - 2 * b₁) ^ 2 / 3 = 4 * a ^ 2 / (3 * (p * n)) := by
      rw [hb₁def, show 1 - 2 * (1 / 2 - a / Real.sqrt (p * n)) = 2 * a / Real.sqrt (p * n) by ring,
        div_pow, Real.sq_sqrt (by positivity)]
      ring
    have hh : -Real.log 2 ≤ h b₁ := by
      rw [sparseAux_h_eq]; linarith [Real.binEntropy_le_log_two (p := b₁)]
    have hpn : 0 < p * n := by positivity
    unfold F
    have h1 : p * n * b * (4 * a ^ 2 / (3 * (p * n))) = 4 / 3 * a ^ 2 * b := by
      field_simp
    have h2 : p * n * b * (4 * a ^ 2 / (3 * (p * n))) ≤
        p * n * b * (1 - b₁ / 2 - 3 / 2 * b₁ ^ (1 / 3 : ℝ) * (1 - b₁) ^ (2 / 3 : ℝ)) := by
      rw [← hsq]; gcongr
    rw [hκ₀]; linarith
  -- `b⁻¹ e^{−n F} ≤ b⁻¹ e^{−n κ₀} ≤ e^{−κ₀ n / 2}` for `n ≥ 2 log(1/b)/κ₀`
  have hexp : b⁻¹ * Real.exp (-(n * F (p * n) b b₁)) ≤ Real.exp (-(κ₀ / 2 * n)) := by
    have h1 : b⁻¹ * Real.exp (-(n * F (p * n) b b₁)) ≤ b⁻¹ * Real.exp (-(n * κ₀)) := by
      gcongr
    have h2 : b⁻¹ * Real.exp (-(n * κ₀)) = Real.exp (Real.log b⁻¹ - n * κ₀) := by
      rw [Real.exp_sub, Real.exp_log (inv_pos.mpr hb0), Real.exp_neg]; ring
    have h3 : Real.log b⁻¹ - n * κ₀ ≤ -(κ₀ / 2 * n) := by
      rw [div_le_iff₀ hκ₀pos] at hnN; linarith
    calc b⁻¹ * Real.exp (-(n * F (p * n) b b₁)) ≤ b⁻¹ * Real.exp (-(n * κ₀)) := h1
      _ = Real.exp (Real.log b⁻¹ - n * κ₀) := h2
      _ ≤ Real.exp (-(κ₀ / 2 * n)) := Real.exp_le_exp.mpr h3
  -- the event of Lemma 2.3 with `b₁ n = n/2 − a n/√(pn)`
  have hev : (fun G : SimpleGraph (Fin n) => ∀ B : Set (Fin n),
      (B.ncard : ℝ) ≤ n / 2 - a * n / Real.sqrt (p * n) → ((majorityStep G B).ncard : ℝ) ≤ b * n) =
      (fun G => ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ b₁ * n →
        ((majorityStep G B).ncard : ℝ) ≤ b * n) := by
    have : (n : ℝ) / 2 - a * n / Real.sqrt (p * n) = b₁ * n := by rw [hb₁def]; ring
    simp only [this]
  rw [hev]
  linarith

end PowerOfFew.Sparse

end
