module

public import PowerOfFew.External.FeigeOfek.Defs
public import PowerOfFew.Model.Gnp
public import Basic.Probability.Chernoff
public import Basic.Combinatorics.Choose

/-!
# Bounded degrees and discrepancy of `G(n, p)`

For `pn ≥ c log n`, with probability at least `1 − n^(−a)`, every degree of `G(n, p)` is at most
`c₁ pn` and the discrepancy property holds (Feige–Ofek 2005, Section 2.2; Chin–Rao–Vu 2015, their
lemma on the degree and discrepancy properties):

* a degree is `Bin(n − 1, p)`, and `P(Bin(n − 1, p) ≥ c₁ pn) ≤ (e / c₁)^(c₁ pn) ≤ n^(−c₁ c log(c₁/e))`
  (`IsBernoulliFamily.measureReal_sum_ge_le_exp_mul_log`), then a union bound over the vertices;
* for sets `S, T` with `m = max(|S|, |T|) > n/e`, bounded degrees give
  `e(S, T) ≤ c₁ d min(|S|, |T|) ≤ c₁ e μ(S, T)`;
* for `m ≤ n/e`, `e(S, T)` is at most twice a `Bin(N, p)` variable with `N ≤ |S| |T|` (the edges
  with one end in `S` and the other in `T`), so `P(e(S, T) ≥ λ μ) ≤ (2e/λ)^(λμ/2)`; with `λ` the
  least value that violates both alternatives this is at most `exp(−(c₃/4) m log(n/m))`, while the
  number of pairs of sets of sizes `s, t ≤ m` is at most `(en/m)^(2m) ≤ exp(4 m log(n/m))`.

The constants are `c₁ = e^(1 + (a + 2)/c)` (so that `c₁ ≥ e` and `c₁ c log(c₁/e) ≥ a + 2`),
`c₂ = max(4e², e c₁)` and `c₃ = 4(a + 9)`. Bounded degrees fail with probability at most
`n · n^(−(a + 2))`. On bounded degrees, a pair `(S, T)` that violates both alternatives has
`1 ≤ |S|, |T|` and `m ≤ n/e`; the least natural number `k*` that violates both satisfies
`k*/μ > c₂ ≥ 4e²`, so `(2eμ/k*)^(k*/2) ≤ exp(−(k*/4) log(k*/μ))`; and `m log(n/m) ≥ log n`, so the
union bound over the sizes gives `(n + 1)² n^(−(c₃/4 − 4)) ≤ n^(−(a + 1))`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.FeigeOfek

/-! ### Elementary inequalities -/

/-- `C(n, s) ≤ (e n / s)^s = exp(s (1 + log(n / s)))` for `s ≥ 1`. -/
private lemma fo4Aux_choose_le_exp {n s : ℕ} (hs : 1 ≤ s) :
    (n.choose s : ℝ) ≤ Real.exp (s * (1 + Real.log (n / s))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    exact (Real.exp_pos _).le
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : (0 : ℝ) < s.factorial := by exact_mod_cast s.factorial_pos
  calc (n.choose s : ℝ) ≤ (n : ℝ) ^ s / s.factorial := Nat.choose_le_pow_div s n
    _ = ((n : ℝ) / s) ^ s * ((s : ℝ) ^ s / s.factorial) := by
        rw [div_pow]
        field_simp
    _ ≤ ((n : ℝ) / s) ^ s * Real.exp s := by
        gcongr
        exact Real.pow_div_factorial_le_exp _ hs'.le s
    _ = Real.exp (s * (1 + Real.log (n / s))) := by
        rw [show (s : ℝ) * (1 + Real.log (n / s)) = s * Real.log (n / s) + s by ring,
          Real.exp_add, ← Real.log_pow, Real.exp_log (by positivity)]

/-- `x (1 + log(n / x))` is nondecreasing on `(0, n]`. -/
private lemma fo4Aux_mul_one_add_log_le {n s m : ℝ} (hs : 0 < s) (hsm : s ≤ m) (hmn : m ≤ n) :
    s * (1 + Real.log (n / s)) ≤ m * (1 + Real.log (n / m)) := by
  have hm : 0 < m := hs.trans_le hsm
  have hn : 0 < n := hm.trans_le hmn
  have h1 : Real.log (n / s) = Real.log (n / m) + Real.log (m / s) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have h3 : 0 ≤ Real.log (n / m) := Real.log_nonneg (by rw [le_div_iff₀ hm]; linarith)
  have h4 : s * Real.log (m / s) ≤ m - s := by
    calc s * Real.log (m / s) ≤ s * (m / s - 1) := by
          gcongr
          exact Real.log_le_sub_one_of_pos (by positivity)
      _ = m - s := by field_simp
  have h5 : s * Real.log (n / m) ≤ m * Real.log (n / m) := mul_le_mul_of_nonneg_right hsm h3
  rw [h1]
  nlinarith

/-- `log n ≤ m log(n / m)` for `1 ≤ m ≤ n / e`. -/
private lemma fo4Aux_log_le_mul_log {n m : ℝ} (hm : 1 ≤ m) (hmn : Real.exp 1 * m ≤ n) :
    Real.log n ≤ m * Real.log (n / m) := by
  have hm0 : 0 < m := by linarith
  have hn : 0 < n := lt_of_lt_of_le (by positivity) hmn
  have h1 : 1 ≤ Real.log (n / m) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hm0]
    exact hmn
  have h2 : Real.log m ≤ m - 1 := Real.log_le_sub_one_of_pos hm0
  have h3 : Real.log n = Real.log (n / m) + Real.log m := by
    rw [← Real.log_mul (by positivity) hm0.ne']
    congr 1
    field_simp
  have h4 : 0 ≤ (m - 1) * (Real.log (n / m) - 1) := mul_nonneg (by linarith) (by linarith)
  rw [h3]
  nlinarith

/-- The number of pairs of sets of sizes `s, t`: `C(n, s) C(n, t) ≤ exp(4 m log(n / m))` for
`1 ≤ s, t` and `m = max(s, t) ≤ n / e`. -/
private lemma fo4Aux_choose_mul_choose_le {n s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hm : Real.exp 1 * max (s : ℝ) t ≤ n) :
    (n.choose s : ℝ) * n.choose t ≤
      Real.exp (4 * (max (s : ℝ) t * Real.log (n / max (s : ℝ) t))) := by
  set m := max (s : ℝ) t
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hsm : (s : ℝ) ≤ m := le_max_left _ _
  have htm : (t : ℝ) ≤ m := le_max_right _ _
  have hm1 : 1 ≤ m := hs'.trans hsm
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hmn : m ≤ n := by nlinarith
  have hm0 : 0 < m := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 1 ≤ Real.log (n / m) := by
    rw [Real.le_log_iff_exp_le (div_pos hn0 hm0), le_div_iff₀ hm0]
    exact hm
  have h1 := fo4Aux_choose_le_exp (n := n) hs
  have h2 := fo4Aux_choose_le_exp (n := n) ht
  have h3 := fo4Aux_mul_one_add_log_le (n := n) (by linarith) hsm hmn
  have h4 := fo4Aux_mul_one_add_log_le (n := n) (by linarith) htm hmn
  have h5 : m * 1 ≤ m * Real.log (n / m) := mul_le_mul_of_nonneg_left hlog (by positivity)
  calc (n.choose s : ℝ) * n.choose t
      ≤ Real.exp (s * (1 + Real.log (n / s))) * Real.exp (t * (1 + Real.log (n / t))) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = Real.exp (s * (1 + Real.log (n / s)) + t * (1 + Real.log (n / t))) :=
        (Real.exp_add _ _).symm
    _ ≤ Real.exp (4 * (m * Real.log (n / m))) := by
        rw [Real.exp_le_exp]
        nlinarith

/-! ### Edge counts as sums of edge indicators -/

/-- The entries of the adjacency matrix of `graphOfEdges ω` are edge indicators. -/
private lemma fo4Aux_adjMat_graphOfEdges {n : ℕ} (ω : EdgeVars n) (u v : Fin n) :
    adjMat (graphOfEdges ω) u v =
      if ¬ (s(u, v) : Sym2 (Fin n)).IsDiag then edgeInd s(u, v) ω else 0 := by
  classical
  simp only [adjMat, Matrix.of_apply, edgeInd, Sym2.mk_isDiag_iff, adj_graphOfEdges]
  split_ifs <;> simp_all

/-- A sum of edge indicators over the off-diagonal pairs of a set of unordered pairs. -/
private lemma fo4Aux_sum_subtype {n : ℕ} (s : Finset (Sym2 (Fin n))) (ω : EdgeVars n) :
    ∑ z ∈ s.subtype (fun z => ¬ z.IsDiag), edgeInd z.1 ω =
      ∑ z ∈ s, if ¬ z.IsDiag then edgeInd z ω else 0 := by
  rw [Finset.sum_subtype_eq_sum_filter (f := fun z => edgeInd z ω), Finset.sum_filter]

/-- The degree of `u` in `graphOfEdges ω` is a sum of at most `n` edge indicators. -/
private lemma fo4Aux_exists_degree {n : ℕ} (u : Fin n) :
    ∃ P : Finset (OffDiag n), (P.card : ℝ) ≤ n ∧
      ∀ ω : EdgeVars n, ∑ v, adjMat (graphOfEdges ω) u v = ∑ z ∈ P, edgeInd z.1 ω := by
  classical
  refine ⟨((Finset.univ : Finset (Fin n)).image (fun v => s(u, v))).subtype
    (fun z => ¬ z.IsDiag), ?_, fun ω => ?_⟩
  · rw [Finset.card_subtype]
    have h1 := Finset.card_filter_le ((Finset.univ : Finset (Fin n)).image (fun v => s(u, v)))
      (fun z => ¬ z.IsDiag)
    have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := fun v => s(u, v))
    rw [Finset.card_univ, Fintype.card_fin] at h2
    exact_mod_cast h1.trans h2
  · rw [fo4Aux_sum_subtype, Finset.sum_image (fun v _ w _ h => Sym2.congr_right.1 h)]
    exact Finset.sum_congr rfl fun v _ => fo4Aux_adjMat_graphOfEdges ω u v

/-- `e(S, T)` in `graphOfEdges ω` is at most twice a sum of at most `|S| |T|` edge indicators:
the pairs with one end in `S` and the other in `T`. -/
private lemma fo4Aux_exists_pairs {n : ℕ} (S T : Finset (Fin n)) :
    ∃ P : Finset (OffDiag n), (P.card : ℝ) ≤ S.card * T.card ∧
      ∀ ω : EdgeVars n, edgeCount (graphOfEdges ω) S T ≤ 2 * ∑ z ∈ P, edgeInd z.1 ω := by
  classical
  set g : Fin n × Fin n → Sym2 (Fin n) := fun x => s(x.1, x.2)
  refine ⟨((S ×ˢ T).image g).subtype (fun z => ¬ z.IsDiag), ?_, fun ω => ?_⟩
  · rw [Finset.card_subtype]
    have h1 := Finset.card_filter_le ((S ×ˢ T).image g) (fun z => ¬ z.IsDiag)
    have h2 := Finset.card_image_le (s := S ×ˢ T) (f := g)
    rw [Finset.card_product] at h2
    exact_mod_cast h1.trans h2
  · set F : Sym2 (Fin n) → ℝ := fun z => if ¬ z.IsDiag then edgeInd z ω else 0 with hF
    have hF0 : ∀ z, 0 ≤ F z := by
      intro z
      simp only [hF, edgeInd]
      split_ifs <;> norm_num
    rw [fo4Aux_sum_subtype]
    calc edgeCount (graphOfEdges ω) S T = ∑ x ∈ S ×ˢ T, F (g x) := by
          rw [edgeCount, Finset.sum_product]
          exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
            fo4Aux_adjMat_graphOfEdges ω u v
      _ = ∑ z ∈ (S ×ˢ T).image g, (Finset.filter (fun x => g x = z) (S ×ˢ T)).card • F z :=
          Finset.sum_comp F g
      _ ≤ ∑ z ∈ (S ×ˢ T).image g, 2 * F z := by
          refine Finset.sum_le_sum fun z hz => ?_
          rw [nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (hF0 z)
          obtain ⟨x0, -, rfl⟩ := Finset.mem_image.1 hz
          have hsub : Finset.filter (fun x => g x = g x0) (S ×ˢ T) ⊆
              {(x0.1, x0.2), (x0.2, x0.1)} := by
            intro x hx
            rw [Finset.mem_filter] at hx
            rcases Sym2.eq_iff.1 hx.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · simp [Prod.ext_iff, h1, h2]
            · simp [Prod.ext_iff, h1, h2]
          have := (Finset.card_le_card hsub).trans Finset.card_le_two
          exact_mod_cast this
      _ = 2 * ∑ z ∈ (S ×ˢ T).image g, F z := (Finset.mul_sum _ _ _).symm

/-- `e(S, T)` is a natural number. -/
private lemma fo4Aux_edgeCount_natCast {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n)) :
    ∃ N : ℕ, edgeCount G S T = N := by
  classical
  refine ⟨∑ u ∈ S, ∑ v ∈ T, if G.Adj u v then 1 else 0, ?_⟩
  simp [edgeCount, adjMat]

/-- The entries of an adjacency matrix are nonnegative. -/
private lemma fo4Aux_adjMat_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    0 ≤ adjMat G u v := by
  classical
  simp only [adjMat, Matrix.of_apply]
  split_ifs <;> norm_num

/-- An adjacency matrix is symmetric. -/
private lemma fo4Aux_adjMat_comm {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    adjMat G u v = adjMat G v u := by
  classical
  simp only [adjMat, Matrix.of_apply, G.adj_comm]

/-- `e(S, T) = e(T, S)`. -/
private lemma fo4Aux_edgeCount_comm {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n)) :
    edgeCount G S T = edgeCount G T S := by
  calc edgeCount G S T = ∑ v ∈ T, ∑ u ∈ S, adjMat G u v := Finset.sum_comm
    _ = edgeCount G T S :=
        Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => fo4Aux_adjMat_comm G u v

/-- Bounded degrees bound `e(S, T)` by `c₁ d |S|`. -/
private lemma fo4Aux_edgeCount_le_left {n : ℕ} {G : SimpleGraph (Fin n)} {d c₁ : ℝ}
    (h : DegreeBound G d c₁) (S T : Finset (Fin n)) :
    edgeCount G S T ≤ c₁ * d * S.card := by
  calc edgeCount G S T = ∑ u ∈ S, ∑ v ∈ T, adjMat G u v := rfl
    _ ≤ ∑ u ∈ S, ∑ v, adjMat G u v :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ T) fun v _ _ => fo4Aux_adjMat_nonneg G u v
    _ ≤ ∑ u ∈ S, c₁ * d := Finset.sum_le_sum fun u _ => h u
    _ = c₁ * d * S.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-! ### The probability bounds -/

/-- An event that never happens has probability `0`. -/
private lemma fo4Aux_gnpProb_eq_zero {n : ℕ} {p : ℝ} {P : SimpleGraph (Fin n) → Prop}
    (h : ∀ G, ¬ P G) : gnpProb n p P = 0 := by
  have : {G : SimpleGraph (Fin n) | P G} = ∅ := Set.eq_empty_of_forall_notMem fun G hG => h G hG
  rw [gnpProb, this, measureReal_empty]

/-- **Degrees.** A vertex has more than `c₁ pn` neighbours with probability at most
`n^(−(a + 2))`: its degree is a sum of at most `n` edge indicators, so the sharp Chernoff bound
gives `(e / c₁)^(c₁ pn) ≤ n^(−c₁ c log(c₁/e)) ≤ n^(−(a + 2))`. -/
private lemma fo4Aux_prob_degree_gt_le {n : ℕ} {p c c₁ a : ℝ} (hn : 2 ≤ n) (hp0 : 0 < p)
    (hp1 : p ≤ 1) (hcp : c * Real.log n ≤ p * n) (hc₁e : Real.exp 1 ≤ c₁)
    (hc₁ : a + 2 ≤ c₁ * c * Real.log (c₁ / Real.exp 1)) (u : Fin n) :
    gnpProb n p (fun G => c₁ * (p * n) < ∑ v, adjMat G u v) ≤ (n : ℝ) ^ (-(a + 2)) := by
  obtain ⟨P, hPcard, hPsum⟩ := fo4Aux_exists_degree u
  have hn' : (0 : ℝ) < n := by positivity
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hc₁0 : 0 < c₁ := he.trans_le hc₁e
  have hd : 0 < c₁ * (p * n) := by positivity
  rw [gnpProb_eq]
  have hsub : {ω : EdgeVars n | c₁ * (p * n) < ∑ v, adjMat (graphOfEdges ω) u v} ⊆
      {ω | c₁ * (p * n) ≤ ∑ z ∈ P, edgeInd z.1 ω} := by
    intro ω hω
    have h : c₁ * (p * n) < ∑ v, adjMat (graphOfEdges ω) u v := hω
    show c₁ * (p * n) ≤ ∑ z ∈ P, edgeInd z.1 ω
    rw [← hPsum ω]
    exact h.le
  refine (measureReal_mono hsub).trans ?_
  rcases Nat.eq_zero_or_pos P.card with hP0 | hP0
  · rw [Finset.card_eq_zero] at hP0
    subst hP0
    have : {ω : EdgeVars n | c₁ * (p * n) ≤ ∑ z ∈ (∅ : Finset (OffDiag n)), edgeInd z.1 ω} =
        ∅ := by
      ext ω
      simp only [Finset.sum_empty, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact hd
    rw [this, measureReal_empty]
    positivity
  · have hP' : (0 : ℝ) < P.card := by exact_mod_cast hP0
    have hX := isBernoulliFamily_edgeInd (n := n) hp0.le hp1
    refine (hX.measureReal_sum_ge_le_exp_mul_log hp0.le hp1 P hd).trans ?_
    rw [Real.rpow_def_of_pos hn', Real.exp_le_exp]
    have h1 : c₁ / Real.exp 1 ≤ c₁ * (p * n) / (Real.exp 1 * (p * P.card)) := by
      rw [div_le_div_iff₀ he (by positivity)]
      have h0 : c₁ * p * P.card ≤ c₁ * p * n := mul_le_mul_of_nonneg_left hPcard (by positivity)
      nlinarith
    have h2 : Real.log (c₁ / Real.exp 1) ≤
        Real.log (c₁ * (p * n) / (Real.exp 1 * (p * P.card))) :=
      Real.log_le_log (by positivity) h1
    have h3 : 0 ≤ Real.log (c₁ / Real.exp 1) :=
      Real.log_nonneg (by rw [le_div_iff₀ he]; linarith)
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have h4 : c₁ * (p * n) * Real.log (c₁ / Real.exp 1) ≤
        c₁ * (p * n) * Real.log (c₁ * (p * n) / (Real.exp 1 * (p * P.card))) :=
      mul_le_mul_of_nonneg_left h2 hd.le
    have h5 : c₁ * (c * Real.log n) * Real.log (c₁ / Real.exp 1) ≤
        c₁ * (p * n) * Real.log (c₁ / Real.exp 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcp hc₁0.le) h3
    have h6 : (a + 2) * Real.log n ≤ c₁ * c * Real.log (c₁ / Real.exp 1) * Real.log n :=
      mul_le_mul_of_nonneg_right hc₁ hlogn
    nlinarith

/-- **Bounded degrees fail** with probability at most `n · n^(−(a + 2)) = n^(−(a + 1))`. -/
private lemma fo4Aux_prob_not_degreeBound {n : ℕ} {p c c₁ a : ℝ} (hn : 2 ≤ n) (hp0 : 0 < p)
    (hp1 : p ≤ 1) (hcp : c * Real.log n ≤ p * n) (hc₁e : Real.exp 1 ≤ c₁)
    (hc₁ : a + 2 ≤ c₁ * c * Real.log (c₁ / Real.exp 1)) :
    gnpProb n p (fun G => ¬ DegreeBound G (p * n) c₁) ≤ (n : ℝ) ^ (-(a + 1)) := by
  have hn' : (0 : ℝ) < n := by positivity
  calc gnpProb n p (fun G => ¬ DegreeBound G (p * n) c₁)
      ≤ gnpProb n p (fun G => ∃ u ∈ (Finset.univ : Finset (Fin n)),
          c₁ * (p * n) < ∑ v, adjMat G u v) := by
        refine gnpProb_mono fun G hG => ?_
        unfold DegreeBound at hG
        push Not at hG
        obtain ⟨u, hu⟩ := hG
        exact ⟨u, Finset.mem_univ u, hu⟩
    _ ≤ ∑ u ∈ (Finset.univ : Finset (Fin n)),
          gnpProb n p (fun G => c₁ * (p * n) < ∑ v, adjMat G u v) := gnpProb_exists_le _ _
    _ ≤ ∑ u ∈ (Finset.univ : Finset (Fin n)), (n : ℝ) ^ (-(a + 2)) :=
        Finset.sum_le_sum fun u _ => fo4Aux_prob_degree_gt_le hn hp0 hp1 hcp hc₁e hc₁ u
    _ = (n : ℝ) ^ (-(a + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          show -(a + 1) = 1 + -(a + 2) by ring, Real.rpow_add hn', Real.rpow_one]

/-- **One pair of sets.** For nonempty `S, T`, with `μ = |S| |T| pn / n` and
`m = max(|S|, |T|)`, both alternatives of the discrepancy property fail for `(S, T)` with
probability at most `exp(−(c₃/4) m log(n/m))` when `c₂ ≥ 4e²`: with `k*` the least natural
number violating both, `e(S, T) ≥ k*` forces the sum `Z` of at most `|S| |T|` edge indicators to be
at least `k*/2`, and `P(Z ≥ k*/2) ≤ (2eμ/k*)^(k*/2) ≤ exp(−(k*/4) log(k*/μ))`. -/
private lemma fo4Aux_prob_bad_le {n : ℕ} {p c₂ c₃ : ℝ} (hn : 1 ≤ n) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hc₂ : 4 * Real.exp 1 ^ 2 ≤ c₂) (S T : Finset (Fin n)) (hS : 1 ≤ S.card)
    (hT : 1 ≤ T.card) :
    gnpProb n p (fun G => c₂ * (S.card * T.card * (p * n) / n) < edgeCount G S T ∧
        c₃ * max (S.card : ℝ) T.card * Real.log (n / max (S.card : ℝ) T.card) <
          edgeCount G S T * Real.log (edgeCount G S T / (S.card * T.card * (p * n) / n))) ≤
      Real.exp (-(c₃ * max (S.card : ℝ) T.card * Real.log (n / max (S.card : ℝ) T.card) / 4)) := by
  classical
  set μ : ℝ := S.card * T.card * (p * n) / n with hμ_def
  set L : ℝ := c₃ * max (S.card : ℝ) T.card * Real.log (n / max (S.card : ℝ) T.card)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hS' : (1 : ℝ) ≤ S.card := by exact_mod_cast hS
  have hT' : (1 : ℝ) ≤ T.card := by exact_mod_cast hT
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hμ : μ = S.card * T.card * p := by
    rw [hμ_def]
    field_simp
  have hμ0 : 0 < μ := by
    rw [hμ]
    positivity
  by_cases hex : ∃ k : ℕ, c₂ * μ < k ∧ L < k * Real.log (k / μ)
  · obtain ⟨P, hPcard, hPsum⟩ := fo4Aux_exists_pairs S T
    obtain ⟨hk1, hk2⟩ := Nat.find_spec hex
    set k : ℕ := Nat.find hex
    have hc₂0 : 0 ≤ c₂ := le_trans (by positivity) hc₂
    have hkpos : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hk1
    rw [gnpProb_eq]
    have hsub : {ω : EdgeVars n | c₂ * μ < edgeCount (graphOfEdges ω) S T ∧
        L < edgeCount (graphOfEdges ω) S T * Real.log (edgeCount (graphOfEdges ω) S T / μ)} ⊆
        {ω | (k : ℝ) / 2 ≤ ∑ z ∈ P, edgeInd z.1 ω} := by
      intro ω hω
      obtain ⟨h1, h2⟩ := hω
      obtain ⟨N, hN⟩ := fo4Aux_edgeCount_natCast (graphOfEdges ω) S T
      rw [hN] at h1 h2
      have hkN : k ≤ N := Nat.find_min' hex ⟨h1, h2⟩
      have hkN' : (k : ℝ) ≤ N := by exact_mod_cast hkN
      have h3 := hPsum ω
      rw [hN] at h3
      show (k : ℝ) / 2 ≤ ∑ z ∈ P, edgeInd z.1 ω
      linarith
    refine (measureReal_mono hsub).trans ?_
    rcases Nat.eq_zero_or_pos P.card with hP0 | hP0
    · rw [Finset.card_eq_zero] at hP0
      subst hP0
      have : {ω : EdgeVars n | (k : ℝ) / 2 ≤ ∑ z ∈ (∅ : Finset (OffDiag n)), edgeInd z.1 ω} =
          ∅ := by
        ext ω
        simp only [Finset.sum_empty, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
          not_le]
        linarith
      rw [this, measureReal_empty]
      positivity
    · have hP' : (0 : ℝ) < P.card := by exact_mod_cast hP0
      have hX := isBernoulliFamily_edgeInd (n := n) hp0.le hp1
      refine (hX.measureReal_sum_ge_le_exp_mul_log hp0.le hp1 P (by positivity)).trans ?_
      rw [Real.exp_le_exp]
      -- `(k/2) / (e p #P) ≥ k / (2eμ)`, as `#P ≤ |S| |T|` and `μ = |S| |T| p`
      have h1 : (k : ℝ) / (2 * Real.exp 1 * μ) ≤ (k / 2) / (Real.exp 1 * (p * P.card)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity), hμ]
        have h0 : p * P.card ≤ p * (S.card * T.card) := mul_le_mul_of_nonneg_left hPcard hp0.le
        have h0' : (k : ℝ) * Real.exp 1 * (p * P.card) ≤
            k * Real.exp 1 * (p * (S.card * T.card)) :=
          mul_le_mul_of_nonneg_left h0 (by positivity)
        nlinarith
      have h2 : Real.log (k / (2 * Real.exp 1 * μ)) ≤
          Real.log ((k / 2) / (Real.exp 1 * (p * P.card))) :=
        Real.log_le_log (by positivity) h1
      -- `log(k / (2eμ)) ≥ log(k/μ) / 2`, as `k / μ > c₂ ≥ 4e²`
      have h3 : Real.log (k / μ) / 2 ≤ Real.log (k / (2 * Real.exp 1 * μ)) := by
        have hkμ : (2 * Real.exp 1) ^ 2 ≤ k / μ := by
          rw [le_div_iff₀ hμ0]
          nlinarith
        have h4 : Real.log (k / (2 * Real.exp 1 * μ)) =
            Real.log (k / μ) - Real.log (2 * Real.exp 1) := by
          rw [← Real.log_div (by positivity) (by positivity)]
          congr 1
          field_simp
        have h5 : Real.log ((2 * Real.exp 1) ^ 2) = 2 * Real.log (2 * Real.exp 1) := by
          rw [Real.log_pow]
          norm_num
        have h6 : Real.log ((2 * Real.exp 1) ^ 2) ≤ Real.log (k / μ) :=
          Real.log_le_log (by positivity) hkμ
        linarith
      have h6 : (k : ℝ) / 2 * (Real.log (k / μ) / 2) ≤
          (k : ℝ) / 2 * Real.log ((k / 2) / (Real.exp 1 * (p * P.card))) :=
        mul_le_mul_of_nonneg_left (h3.trans h2) (by positivity)
      linarith
  · have hnot : ∀ G : SimpleGraph (Fin n), ¬ (c₂ * μ < edgeCount G S T ∧
        L < edgeCount G S T * Real.log (edgeCount G S T / μ)) := by
      rintro G ⟨h1, h2⟩
      obtain ⟨N, hN⟩ := fo4Aux_edgeCount_natCast G S T
      rw [hN] at h1 h2
      exact hex ⟨N, h1, h2⟩
    rw [fo4Aux_gnpProb_eq_zero hnot]
    positivity

/-- The union bound weight of the pairs of sets of sizes `s, t`: `exp(−(c₃/4) m log(n/m))` with
`m = max(s, t)` when `1 ≤ s, t` and `m ≤ n/e`, and `0` otherwise. -/
private def fo4Aux_weight (n : ℕ) (c₃ : ℝ) (s t : ℕ) : ℝ :=
  if 1 ≤ s ∧ 1 ≤ t ∧ Real.exp 1 * max (s : ℝ) t ≤ n then
    Real.exp (-(c₃ * max (s : ℝ) t * Real.log (n / max (s : ℝ) t) / 4))
  else 0

/-- The pairs of sets of sizes `s, t` contribute at most `n^(−(a + 5))`:
`C(n, s) C(n, t) ≤ exp(4 m log(n/m))`, `c₃/4 = a + 9`, and `m log(n/m) ≥ log n`. -/
private lemma fo4Aux_term_le {n : ℕ} {a : ℝ} (ha : 0 < a) (hn : 2 ≤ n) (s t : ℕ) :
    (n.choose s : ℝ) * ((n.choose t : ℝ) * fo4Aux_weight n (4 * (a + 9)) s t) ≤
      (n : ℝ) ^ (-(a + 5)) := by
  have hn' : (0 : ℝ) < n := by positivity
  unfold fo4Aux_weight
  split_ifs with h
  · obtain ⟨hs, ht, hm⟩ := h
    have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hm1 : (1 : ℝ) ≤ max (s : ℝ) t := hs'.trans (le_max_left _ _)
    have h1 := fo4Aux_choose_mul_choose_le hs ht hm
    have h2 := fo4Aux_log_le_mul_log hm1 hm
    rw [← mul_assoc]
    calc (n.choose s : ℝ) * n.choose t *
          Real.exp (-(4 * (a + 9) * max (s : ℝ) t * Real.log (n / max (s : ℝ) t) / 4))
        ≤ Real.exp (4 * (max (s : ℝ) t * Real.log (n / max (s : ℝ) t))) *
          Real.exp (-(4 * (a + 9) * max (s : ℝ) t * Real.log (n / max (s : ℝ) t) / 4)) := by
          gcongr
      _ = Real.exp (-((a + 5) * (max (s : ℝ) t * Real.log (n / max (s : ℝ) t)))) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (-((a + 5) * Real.log n)) := by
          rw [Real.exp_le_exp, neg_le_neg_iff]
          exact mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = (n : ℝ) ^ (-(a + 5)) := by
          rw [Real.rpow_def_of_pos hn']
          congr 1
          ring
  · rw [mul_zero, mul_zero]
    positivity

/-- **Discrepancy.** With `c₂ ≥ max(4e², e c₁)` and `c₃ = 4(a + 9)`, the event that the degrees
are bounded but the discrepancy property fails has probability at most `n^(−(a + 1))`. -/
private lemma fo4Aux_prob_not_discrepancy {n : ℕ} {p c₁ c₂ a : ℝ} (hn : 2 ≤ n) (hp0 : 0 < p)
    (hp1 : p ≤ 1) (ha : 0 < a) (hc₁ : 0 ≤ c₁) (hc₂ : 4 * Real.exp 1 ^ 2 ≤ c₂)
    (hc₂' : Real.exp 1 * c₁ ≤ c₂) :
    gnpProb n p (fun G => DegreeBound G (p * n) c₁ ∧ ¬ Discrepancy G (p * n) c₂ (4 * (a + 9))) ≤
      (n : ℝ) ^ (-(a + 1)) := by
  classical
  have hn' : (0 : ℝ) < n := by positivity
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set c₃ : ℝ := 4 * (a + 9)
  set U : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powerset with hU
  -- the event that `(S, T)` is a pair of small nonempty sets violating both alternatives
  let E : Finset (Fin n) → Finset (Fin n) → SimpleGraph (Fin n) → Prop := fun S T G =>
    (1 ≤ S.card ∧ 1 ≤ T.card ∧ Real.exp 1 * max (S.card : ℝ) T.card ≤ n) ∧
      (c₂ * (S.card * T.card * (p * n) / n) < edgeCount G S T ∧
        c₃ * max (S.card : ℝ) T.card * Real.log (n / max (S.card : ℝ) T.card) <
          edgeCount G S T * Real.log (edgeCount G S T / (S.card * T.card * (p * n) / n)))
  -- (1) with bounded degrees, a pair violating both alternatives consists of small nonempty sets
  have hsub : ∀ G, DegreeBound G (p * n) c₁ ∧ ¬ Discrepancy G (p * n) c₂ c₃ →
      ∃ S ∈ U, ∃ T ∈ U, E S T G := by
    rintro G ⟨hdeg, hdisc⟩
    unfold Discrepancy at hdisc
    push Not at hdisc
    obtain ⟨S, T, h1, h2⟩ := hdisc
    refine ⟨S, Finset.mem_powerset.2 (Finset.subset_univ _), T,
      Finset.mem_powerset.2 (Finset.subset_univ _), ⟨?_, ?_, ?_⟩, h1, h2⟩
    · by_contra hS
      have : S = ∅ := Finset.card_eq_zero.1 (by omega)
      subst this
      simp [edgeCount] at h1
    · by_contra hT
      have : T = ∅ := Finset.card_eq_zero.1 (by omega)
      subst this
      simp [edgeCount] at h1
    · by_contra hm
      push Not at hm
      have hl := fo4Aux_edgeCount_le_left hdeg S T
      have hr := fo4Aux_edgeCount_le_left hdeg T S
      rw [← fo4Aux_edgeCount_comm] at hr
      have hμ : (S.card : ℝ) * T.card * (p * n) / n = S.card * T.card * p := by
        field_simp
      rw [hμ] at h1
      have h3 : Real.exp 1 * c₁ * (S.card * T.card * p) ≤ c₂ * (S.card * T.card * p) :=
        mul_le_mul_of_nonneg_right hc₂' (by positivity)
      rcases le_total (S.card : ℝ) T.card with hst | hst
      · rw [max_eq_right hst] at hm
        have h4 : c₁ * p * S.card * n ≤ c₁ * p * S.card * (Real.exp 1 * T.card) :=
          mul_le_mul_of_nonneg_left hm.le (by positivity)
        nlinarith
      · rw [max_eq_left hst] at hm
        have h4 : c₁ * p * T.card * n ≤ c₁ * p * T.card * (Real.exp 1 * S.card) :=
          mul_le_mul_of_nonneg_left hm.le (by positivity)
        nlinarith
  -- (2) the bound for one pair of sets
  have hE : ∀ S T : Finset (Fin n), gnpProb n p (E S T) ≤ fo4Aux_weight n c₃ S.card T.card := by
    intro S T
    unfold fo4Aux_weight
    by_cases h : 1 ≤ S.card ∧ 1 ≤ T.card ∧ Real.exp 1 * max (S.card : ℝ) T.card ≤ n
    · rw [ite_eq_left h]
      refine le_trans (gnpProb_mono fun G hG => hG.2) ?_
      exact fo4Aux_prob_bad_le (by omega) hp0 hp1 hc₂ S T h.1 h.2.1
    · rw [ite_eq_right h, fo4Aux_gnpProb_eq_zero fun G hG => h hG.1]
  -- (3) the union bound, grouped by the sizes of the sets
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hgroup : ∀ f : ℕ → ℝ, ∑ S ∈ U, f S.card =
      ∑ s ∈ Finset.range (n + 1), n.choose s • f s := by
    intro f
    rw [hU, Finset.sum_powerset_apply_card, hcard]
  calc gnpProb n p (fun G => DegreeBound G (p * n) c₁ ∧ ¬ Discrepancy G (p * n) c₂ c₃)
      ≤ gnpProb n p (fun G => ∃ S ∈ U, ∃ T ∈ U, E S T G) := gnpProb_mono hsub
    _ ≤ ∑ S ∈ U, gnpProb n p (fun G => ∃ T ∈ U, E S T G) := gnpProb_exists_le _ _
    _ ≤ ∑ S ∈ U, ∑ T ∈ U, gnpProb n p (E S T) :=
        Finset.sum_le_sum fun S _ => gnpProb_exists_le _ _
    _ ≤ ∑ S ∈ U, ∑ T ∈ U, fo4Aux_weight n c₃ S.card T.card :=
        Finset.sum_le_sum fun S _ => Finset.sum_le_sum fun T _ => hE S T
    _ = ∑ s ∈ Finset.range (n + 1),
          n.choose s • ∑ t ∈ Finset.range (n + 1), n.choose t • fo4Aux_weight n c₃ s t := by
        rw [← hgroup (fun s => ∑ t ∈ Finset.range (n + 1),
          n.choose t • fo4Aux_weight n c₃ s t)]
        exact Finset.sum_congr rfl fun S _ => hgroup (fun t => fo4Aux_weight n c₃ S.card t)
    _ ≤ ∑ s ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1), (n : ℝ) ^ (-(a + 5)) := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [nsmul_eq_mul, Finset.mul_sum]
        refine Finset.sum_le_sum fun t _ => ?_
        rw [nsmul_eq_mul]
        exact fo4Aux_term_le ha hn s t
    _ = ((n : ℝ) + 1) ^ 2 * (n : ℝ) ^ (-(a + 5)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (n : ℝ) ^ (-(a + 1)) := by
        have h4 : (n : ℝ) ^ (-(a + 1)) = (n : ℝ) ^ (4 : ℝ) * (n : ℝ) ^ (-(a + 5)) := by
          rw [← Real.rpow_add hn']
          congr 1
          ring
        rw [h4]
        have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
        have h5 : ((n : ℝ) + 1) ^ 2 ≤ (n : ℝ) ^ (4 : ℝ) := by
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          have h6 : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by nlinarith
          calc ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h6 2
            _ = (n : ℝ) ^ 4 := by ring
        exact mul_le_mul_of_nonneg_right h5 (by positivity)

/-- **Bounded degrees and discrepancy.** For all `c, a > 0` there are constants `c₁ ≥ 0`, `c₂ ≥ e`
and `c₃ ≥ 0` such that for `n ≥ 2` and `pn ≥ c log n`, with probability at least `1 − n^(−a)`,
every degree of `G(n, p)` is at most `c₁ pn` and `G(n, p)` has the discrepancy property with
constants `c₂, c₃` and expected degree `pn`. -/
theorem exists_degreeBound_discrepancy {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ∃ c₁ c₂ c₃ : ℝ, 0 ≤ c₁ ∧ Real.exp 1 ≤ c₂ ∧ 0 ≤ c₃ ∧
      ∀ (n : ℕ) (p : ℝ), 2 ≤ n → 0 < p → p ≤ 1 → c * Real.log n ≤ p * n →
        gnpProb n p (fun G => ¬ (DegreeBound G (p * n) c₁ ∧ Discrepancy G (p * n) c₂ c₃)) ≤
          (n : ℝ) ^ (-a) := by
  set c₁ : ℝ := Real.exp (1 + (a + 2) / c) with hc₁_def
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hac : 0 < (a + 2) / c := by positivity
  have hc₁e : Real.exp 1 ≤ c₁ := Real.exp_le_exp.2 (by linarith)
  have hc₁ : a + 2 ≤ c₁ * c * Real.log (c₁ / Real.exp 1) := by
    have h1 : Real.log (c₁ / Real.exp 1) = (a + 2) / c := by
      rw [hc₁_def, ← Real.exp_sub, Real.log_exp]
      ring
    have h2 : 1 ≤ c₁ := Real.one_le_exp (by positivity)
    rw [h1, mul_assoc, mul_div_cancel₀ _ hc.ne']
    nlinarith
  refine ⟨c₁, max (4 * Real.exp 1 ^ 2) (Real.exp 1 * c₁), 4 * (a + 9), by positivity, ?_,
    by positivity, ?_⟩
  · refine le_trans ?_ (le_max_left _ _)
    have h1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    nlinarith
  intro n p hn hp0 hp1 hcp
  have hn' : (0 : ℝ) < n := by positivity
  calc gnpProb n p (fun G => ¬ (DegreeBound G (p * n) c₁ ∧
          Discrepancy G (p * n) (max (4 * Real.exp 1 ^ 2) (Real.exp 1 * c₁)) (4 * (a + 9))))
      ≤ gnpProb n p (fun G => ¬ DegreeBound G (p * n) c₁ ∨ (DegreeBound G (p * n) c₁ ∧
          ¬ Discrepancy G (p * n) (max (4 * Real.exp 1 ^ 2) (Real.exp 1 * c₁)) (4 * (a + 9)))) :=
        gnpProb_mono fun G hG => by tauto
    _ ≤ gnpProb n p (fun G => ¬ DegreeBound G (p * n) c₁) +
          gnpProb n p (fun G => DegreeBound G (p * n) c₁ ∧
            ¬ Discrepancy G (p * n) (max (4 * Real.exp 1 ^ 2) (Real.exp 1 * c₁)) (4 * (a + 9))) :=
        gnpProb_or_le _ _
    _ ≤ (n : ℝ) ^ (-(a + 1)) + (n : ℝ) ^ (-(a + 1)) :=
        add_le_add (fo4Aux_prob_not_degreeBound hn hp0 hp1 hcp hc₁e hc₁)
          (fo4Aux_prob_not_discrepancy hn hp0 hp1 ha (by positivity) (le_max_left _ _)
            (le_max_right _ _))
    _ ≤ (n : ℝ) ^ (-a) := by
        have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
        have h3 : (n : ℝ) ^ (-(a + 1)) = (n : ℝ) ^ (-a) / n := by
          rw [show -(a + 1) = -a + -1 by ring, Real.rpow_add hn', Real.rpow_neg_one, div_eq_mul_inv]
        rw [h3]
        have h4 : 0 < (n : ℝ) ^ (-a) := Real.rpow_pos_of_pos hn' _
        rw [← add_div, div_le_iff₀ hn']
        have h5 : (n : ℝ) ^ (-a) * 2 ≤ (n : ℝ) ^ (-a) * n := mul_le_mul_of_nonneg_left h2 h4.le
        linarith

end PowerOfFew.FeigeOfek
