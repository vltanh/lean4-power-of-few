module

public import PowerOfFew.Model.Gnp
public import PowerOfFew.Model.Majority
public import PowerOfFew.Model.EdgeConditioning
public import Basic.Probability.Concentration
public import Basic.Combinatorics.Choose

/-!
# Dense paper, Section 3: Day Two and after

Lemmas 3.2–3.6 of the dense paper (journal version). With high probability the graph shrinks
every Blue set below a threshold, whichever vertices are Blue ("shrinking arguments"), by
Hoeffding's inequality (the paper's Theorem 3.1, `ProbabilityTheory.measureReal_sum_ge_add_le_exp`
and `measureReal_sum_le_sub_le_exp`) and a union bound over all colourings.

Lemmas 3.3, 3.5 and 3.6 are Parts 4, 2 and 3 of Theorem 1.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace PowerOfFew.Dense

/-! ### Lemma 3.2 -/

/-- **Lemma 3.2** (`D:lem:binom-bound`). For integers `n ≥ 1` and `0 ≤ k ≤ n`,
`C(n, k) < 2ⁿ / √n`. -/
theorem lemma3_2 {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    (n.choose k : ℝ) < 2 ^ n / Real.sqrt n := by
  -- `C(n, k) ≤ C(n, ⌊n/2⌋)`
  refine lt_of_le_of_lt (Nat.cast_le.mpr (Nat.choose_le_middle k n)) ?_
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · -- `n = 2m`: Matoušek–Nešetřil, Proposition 2.6.2
    have hm : 1 ≤ m := by omega
    have h := Nat.centralBinom_lt_four_pow_div_sqrt hm
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    have e1 : ((2 : ℝ) ^ (2 * m)) = 4 ^ m := by rw [pow_mul]; norm_num
    have e2 : (((2 * m : ℕ) : ℝ)) = 2 * (m : ℝ) := by push_cast; ring
    rw [Nat.mul_div_cancel_left m two_pos, e1, e2]
    exact h
  · -- `n = 2m + 1` (the paper's `2m − 1`, with `m` shifted by one):
    -- `C(2m + 1, m) = C(2m + 2, m + 1) / 2 < 2^(2m + 1) / √(2m + 2) < 2^(2m + 1) / √(2m + 1)`
    have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv]
    have hc : 2 * (2 * m + 1).choose m = (2 * (m + 1)).choose (m + 1) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.choose_succ_succ', Nat.choose_symm_half]
      ring
    have h := Nat.centralBinom_lt_four_pow_div_sqrt (m := m + 1) (by omega)
    rw [Nat.centralBinom_eq_two_mul_choose, ← hc] at h
    have hs1 : 0 < Real.sqrt ((2 * m + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hs2 : Real.sqrt ((2 * m + 1 : ℕ) : ℝ) ≤ Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) :=
      Real.sqrt_le_sqrt (by push_cast; linarith)
    calc ((2 * m + 1).choose m : ℝ) = (1 / 2) * ((2 * (2 * m + 1).choose m : ℕ) : ℝ) := by
          push_cast; ring
      _ < (1 / 2) * (4 ^ (m + 1) / Real.sqrt (2 * ((m + 1 : ℕ) : ℝ))) := by gcongr
      _ = 2 ^ (2 * m + 1) / Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) := by
          have e : (2 : ℝ) ^ (2 * m + 1) = 4 ^ (m + 1) / 2 := by
            rw [pow_succ, pow_mul, pow_succ]; norm_num; ring
          rw [e]; ring
      _ ≤ 2 ^ (2 * m + 1) / Real.sqrt ((2 * m + 1 : ℕ) : ℝ) := by gcongr

/-! ### Lemma 3.3 -/

private theorem shrinkAux_integrable_edgeInd {n : ℕ} {p : ℝ} (e : Sym2 (Fin n)) :
    Integrable (edgeInd e) (edgeLaw n p) := by
  refine Integrable.of_mem_Icc 0 1 (measurable_edgeInd e).aemeasurable (ae_of_all _ fun ω => ?_)
  unfold edgeInd
  split_ifs <;> simp

private theorem shrinkAux_edgeInd_eq_zero_or_one {n : ℕ} (e : Sym2 (Fin n)) (ω : EdgeVars n) :
    edgeInd e ω = 0 ∨ edgeInd e ω = 1 := by
  unfold edgeInd
  split_ifs <;> simp

/-- The degree of `v` in `G(n, p)` is at most `(2/3) p (n − 1)` with probability at most
`exp(−(2/9) p² (n − 1))`: `d(v)` is a sum of `n − 1` independent `Bin(1, p)` variables, and
Hoeffding's inequality (Theorem 3.1) applies with `t = (1/3) p (n − 1)` (proof of Lemma 3.3). -/
private theorem shrinkAux_degree_le {n : ℕ} (hn : 1 < n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (v : Fin n) :
    gnpProb n p (fun G => (degree G v : ℝ) ≤ 2 / 3 * p * ((n : ℝ) - 1)) ≤
      Real.exp (-(2 / 9 * p ^ 2 * ((n : ℝ) - 1))) := by
  classical
  have hB := isBernoulliFamily_edgesAt (n := n) hp0.le hp1.le v
  -- `d(v)` is the sum of the `n − 1` edge indicators at `v`
  have hdeg : ∀ ω, (degree (graphOfEdges ω) v : ℝ) =
      ∑ u : {u : Fin n // u ≠ v}, edgeInd s(v, u.1) ω := by
    intro ω
    have h1 : degree (graphOfEdges ω) v = nbrCount (graphOfEdges ω) Set.univ v := by
      unfold degree nbrCount
      congr 1
      ext u
      simp
    rw [h1, nbrCount_graphOfEdges]
    exact Finset.sum_subtype _ (by simp) _
  have hcardR : ((Finset.univ : Finset {u : Fin n // u ≠ v}).card : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.card_univ, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique,
      Nat.cast_sub (by omega)]
    simp
  -- `E d(v) = p (n − 1)`
  have hmean : ∫ ω, ∑ u : {u : Fin n // u ≠ v}, edgeInd s(v, u.1) ω ∂(edgeLaw n p) =
      ((n : ℝ) - 1) * p := by
    rw [integral_finsetSum _ (fun u _ => shrinkAux_integrable_edgeInd _)]
    simp only [fun u => hB.integral_eq u, Finset.sum_const, nsmul_eq_mul, hcardR]
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  -- Hoeffding's inequality, lower tail, with `t = (1/3) p (n − 1)`
  have hH := measureReal_sum_le_sub_le_exp hB.indep hB.measurable Finset.univ (fun _ => 0)
    (fun _ => 1) (fun u _ ω => by rcases hB.zero_or_one u ω with h | h <;> simp [h])
    (t := p * ((n : ℝ) - 1) / 3) (by positivity)
  rw [gnpProb_eq]
  calc (edgeLaw n p).real {ω | (degree (graphOfEdges ω) v : ℝ) ≤ 2 / 3 * p * ((n : ℝ) - 1)}
      = (edgeLaw n p).real {ω | ∑ u : {u : Fin n // u ≠ v}, edgeInd s(v, u.1) ω ≤
          (∫ ω', ∑ u : {u : Fin n // u ≠ v}, edgeInd s(v, u.1) ω' ∂(edgeLaw n p)) -
            p * ((n : ℝ) - 1) / 3} := by
        congr 1
        ext ω
        simp only [Set.mem_ofPred_eq, hdeg, hmean]
        constructor <;> intro h <;> linarith
    _ ≤ _ := hH
    _ = Real.exp (-(2 / 9 * p ^ 2 * ((n : ℝ) - 1))) := by
        congr 1
        simp only [sub_zero, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hcardR]
        field_simp
        ring

/-- **Lemma 3.3** (`D:prop:uni-large-linear-advantage`; Part 4 of Theorem 1.6). For `p ∈ (0, 1)`
and `n > 1`, with probability at least `1 − n exp(−(2/9) p² (n − 1)) = 1 − P₄(n, p)`, every vertex
of `G` has more than `(2/3) p (n − 1)` neighbours, so every Blue set of at most `(1/3) p (n − 1)`
vertices vanishes the next day. -/
theorem lemma3_3 {n : ℕ} (hn : 1 < n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    1 - denseP4 n p ≤ gnpProb n p (fun G => (∀ v, 2 / 3 * p * ((n : ℝ) - 1) < degree G v) ∧
      ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3 → majorityStep G B = ∅) := by
  apply le_gnpProb_of_not_le
  calc gnpProb n p (fun G => ¬ ((∀ v, 2 / 3 * p * ((n : ℝ) - 1) < degree G v) ∧
        ∀ B : Set (Fin n), (B.ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3 → majorityStep G B = ∅))
      ≤ gnpProb n p (fun G => ∃ v ∈ Finset.univ,
          (degree G v : ℝ) ≤ 2 / 3 * p * ((n : ℝ) - 1)) := by
        apply gnpProb_mono
        intro G hG
        by_contra hcon
        push Not at hcon
        apply hG
        -- all degrees exceed `(2/3) p (n − 1)`, so a Blue camp of at most `(1/3) p (n − 1)`
        -- vertices cannot form a majority in any neighbourhood, and vanishes the next day
        have hdeg : ∀ v, 2 * (p * ((n : ℝ) - 1) / 3) < degree G v := fun v => by
          have := hcon v (Finset.mem_univ v)
          linarith
        exact ⟨fun v => hcon v (Finset.mem_univ v),
          fun B hB => majorityStep_eq_empty_of_lt_degree G hdeg hB⟩
    -- the union bound over the `n` vertices
    _ ≤ ∑ v, gnpProb n p (fun G => (degree G v : ℝ) ≤ 2 / 3 * p * ((n : ℝ) - 1)) :=
        gnpProb_exists_le _ _
    _ ≤ ∑ _v : Fin n, Real.exp (-(2 / 9 * p ^ 2 * ((n : ℝ) - 1))) :=
        Finset.sum_le_sum fun v _ => shrinkAux_degree_le hn hp0 hp1 v
    _ = denseP4 n p := by simp [denseP4]

/-! ### Lemma 3.4 -/

/-- The unordered pairs of distinct vertices, which index the edge variables `W_{uv}`. -/
private abbrev shrinkAux_pairs (n : ℕ) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag)

/-- A sum over the ordered pairs `(v, u)` of distinct vertices, as a sum over the unordered
pairs `{u, v}`. -/
private theorem shrinkAux_sum_erase_eq_sum_pairs {n : ℕ} (F : Fin n → Fin n → ℝ) :
    ∑ v, ∑ u ∈ Finset.univ.erase v, F v u =
      ∑ e ∈ shrinkAux_pairs n,
        Sym2.lift ⟨fun a b => F a b + F b a, fun _ _ => add_comm _ _⟩ e := by
  classical
  set T : Finset (Fin n × Fin n) := (Finset.univ ×ˢ Finset.univ).filter (fun x => x.1 ≠ x.2)
    with hT
  have h1 : ∑ v, ∑ u ∈ Finset.univ.erase v, F v u = ∑ x ∈ T, F x.1 x.2 := by
    rw [hT, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_filter, Finset.filter_ne]
  rw [h1, ← Finset.sum_fiberwise_of_maps_to (g := fun x : Fin n × Fin n => s(x.1, x.2))
    (t := shrinkAux_pairs n)]
  · refine Finset.sum_congr rfl fun e he => ?_
    induction e using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := by simpa [Sym2.mk_isDiag_iff] using he
      have hfib : T.filter (fun x => s(x.1, x.2) = s(a, b)) = {(a, b), (b, a)} := by
        ext x
        simp only [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hx, hxe⟩
          obtain ⟨x1, x2⟩ := x
          rcases Sym2.eq_iff.mp hxe with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · left; exact Prod.ext h1 h2
          · right; exact Prod.ext h1 h2
        · rintro (rfl | rfl)
          · exact ⟨hab, rfl⟩
          · exact ⟨hab.symm, Sym2.eq_swap⟩
      rw [hfib, Finset.sum_pair (by simp [hab]), Sym2.lift_mk]
  · intro x hx
    simp only [hT, Finset.mem_filter] at hx
    simpa [Sym2.mk_isDiag_iff] using hx.2

/-- `∑_v ∑_{u ≠ v} f(v) g(u) = (∑ f)(∑ g) − ∑ f g`. -/
private theorem shrinkAux_sum_erase_mul {n : ℕ} (f g : Fin n → ℝ) :
    ∑ v, ∑ u ∈ Finset.univ.erase v, f v * g u = (∑ v, f v) * (∑ u, g u) - ∑ v, f v * g v := by
  simp_rw [← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ _), mul_sub,
    Finset.sum_sub_distrib, Finset.sum_mul]

/-- The indicator `1_S` of a set of vertices. -/
private def shrinkAux_ind {n : ℕ} (S : Finset (Fin n)) (v : Fin n) : ℝ := if v ∈ S then 1 else 0

/-- The colour sign `J(u)`: `1` if `u` is Red, `−1` if `u` is Blue (`u ∈ B`). -/
private def shrinkAux_J {n : ℕ} (B : Finset (Fin n)) (u : Fin n) : ℝ := 1 - 2 * shrinkAux_ind B u

private theorem shrinkAux_sum_ind {n : ℕ} (S : Finset (Fin n)) :
    ∑ v, shrinkAux_ind S v = S.card := by
  simp [shrinkAux_ind]

private theorem shrinkAux_ind_mul_ind {n : ℕ} (S B : Finset (Fin n)) (v : Fin n) :
    shrinkAux_ind S v * shrinkAux_ind B v = shrinkAux_ind (S ∩ B) v := by
  unfold shrinkAux_ind
  by_cases hS : v ∈ S <;> by_cases hB : v ∈ B <;> simp [hS, hB]

private theorem shrinkAux_ind_sq {n : ℕ} (S : Finset (Fin n)) (v : Fin n) :
    shrinkAux_ind S v ^ 2 = shrinkAux_ind S v := by
  unfold shrinkAux_ind
  split_ifs <;> norm_num

private theorem shrinkAux_J_sq {n : ℕ} (B : Finset (Fin n)) (u : Fin n) :
    shrinkAux_J B u ^ 2 = 1 := by
  unfold shrinkAux_J shrinkAux_ind
  split_ifs <;> norm_num

/-- `∑_u J(u) = |R| − |B| = n − 2|B|`. -/
private theorem shrinkAux_sum_J {n : ℕ} (B : Finset (Fin n)) :
    ∑ u, shrinkAux_J B u = (n : ℝ) - 2 * B.card := by
  simp only [shrinkAux_J, Finset.sum_sub_distrib, ← Finset.mul_sum, shrinkAux_sum_ind]
  simp

/-- `∑_{v ∈ S} J(v) = m_R − m_B = |S| − 2|S ∩ B|`. -/
private theorem shrinkAux_sum_ind_mul_J {n : ℕ} (B S : Finset (Fin n)) :
    ∑ v, shrinkAux_ind S v * shrinkAux_J B v = (S.card : ℝ) - 2 * (S ∩ B).card := by
  simp only [shrinkAux_J, mul_sub, mul_one, Finset.sum_sub_distrib, shrinkAux_sum_ind]
  simp only [mul_left_comm _ (2 : ℝ), ← Finset.mul_sum, shrinkAux_ind_mul_ind, shrinkAux_sum_ind]

/-- The coefficient `X_{uv} = J(u) 1_S(v) + J(v) 1_S(u)` of the edge variable `W_{uv}` in
`δ(S)` (the paper's equation (3.1)). -/
private def shrinkAux_X {n : ℕ} (B S : Finset (Fin n)) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun u v => shrinkAux_J B u * shrinkAux_ind S v + shrinkAux_J B v * shrinkAux_ind S u,
    fun _ _ => add_comm _ _⟩

/-- `δ(S) = ∑_{v ∈ S} δ(v)`, where `δ(v) = |N(v) ∩ R| − |N(v) ∩ B|`. -/
private def shrinkAux_delta {n : ℕ} (G : SimpleGraph (Fin n)) (B S : Finset (Fin n)) : ℝ :=
  ∑ v ∈ S, ((nbrCount G (↑B)ᶜ v : ℝ) - nbrCount G ↑B v)

/-- If `S` turns entirely Blue, then `δ(S) ≤ 0`: every `v ∈ S` has at least as many Blue as Red
neighbours. -/
private theorem shrinkAux_delta_nonpos {n : ℕ} {G : SimpleGraph (Fin n)} {B S : Finset (Fin n)}
    (h : (↑S : Set (Fin n)) ⊆ majorityStep G ↑B) : shrinkAux_delta G B S ≤ 0 := by
  unfold shrinkAux_delta
  refine Finset.sum_nonpos fun v hv => ?_
  have hv' := h (Finset.mem_coe.mpr hv)
  simp only [majorityStep, Set.mem_ofPred_eq] at hv'
  rcases hv' with h1 | ⟨h1, _⟩
  · have : (nbrCount G (↑B)ᶜ v : ℝ) < nbrCount G ↑B v := by exact_mod_cast h1
    linarith
  · rw [h1]
    simp

/-- The paper's equation (3.1): `δ(S) = ∑_{u ≠ v} [J(u) 1_S(v) + J(v) 1_S(u)] W_{uv}`, a sum
over the unordered pairs `{u, v}`. -/
private theorem shrinkAux_delta_eq {n : ℕ} (ω : EdgeVars n) (B S : Finset (Fin n)) :
    shrinkAux_delta (graphOfEdges ω) B S =
      ∑ e ∈ shrinkAux_pairs n, shrinkAux_X B S e * edgeInd e ω := by
  classical
  -- `δ(v) = ∑_{u ≠ v} J(u) W_{uv}`
  have hv : ∀ v, ((nbrCount (graphOfEdges ω) (↑B)ᶜ v : ℝ) - nbrCount (graphOfEdges ω) ↑B v) =
      ∑ u ∈ Finset.univ.erase v, shrinkAux_J B u * edgeInd s(v, u) ω := by
    intro v
    rw [nbrCount_graphOfEdges, nbrCount_graphOfEdges, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_sub_distrib, ← Finset.filter_ne', Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases huv : u = v <;> by_cases huB : u ∈ B <;>
      norm_num [huv, huB, shrinkAux_J, shrinkAux_ind]
  -- `δ(S) = ∑_v 1_S(v) ∑_{u ≠ v} J(u) W_{uv}`, then group the two orientations of each pair
  unfold shrinkAux_delta
  rw [Finset.sum_congr rfl fun v _ => hv v]
  have hS : ∑ v ∈ S, ∑ u ∈ Finset.univ.erase v, shrinkAux_J B u * edgeInd s(v, u) ω =
      ∑ v, ∑ u ∈ Finset.univ.erase v,
        shrinkAux_ind S v * shrinkAux_J B u * edgeInd s(v, u) ω := by
    simp_rw [mul_assoc, ← Finset.mul_sum, shrinkAux_ind, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hS, shrinkAux_sum_erase_eq_sum_pairs]
  refine Finset.sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Sym2.lift_mk, shrinkAux_X]
    rw [Sym2.eq_swap (a := b) (b := a)]
    ring

/-- The sum of the coefficients, `∑_{u ≠ v} X_{uv} = m(n − 2n₀) − m + 2m_B` with `m = |S|`,
`n₀ = |B|` and `m_B = |S ∩ B|`; so `E δ(S) = p [m(n − 2n₀) − m + 2m_B]` (proof of Lemma 3.4). -/
private theorem shrinkAux_sum_X {n : ℕ} (B S : Finset (Fin n)) :
    ∑ e ∈ shrinkAux_pairs n, shrinkAux_X B S e =
      (S.card : ℝ) * (n - 2 * B.card) - S.card + 2 * (S ∩ B).card := by
  have h := shrinkAux_sum_erase_eq_sum_pairs (n := n)
    (fun v u => shrinkAux_ind S v * shrinkAux_J B u)
  rw [shrinkAux_sum_erase_mul, shrinkAux_sum_ind, shrinkAux_sum_J, shrinkAux_sum_ind_mul_J] at h
  rw [← Finset.sum_congr rfl fun e _ => ?_, ← h]
  · ring
  · induction e using Sym2.ind with
    | _ a b => simp only [Sym2.lift_mk, shrinkAux_X]; ring

/-- The sum of the squared coefficients,
`∑_{u ≠ v} X_{uv}² = 2m_R² + 2m_B² − 2m_R − 2m_B + m(n − m_R − m_B)` with `m_R = |S ∖ B|` and
`m_B = |S ∩ B|` (proof of Lemma 3.4). -/
private theorem shrinkAux_sum_X_sq {n : ℕ} (B S : Finset (Fin n)) :
    ∑ e ∈ shrinkAux_pairs n, shrinkAux_X B S e ^ 2 =
      2 * ((S \ B).card : ℝ) ^ 2 + 2 * ((S ∩ B).card : ℝ) ^ 2 - 2 * (S \ B).card -
        2 * (S ∩ B).card + S.card * (n - (S \ B).card - (S ∩ B).card) := by
  have h := shrinkAux_sum_erase_eq_sum_pairs (n := n)
    (fun v u => shrinkAux_ind S v * shrinkAux_J B u * shrinkAux_X B S s(v, u))
  have h2 : ∑ e ∈ shrinkAux_pairs n, shrinkAux_X B S e ^ 2 =
      ∑ v, ∑ u ∈ Finset.univ.erase v,
        shrinkAux_ind S v * shrinkAux_J B u * shrinkAux_X B S s(v, u) := by
    rw [h]
    refine Finset.sum_congr rfl fun e _ => ?_
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Sym2.lift_mk]
      rw [Sym2.eq_swap (a := b) (b := a)]
      simp only [shrinkAux_X, Sym2.lift_mk]
      ring
  have hterm : ∀ v u, shrinkAux_ind S v * shrinkAux_J B u * shrinkAux_X B S s(v, u) =
      (shrinkAux_ind S v * shrinkAux_J B v) * (shrinkAux_ind S u * shrinkAux_J B u) +
        shrinkAux_ind S v * 1 := by
    intro v u
    simp only [shrinkAux_X, Sym2.lift_mk]
    linear_combination (shrinkAux_ind S v) ^ 2 * shrinkAux_J_sq B u + shrinkAux_ind_sq S v
  have hsq : ∑ v, (shrinkAux_ind S v * shrinkAux_J B v) * (shrinkAux_ind S v * shrinkAux_J B v) =
      S.card := by
    rw [← shrinkAux_sum_ind S]
    refine Finset.sum_congr rfl fun v _ => ?_
    linear_combination (shrinkAux_ind S v) ^ 2 * shrinkAux_J_sq B v + shrinkAux_ind_sq S v
  rw [h2]
  simp only [hterm, Finset.sum_add_distrib]
  rw [shrinkAux_sum_erase_mul, shrinkAux_sum_erase_mul, hsq, shrinkAux_sum_ind_mul_J]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    shrinkAux_sum_ind]
  have hcard : (S.card : ℝ) = (S \ B).card + (S ∩ B).card := by
    rw [← Nat.cast_add, Finset.card_sdiff_add_card_inter]
  rw [hcard]
  ring

/-- Real arithmetic for the exponent: if `0 ≤ t₀ ≤ t`, `0 ≤ D ≤ D₀`, and `t = 0` when `D = 0`,
then `−2t²/D ≤ −2t₀²/D₀`. -/
private theorem shrinkAux_neg_div_le {t t₀ D D₀ : ℝ} (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t) (hD : 0 ≤ D)
    (hDD : D ≤ D₀) (hD0 : D = 0 → t = 0) : -2 * t ^ 2 / D ≤ -2 * t₀ ^ 2 / D₀ := by
  rcases hD.eq_or_lt with h | h
  · have ht0 : t = 0 := hD0 h.symm
    have : t₀ = 0 := le_antisymm (ht0 ▸ ht) ht₀
    simp [ht0, this]
  · have hD₀ : 0 < D₀ := h.trans_le hDD
    rw [div_le_div_iff₀ h hD₀]
    have h1 : t₀ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ ht₀ ht 2
    nlinarith [mul_le_mul h1 hDD h.le (sq_nonneg t)]

/-- The core of the proof of Lemma 3.4: for a Blue set `B` of `n₀` vertices and a set `S` of
`m ≥ 1` vertices, `P(S ⊆ B₁) ≤ P(δ(S) ≤ 0) ≤ exp(−2p²(n − 2n₀ − 1)² m / (n + m − 2))`, by
Hoeffding's inequality applied to the decomposition (3.1) of `δ(S)` into independent summands
`X_{uv} W_{uv}`, each with range `|X_{uv}|`. -/
private theorem shrinkAux_prob_subset_le {n n₀ m : ℕ} (hn₀ : (n₀ : ℝ) < n / 2) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) {B S : Finset (Fin n)} (hB : B.card = n₀) (hS : S.card = m)
    (hm : 0 < m) :
    gnpProb n p (fun G => (↑S : Set (Fin n)) ⊆ majorityStep G ↑B) ≤
      Real.exp (-(2 * p ^ 2 * ((n : ℝ) - 2 * n₀ - 1) ^ 2 * m / (n + m - 2))) := by
  classical
  set X := shrinkAux_X B S with hX
  set Y : Sym2 (Fin n) → EdgeVars n → ℝ := fun e ω => X e * edgeInd e ω with hY
  -- the summands `X_{uv} W_{uv}` are independent, with values in `{0, X_{uv}}`
  have hindep : iIndepFun Y (edgeLaw n p) :=
    (iIndepFun_edgeInd n p).comp (fun e x => X e * x) (fun e => measurable_const.mul measurable_id)
  have hmeas : ∀ e, Measurable (Y e) := fun e => (measurable_edgeInd e).const_mul (X e)
  have hbound : ∀ e ∈ shrinkAux_pairs n, ∀ ω, Y e ω ∈ Set.Icc (min 0 (X e)) (max 0 (X e)) := by
    intro e _ ω
    rcases shrinkAux_edgeInd_eq_zero_or_one e ω with h | h <;> simp [hY, h]
  -- `E δ(S) = p ∑ X_{uv} = p [m(n − 2n₀) − m + 2m_B]`
  have hmean : ∫ ω, ∑ e ∈ shrinkAux_pairs n, Y e ω ∂(edgeLaw n p) =
      p * ∑ e ∈ shrinkAux_pairs n, X e := by
    rw [integral_finsetSum _ fun e _ => (shrinkAux_integrable_edgeInd e).const_mul (X e),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have he' : ¬ e.IsDiag := (Finset.mem_filter.mp he).2
    have hint : ∫ ω, edgeInd e ω ∂(edgeLaw n p) = p :=
      (isBernoulliFamily_edgeInd hp0.le hp1.le).integral_eq ⟨e, he'⟩
    rw [integral_const_mul, hint]
    ring
  set t := ∫ ω, ∑ e ∈ shrinkAux_pairs n, Y e ω ∂(edgeLaw n p) with ht
  have hsumX := shrinkAux_sum_X B S
  have hsumX2 := shrinkAux_sum_X_sq B S
  rw [hB, hS] at hsumX
  rw [hS] at hsumX2
  have hcard : (m : ℝ) = (S \ B).card + (S ∩ B).card := by
    rw [← hS, ← Nat.cast_add, Finset.card_sdiff_add_card_inter]
  have hn₀' : (2 * n₀ + 1 : ℝ) ≤ n := by
    have h2 : 2 * n₀ < n := by
      have : (2 * n₀ : ℝ) < n := by linarith
      exact_mod_cast this
    exact_mod_cast h2
  -- `E δ(S) ≥ pm(n − 2n₀ − 1) ≥ 0`
  have ht₀ : 0 ≤ p * m * ((n : ℝ) - 2 * n₀ - 1) := by
    have : (0 : ℝ) ≤ (n : ℝ) - 2 * n₀ - 1 := by linarith
    positivity
  have htt : p * m * ((n : ℝ) - 2 * n₀ - 1) ≤ t := by
    rw [hmean, hsumX]
    have : (0 : ℝ) ≤ (S ∩ B).card := Nat.cast_nonneg _
    nlinarith
  -- `∑ X_{uv}² = 2(m_R + m_B)² − 4m_R m_B − 2m + m(n − m) ≤ m(n + m − 2)`
  have hD : 0 ≤ ∑ e ∈ shrinkAux_pairs n, X e ^ 2 := Finset.sum_nonneg fun e _ => sq_nonneg _
  have hDD : ∑ e ∈ shrinkAux_pairs n, X e ^ 2 ≤ m * ((n : ℝ) + m - 2) := by
    rw [hsumX2, hcard]
    have h1 : (0 : ℝ) ≤ (S \ B).card := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (S ∩ B).card := Nat.cast_nonneg _
    nlinarith [mul_nonneg h1 h2]
  have hD0 : ∑ e ∈ shrinkAux_pairs n, X e ^ 2 = 0 → t = 0 := by
    intro h0
    rw [Finset.sum_sq_eq_zero_iff] at h0
    rw [hmean, Finset.sum_eq_zero h0, mul_zero]
  -- Hoeffding's inequality (Theorem 3.1), lower tail, with `t = E δ(S)`
  have hH := measureReal_sum_le_sub_le_exp hindep hmeas (shrinkAux_pairs n) (fun e => min 0 (X e))
    (fun e => max 0 (X e)) hbound (t := t) (ht₀.trans htt)
  have hwidth : ∀ e, (max 0 (X e) - min 0 (X e)) ^ 2 = X e ^ 2 := by
    intro e
    rcases le_total 0 (X e) with h | h <;> simp [h]
  simp only [hwidth] at hH
  rw [← ht, sub_self] at hH
  calc gnpProb n p (fun G => (↑S : Set (Fin n)) ⊆ majorityStep G ↑B)
      ≤ gnpProb n p (fun G => shrinkAux_delta G B S ≤ 0) :=
        gnpProb_mono fun G h => shrinkAux_delta_nonpos h
    _ = (edgeLaw n p).real {ω | ∑ e ∈ shrinkAux_pairs n, Y e ω ≤ 0} := by
        rw [gnpProb_eq]
        simp only [shrinkAux_delta_eq]
        rfl
    _ ≤ Real.exp (-2 * t ^ 2 / ∑ e ∈ shrinkAux_pairs n, X e ^ 2) := hH
    _ ≤ Real.exp (-2 * (p * m * ((n : ℝ) - 2 * n₀ - 1)) ^ 2 / (m * ((n : ℝ) + m - 2))) :=
        Real.exp_le_exp.mpr (shrinkAux_neg_div_le ht₀ htt hD hDD hD0)
    _ = Real.exp (-(2 * p ^ 2 * ((n : ℝ) - 2 * n₀ - 1) ^ 2 * m / (n + m - 2))) := by
        congr 1
        have hm' : (m : ℝ) ≠ 0 := by positivity
        rw [show -2 * (p * m * ((n : ℝ) - 2 * n₀ - 1)) ^ 2 =
          m * (-(2 * p ^ 2 * ((n : ℝ) - 2 * n₀ - 1) ^ 2 * m)) by ring,
          mul_div_mul_left _ _ hm', neg_div]

/-- **Lemma 3.4** (`D:lem:uni-bad-set-bound`). Let `p ∈ (0, 1)` and `n, n₀ ∈ ℕ` with `n₀ < n/2`.
For every `m ≤ n`, with probability at least
`1 − (4ⁿ / n) exp(−2p² (n − 2n₀ − 1)² m / (n + m − 2))`, every Blue set of at most `n₀` vertices
has fewer than `m` Blue vertices the next day.

Departure from the paper (a gap filled): the paper's double union bound runs over the Blue sets
of exactly `n₀` vertices; a Blue set of fewer vertices lies in one of exactly `n₀` vertices, and
a larger Blue set gives a larger Blue set the next day (`majorityStep_mono`). -/
theorem lemma3_4 {n n₀ : ℕ} (hn₀ : (n₀ : ℝ) < n / 2) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {m : ℕ}
    (hm : m ≤ n) :
    1 - 4 ^ n / n * Real.exp (-(2 * p ^ 2 * ((n : ℝ) - 2 * n₀ - 1) ^ 2 * m / (n + m - 2))) ≤
      gnpProb n p (fun G => ∀ B : Set (Fin n), B.ncard ≤ n₀ → (majorityStep G B).ncard < m) := by
  classical
  have hn₀n : n₀ ≤ n := by
    have : (n₀ : ℝ) ≤ n := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact_mod_cast this
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp at hn₀
      linarith [(Nat.cast_nonneg n₀ : (0 : ℝ) ≤ n₀)]
    · exact h
  have h4n : 1 ≤ (4 : ℝ) ^ n / n := by
    rw [le_div_iff₀ (by exact_mod_cast hn), one_mul]
    exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 4)).le
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · -- `m = 0`: the bound is `1 − 4ⁿ/n ≤ 0`
    refine le_trans ?_ (gnpProb_nonneg _)
    simp only [Nat.cast_zero, mul_zero, zero_div, neg_zero, Real.exp_zero, mul_one]
    linarith
  apply le_gnpProb_of_not_le
  set E := Real.exp (-(2 * p ^ 2 * ((n : ℝ) - 2 * n₀ - 1) ^ 2 * m / (n + m - 2))) with hE
  calc gnpProb n p (fun G => ¬ ∀ B : Set (Fin n), B.ncard ≤ n₀ → (majorityStep G B).ncard < m)
      ≤ gnpProb n p (fun G => ∃ BS ∈ Finset.powersetCard n₀ (Finset.univ : Finset (Fin n)) ×ˢ
          Finset.powersetCard m (Finset.univ : Finset (Fin n)),
            (↑BS.2 : Set (Fin n)) ⊆ majorityStep G ↑BS.1) := by
        apply gnpProb_mono
        intro G hG
        push Not at hG
        obtain ⟨B, hB, hBm⟩ := hG
        -- a Blue set of at most `n₀` vertices lies in one of exactly `n₀` vertices
        obtain ⟨B', hBB', -, hB'⟩ := Set.exists_subsuperset_card_eq (Set.subset_univ B) hB
          (by simp [Set.ncard_univ, hn₀n])
        have hmB' : m ≤ (majorityStep G B').ncard :=
          hBm.trans (Set.ncard_le_ncard (majorityStep_mono G hBB'))
        -- `m` of the vertices that are Blue the next day
        obtain ⟨S, hS, hSm⟩ := Set.exists_subset_card_eq hmB'
        refine ⟨(B'.toFinset, S.toFinset), ?_, ?_⟩
        · rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
          refine ⟨⟨Finset.subset_univ _, ?_⟩, ⟨Finset.subset_univ _, ?_⟩⟩
          · rw [← Set.ncard_eq_toFinset_card', hB']
          · rw [← Set.ncard_eq_toFinset_card', hSm]
        · simpa using hS
    -- the double union bound over the choices of `B` and `S`
    _ ≤ ∑ BS ∈ Finset.powersetCard n₀ (Finset.univ : Finset (Fin n)) ×ˢ
          Finset.powersetCard m (Finset.univ : Finset (Fin n)),
            gnpProb n p (fun G => (↑BS.2 : Set (Fin n)) ⊆ majorityStep G ↑BS.1) :=
        gnpProb_exists_le _ _
    _ ≤ ∑ BS ∈ Finset.powersetCard n₀ (Finset.univ : Finset (Fin n)) ×ˢ
          Finset.powersetCard m (Finset.univ : Finset (Fin n)), E := by
        refine Finset.sum_le_sum fun BS hBS => ?_
        simp only [Finset.mem_product, Finset.mem_powersetCard] at hBS
        exact shrinkAux_prob_subset_le hn₀ hp0 hp1 hBS.1.2 hBS.2.2 hm0
    _ = (n.choose n₀ : ℝ) * n.choose m * E := by
        simp [Finset.card_product, Finset.card_powersetCard]
    _ ≤ 4 ^ n / n * E := by
        gcongr
        -- by Lemma 3.2, `C(n, n₀) C(n, m) < (2ⁿ/√n)² = 4ⁿ/n`
        have h1 := lemma3_2 hn hn₀n
        have h2 := lemma3_2 hn hm
        calc (n.choose n₀ : ℝ) * n.choose m ≤ (2 ^ n / Real.sqrt n) * (2 ^ n / Real.sqrt n) :=
              mul_le_mul h1.le h2.le (Nat.cast_nonneg _) (by positivity)
          _ = 4 ^ n / n := by
              rw [div_mul_div_comm, Real.mul_self_sqrt (Nat.cast_nonneg _), ← mul_pow]
              norm_num

/-! ### Lemmas 3.5 and 3.6 -/

/-- `(4ⁿ / n) e^{−E} = n⁻¹ e^{−(E − 2n log 2)}` (proofs of Lemmas 3.5 and 3.6). -/
private theorem shrinkAux_four_pow_div_mul_exp (n : ℕ) (E : ℝ) :
    4 ^ n / n * Real.exp (-E) = (n : ℝ)⁻¹ * Real.exp (-(E - 2 * n * Real.log 2)) := by
  have h4 : (4 : ℝ) ^ n = Real.exp (2 * n * Real.log 2) := by
    rw [show (2 : ℝ) * n * Real.log 2 = n * Real.log 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [h4, div_eq_inv_mul, mul_assoc, ← Real.exp_add]
  ring_nf

/-- **Lemma 3.5** (`D:prop:uni-sqrt-advantage-ex`; Part 2 of Theorem 1.6). With probability at
least `1 − P₂(n)`, every Blue set of at most `n/2 − (0.8/p) √n` vertices has at most `0.4 n` Blue
vertices the next day.

Reading: the lemma prints the bound as `1 − n⁻¹ exp(−0.025 n) = 1 − P₂(n)`, and Theorem 1.6 prints
`P₂(n) = n⁻¹ exp(−(0.076 n − 1.38 √n))`; the proof computes `0.076 n − 1.83 √n`, which is
`denseP2`. The printed `0.025 n` bound follows for `n ≥ 1288` (`lemma3_5_printed`).

In the proof, the paper's display bounding the exponent drops the square on `(1.6 √n / p − 1)`
(a typo; the next line expands the square).

Departure from the paper (a case the paper leaves implicit): when `n/2 − (0.8/p) √n < 0`, no Blue
set qualifies and the event is sure. -/
theorem lemma3_5 {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    1 - denseP2 n ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
      (B.ncard : ℝ) ≤ n / 2 - 0.8 / p * Real.sqrt n → ((majorityStep G B).ncard : ℝ) ≤ 0.4 * n) := by
  have hP2 : 0 ≤ denseP2 n := by unfold denseP2; positivity
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by positivity)
  have hss : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  rcases lt_or_ge (n / 2 - 0.8 / p * Real.sqrt n : ℝ) 0 with hneg | hpos
  · -- no Blue set has at most `n/2 − (0.8/p)√n < 0` vertices: the event is sure
    have h1 : gnpProb n p (fun _ => True) ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
        (B.ncard : ℝ) ≤ n / 2 - 0.8 / p * Real.sqrt n →
          ((majorityStep G B).ncard : ℝ) ≤ 0.4 * n) := by
      refine gnpProb_mono fun G _ B hB => ?_
      have : (0 : ℝ) ≤ B.ncard := Nat.cast_nonneg _
      linarith
    rw [gnpProb_true] at h1
    linarith
  -- `n₂ = ⌊n/2 − (0.8/p)√n⌋` and `m = ⌈0.4 n⌉`
  set n₂ := ⌊(n / 2 - 0.8 / p * Real.sqrt n : ℝ)⌋₊ with hn₂
  set m := ⌈(0.4 * n : ℝ)⌉₊ with hm
  have hn₂x : (n₂ : ℝ) ≤ n / 2 - 0.8 / p * Real.sqrt n := Nat.floor_le hpos
  have hn₂n : (n₂ : ℝ) < n / 2 := by
    have : 0 < 0.8 / p * Real.sqrt n := by positivity
    linarith
  have hmn : m ≤ n := Nat.ceil_le.mpr (by linarith)
  have hm4 : (0.4 * n : ℝ) ≤ m := Nat.le_ceil _
  -- Lemma 3.4: every Blue set of at most `n₂` vertices shrinks to at most `m − 1` vertices
  have h34 := lemma3_4 hn₂n hp0 hp1 hmn
  -- this event implies ours: an integer `< ⌈0.4 n⌉` is `≤ 0.4 n`
  have hev : gnpProb n p (fun G => ∀ B : Set (Fin n), B.ncard ≤ n₂ →
      (majorityStep G B).ncard < m) ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
        (B.ncard : ℝ) ≤ n / 2 - 0.8 / p * Real.sqrt n →
          ((majorityStep G B).ncard : ℝ) ≤ 0.4 * n) :=
    gnpProb_mono fun G hG B hB => (Nat.lt_ceil.mp (hG B (Nat.le_floor hB))).le
  -- the bound: `(4ⁿ/n) e^{−E} = n⁻¹ e^{−(E − 2n log 2)}` with `E − 2n log 2 ≥ 0.076 n − 1.83 √n`
  have hbound : 4 ^ n / n * Real.exp (-(2 * p ^ 2 * ((n : ℝ) - 2 * n₂ - 1) ^ 2 * m /
      (n + m - 2))) ≤ denseP2 n := by
    rw [shrinkAux_four_pow_div_mul_exp, denseP2]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    -- `√n > 1.6`, so `n > 2.56` and `n + m − 2 > 0`
    have hp08 : 0.8 * Real.sqrt n < 0.8 / p * Real.sqrt n := by
      gcongr
      rw [lt_div_iff₀ hp0]
      linarith
    have hs16 : 1.6 < Real.sqrt n := by nlinarith
    have hn3 : (2.56 : ℝ) < n := by nlinarith
    have hnm : (0 : ℝ) < n + m - 2 := by linarith
    -- `m / (n + m − 2) ≥ m / (n + m) ≥ 2/7`
    have hfrac : 2 / 7 ≤ (m : ℝ) / (n + m - 2) := by
      calc (2 / 7 : ℝ) ≤ m / (n + m) := by
            rw [le_div_iff₀ (by positivity)]
            linarith
        _ ≤ m / (n + m - 2) := by
            gcongr
            linarith
    -- `n − 2n₂ − 1 ≥ 1.6 √n / p − 1 ≥ 0`
    have hgap : 1.6 * Real.sqrt n / p - 1 ≤ (n : ℝ) - 2 * n₂ - 1 := by
      have : 1.6 * Real.sqrt n / p = 2 * (0.8 / p * Real.sqrt n) := by ring
      linarith
    have hgap0 : 0 ≤ 1.6 * Real.sqrt n / p - 1 := by
      rw [sub_nonneg, le_div_iff₀ hp0]
      nlinarith
    have hsq : (1.6 * Real.sqrt n / p - 1) ^ 2 ≤ ((n : ℝ) - 2 * n₂ - 1) ^ 2 :=
      pow_le_pow_left₀ hgap0 hgap 2
    -- `2p²(n − 2n₂ − 1)² m / (n + m − 2) ≥ (4/7) p² (1.6√n/p − 1)² = (4/7)(1.6√n − p)²`
    have hE : 4 / 7 * (1.6 * Real.sqrt n - p) ^ 2 ≤
        2 * p ^ 2 * ((n : ℝ) - 2 * n₂ - 1) ^ 2 * m / (n + m - 2) := by
      have e1 : 4 / 7 * (1.6 * Real.sqrt n - p) ^ 2 =
          2 * p ^ 2 * (1.6 * Real.sqrt n / p - 1) ^ 2 * (2 / 7) := by
        field_simp
        ring
      have e2 : 2 * p ^ 2 * ((n : ℝ) - 2 * n₂ - 1) ^ 2 * m / (n + m - 2) =
          2 * p ^ 2 * ((n : ℝ) - 2 * n₂ - 1) ^ 2 * (m / (n + m - 2)) := by ring
      rw [e1, e2]
      gcongr
    -- `(4/7)(1.6√n − p)² − 2n log 2 = (10.24/7 − 2 log 2) n − (12.8/7) p √n + (4/7) p²
    --   ≥ 0.076 n − 1.83 √n`
    have hexp : 4 / 7 * (1.6 * Real.sqrt n - p) ^ 2 - 2 * n * Real.log 2 =
        (10.24 / 7 - 2 * Real.log 2) * n - 12.8 / 7 * p * Real.sqrt n + 4 / 7 * p ^ 2 := by
      linear_combination (4 / 7 * 2.56 : ℝ) * hss
    have h1 : 0.076 * (n : ℝ) ≤ (10.24 / 7 - 2 * Real.log 2) * n := by
      have := Real.log_two_lt_d9
      gcongr
      linarith
    have h2 : 12.8 / 7 * p * Real.sqrt n ≤ 1.83 * Real.sqrt n := by
      gcongr
      linarith
    have h3 : 0 ≤ 4 / 7 * p ^ 2 := by positivity
    linarith
  linarith

/-- The bound of Lemma 3.5 as printed in the lemma, `1 − n⁻¹ exp(−0.025 n)`, for `n ≥ 1288`, where
`0.025 n ≤ 0.076 n − 1.83 √n`. -/
theorem lemma3_5_printed {n : ℕ} (hn : 1288 ≤ n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    1 - (n : ℝ)⁻¹ * Real.exp (-(0.025 * n)) ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
      (B.ncard : ℝ) ≤ n / 2 - 0.8 / p * Real.sqrt n → ((majorityStep G B).ncard : ℝ) ≤ 0.4 * n) := by
  refine le_trans ?_ (lemma3_5 (by omega) hp0 hp1)
  -- `0.025 n ≤ 0.076 n − 1.83 √n` for `n ≥ 1288`, since `√n ≥ 35.8824 ≥ 1.83 / 0.051`
  have hnR : (1288 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (35.8824 : ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by linarith)
  have hss : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hkey : 0.025 * (n : ℝ) ≤ 0.076 * n - 1.83 * Real.sqrt n := by nlinarith
  rw [denseP2]
  gcongr

/-- `P₃(n, p) ≥ 1` for `n ≤ 4`, so that Lemma 3.6 is trivial there. -/
private theorem shrinkAux_one_le_denseP3 {n : ℕ} (hn : 1 ≤ n) (hn4 : n ≤ 4) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) : 1 ≤ denseP3 n p := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn4R : (n : ℝ) ≤ 4 := by exact_mod_cast hn4
  have hp3 : p ^ 3 ≤ 1 := pow_le_one₀ hp0.le hp1.le
  rw [denseP3, ← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
  have h := Real.add_one_le_exp (-(0.02 * n * (p ^ 3 * n - 80)))
  have hn2 : (n : ℝ) ^ 2 ≤ 16 := by nlinarith
  have hpn : p ^ 3 * (n : ℝ) ^ 2 ≤ 16 := by
    nlinarith [mul_le_mul hp3 hn2 (by positivity) (by norm_num)]
  have : (n : ℝ) ≤ -(0.02 * n * (p ^ 3 * n - 80)) + 1 := by nlinarith
  linarith

/-- **Lemma 3.6** (`D:prop:uni-linear-advantage`; Part 3 of Theorem 1.6). With probability at
least `1 − n⁻¹ exp(−0.02 n (p³ n − 80)) = 1 − P₃(n, p)`, every Blue set of at most `0.4 n` vertices
has at most `(1/3) p (n − 1)` Blue vertices the next day.

Departure from the paper (a gap filled): the step `(n − 2n₂ − 1)² ≥ (0.2 n − 1)²` of the proof
needs `0.2 n − 1 ≥ 0`, and fails for `n = 1` and `n = 3` (e.g. `n = 1`, `n₂ = 0`: `0 < 0.64`).
For `n ≤ 4` the lemma is trivial instead, since `P₃(n, p) ≥ 1` there; for `n ≥ 5` the proof is
the paper's. -/
theorem lemma3_6 {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    1 - denseP3 n p ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
      (B.ncard : ℝ) ≤ 0.4 * n → ((majorityStep G B).ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3) := by
  rcases lt_or_ge n 5 with hn5 | hn5
  · -- `n ≤ 4`: `P₃(n, p) ≥ 1`
    have := shrinkAux_one_le_denseP3 hn (by omega) hp0 hp1
    linarith [gnpProb_nonneg (n := n) (p := p) (fun G => ∀ B : Set (Fin n),
      (B.ncard : ℝ) ≤ 0.4 * n → ((majorityStep G B).ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3)]
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn5
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  -- `n₂ = ⌊0.4 n⌋` and `m = ⌈p(n − 1)/3⌉`
  set n₂ := ⌊(0.4 * n : ℝ)⌋₊ with hn₂
  set m := ⌈(p * ((n : ℝ) - 1) / 3 : ℝ)⌉₊ with hm
  have hn₂x : (n₂ : ℝ) ≤ 0.4 * n := Nat.floor_le (by positivity)
  have hn₂n : (n₂ : ℝ) < n / 2 := by linarith
  have hmn : m ≤ n := Nat.ceil_le.mpr (by nlinarith)
  have hmy : p * ((n : ℝ) - 1) / 3 ≤ m := Nat.le_ceil _
  -- Lemma 3.4: every Blue set of at most `n₂` vertices shrinks to at most `m − 1` vertices
  have h34 := lemma3_4 hn₂n hp0 hp1 hmn
  -- this event implies ours: an integer `< ⌈p(n − 1)/3⌉` is `≤ p(n − 1)/3`
  have hev : gnpProb n p (fun G => ∀ B : Set (Fin n), B.ncard ≤ n₂ →
      (majorityStep G B).ncard < m) ≤ gnpProb n p (fun G => ∀ B : Set (Fin n),
        (B.ncard : ℝ) ≤ 0.4 * n → ((majorityStep G B).ncard : ℝ) ≤ p * ((n : ℝ) - 1) / 3) :=
    gnpProb_mono fun G hG B hB => (Nat.lt_ceil.mp (hG B (Nat.le_floor hB))).le
  -- the bound: `(4ⁿ/n) e^{−E} = n⁻¹ e^{−(E − 2n log 2)}` with `E − 2n log 2 ≥ 0.02 n (p³n − 80)`
  have hbound : 4 ^ n / n * Real.exp (-(2 * p ^ 2 * ((n : ℝ) - 2 * n₂ - 1) ^ 2 * m /
      (n + m - 2))) ≤ denseP3 n p := by
    rw [shrinkAux_four_pow_div_mul_exp, denseP3]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    -- since `n₂ ≤ 0.4 n`, `(n − 2n₂ − 1)² ≥ (0.2 n − 1)²`
    have hsq : (0.2 * n - 1 : ℝ) ^ 2 ≤ ((n : ℝ) - 2 * n₂ - 1) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    -- `m / (n + m − 2) ≥ (p(n − 1)/3) / (n + p(n − 1)/3 − 1) = p / (3 + p) ≥ p / 4`
    have hy : (0 : ℝ) ≤ p * ((n : ℝ) - 1) / 3 := by positivity
    have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hmy
    have hnm : (0 : ℝ) < n + m - 2 := by linarith
    have hfrac : p / 4 ≤ (m : ℝ) / (n + m - 2) := by
      calc p / 4 ≤ p / (3 + p) := by
            gcongr
            linarith
        _ = (p * ((n : ℝ) - 1) / 3) / (n + p * ((n : ℝ) - 1) / 3 - 1) := by
            rw [div_eq_div_iff (by positivity) (by nlinarith)]
            ring
        _ ≤ m / (n + m - 2) := by
            rw [div_le_div_iff₀ (by linarith) hnm]
            nlinarith
    -- `2p²(n − 2n₂ − 1)² m / (n + m − 2) ≥ 2p²(0.2n − 1)² · p/4 = p³ (0.2n − 1)² / 2`
    have hE : p ^ 3 * (0.2 * n - 1 : ℝ) ^ 2 / 2 ≤
        2 * p ^ 2 * ((n : ℝ) - 2 * n₂ - 1) ^ 2 * m / (n + m - 2) := by
      have e1 : p ^ 3 * (0.2 * n - 1 : ℝ) ^ 2 / 2 = 2 * p ^ 2 * (0.2 * n - 1) ^ 2 * (p / 4) := by
        ring
      have e2 : 2 * p ^ 2 * ((n : ℝ) - 2 * n₂ - 1) ^ 2 * m / (n + m - 2) =
          2 * p ^ 2 * ((n : ℝ) - 2 * n₂ - 1) ^ 2 * (m / (n + m - 2)) := by ring
      rw [e1, e2]
      gcongr
    -- `p³(0.2n − 1)²/2 − 2n log 2 = p³(0.02n² − 0.2n + 1/2) − 2n log 2
    --   = 0.02 n (p³n − 10p³ − 100 log 2) + p³/2 ≥ 0.02 n (p³n − 80)`,
    -- since `10p³ + 100 log 2 ≤ 10 + 100 log 2 < 80`
    have hexp : p ^ 3 * (0.2 * n - 1 : ℝ) ^ 2 / 2 - 2 * n * Real.log 2 =
        0.02 * n * (p ^ 3 * n - 10 * p ^ 3 - 100 * Real.log 2) + p ^ 3 / 2 := by
      ring
    have hp3 : p ^ 3 ≤ 1 := pow_le_one₀ hp0.le hp1.le
    have h80 : 10 * p ^ 3 + 100 * Real.log 2 < 80 := by
      have := Real.log_two_lt_d9
      linarith
    have h1 : 0.02 * n * (p ^ 3 * n - 80) ≤
        0.02 * n * (p ^ 3 * n - 10 * p ^ 3 - 100 * Real.log 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : 0 ≤ p ^ 3 / 2 := by positivity
    linarith
  linarith

end PowerOfFew.Dense

end
