module

public import Mathlib

/-!
# Feige and Ofek's bound for the heavy pairs: the six cases

The combinatorial core of the bound on the heavy pairs (Feige–Ofek 2005, Section 2.2; Chin–Rao–Vu
2015, the appendix that proves their heavy-pair lemma), stated on block data.

The coordinates of `x` are grouped into the blocks `S_i = {u : 2^(i−1) < √n |xᵤ| ≤ 2^i}`, `i ∈ ℤ`,
and those of `y` into blocks `T_j`. With `sᵢ = |S_i|`, `tⱼ = |T_j|`, `e_{ij} = e(S_i, T_j)`,
`αᵢ = sᵢ 4^i / n`, `βⱼ = tⱼ 4^j / n`, `μ_{ij} = sᵢ tⱼ d / n`, `λ_{ij} = e_{ij} / μ_{ij}` and
`σ_{ij} = λ_{ij} √d / 2^(i+j)`, the heavy pairs contribute at most
`∑_{2^(i+j) > √d} e_{ij} 2^(i+j) / n = √d ∑ αᵢ βⱼ σ_{ij}`, and `∑ αᵢ ≤ 4`, `∑ βⱼ ≤ 4`. The pairs
`(i, j)` with `sᵢ ≤ tⱼ` fall into six cases, each taken only if the earlier ones fail:

1. `σ_{ij} ≤ 1`: at most `∑ αᵢ βⱼ ≤ 16`;
2. `λ_{ij} ≤ c₂`: then `σ_{ij} ≤ c₂`, at most `16 c₂`;
3. `2^i > √d 2^j`: bounded degrees give `λ_{ij} ≤ c₁ n / tⱼ`, so `βⱼ σ_{ij} ≤ c₁ √d 2^j / 2^i`, a
   geometric sum over `j`: at most `8 c₁`;
4. otherwise the discrepancy property, with `m = tⱼ`, gives
   `σ_{ij} αᵢ log λ_{ij} ≤ c₃ (2^i / (2^j √d)) log(n / tⱼ)`, and
   (a) if `log λ_{ij} > (1/4) log(n / tⱼ)`: `σ_{ij} αᵢ ≤ 4 c₃ 2^i / (2^j √d)`, a geometric sum
       over `i` (as `2^i ≤ √d 2^j`): at most `32 c₃`;
   (b) if not, and `log(n / tⱼ) ≤ 4 log 2^j`: then `λ_{ij} ≤ 2^j`, so `2^i < √d`, and
       `log λ_{ij} ≥ 1`: `σ_{ij} αᵢ ≤ 4 c₃ (2^i / √d) (log 2^j / 2^j)`, at most `32 c₃`;
   (c) if not, and `log(n / tⱼ) > 4 log 2^j`: then `λ_{ij} ≤ 1 / βⱼ`, so
       `βⱼ σ_{ij} ≤ √d / 2^(i+j)`, a geometric sum over `j`: at most `8`.

The pairs with `sᵢ > tⱼ` are bounded in the same way with the roles of `x` and `y` exchanged. In
total the heavy pairs contribute at most `2 (24 + 8 c₁ + 16 c₂ + 64 c₃) √d`.
-/

@[expose] public section

noncomputable section

namespace PowerOfFew.FeigeOfek

/-- **The six cases of Feige and Ofek**, on block data. Let `I, J ⊆ ℤ` be finite sets of block
indices, `s, t` the block sizes (between `1` and `n`) and `e` the block edge counts, with
`∑_{i ∈ I} sᵢ 4^i / n ≤ 4` and `∑_{j ∈ J} tⱼ 4^j / n ≤ 4` (the vectors have norm at most `1`),
`e_{ij} ≤ c₁ d min(sᵢ, tⱼ)` (bounded degrees), and, for every pair, `e_{ij} ≤ c₂ μ_{ij}` or
`e_{ij} log(e_{ij} / μ_{ij}) ≤ c₃ m log(n / m)` with `μ_{ij} = sᵢ tⱼ d / n` and `m = max(sᵢ, tⱼ)`
(discrepancy). Then the block pairs with `2^(i+j) > √d` contribute
`∑ e_{ij} 2^(i+j) / n ≤ 2 (24 + 8 c₁ + 16 c₂ + 64 c₃) √d`. -/
theorem sum_blocks_le {n d c₁ c₂ c₃ : ℝ} (hn : 0 < n) (hd : 0 < d) (hc₁ : 0 ≤ c₁)
    (hc₂ : Real.exp 1 ≤ c₂) (hc₃ : 0 ≤ c₃) (I J : Finset ℤ) (s t : ℤ → ℝ) (e : ℤ → ℤ → ℝ)
    (hs : ∀ i ∈ I, 1 ≤ s i ∧ s i ≤ n) (ht : ∀ j ∈ J, 1 ≤ t j ∧ t j ≤ n)
    (hα : ∑ i ∈ I, s i * 4 ^ i / n ≤ 4) (hβ : ∑ j ∈ J, t j * 4 ^ j / n ≤ 4)
    (he : ∀ i ∈ I, ∀ j ∈ J, 0 ≤ e i j)
    (hdeg : ∀ i ∈ I, ∀ j ∈ J, e i j ≤ c₁ * d * s i ∧ e i j ≤ c₁ * d * t j)
    (hdisc : ∀ i ∈ I, ∀ j ∈ J, e i j ≤ c₂ * (s i * t j * d / n) ∨
      e i j * Real.log (e i j / (s i * t j * d / n)) ≤
        c₃ * max (s i) (t j) * Real.log (n / max (s i) (t j))) :
    ∑ i ∈ I, ∑ j ∈ J,
        (if Real.sqrt d < (2 : ℝ) ^ (i + j) then e i j * (2 : ℝ) ^ (i + j) / n else 0) ≤
      2 * (24 + 8 * c₁ + 16 * c₂ + 64 * c₃) * Real.sqrt d := by
  sorry

end PowerOfFew.FeigeOfek
