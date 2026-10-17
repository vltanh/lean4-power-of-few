module

public import Mathlib

/-!
# Upper bounds on binomial coefficients

* `Nat.centralBinom_lt_four_pow_div_sqrt`: `C(2m, m) < 2^(2m) / √(2m)` for `m ≥ 1`
  (Matoušek–Nešetřil, *Invitation to Discrete Mathematics*, Proposition 2.6.2, which the dense
  paper cites in the proof of its Lemma 3.2).
* `Nat.choose_le_exp_mul_binEntropy`: `C(n, k) ≤ exp(n H(k / n))`, with `H` the binary entropy in
  nats (the "routine Stirling bound" in the proof of the sparse paper's Lemma 2.3).
-/

@[expose] public section

namespace Nat

/-- `C(2m, m) < 2^(2m) / √(2m)` for `m ≥ 1` (Matoušek–Nešetřil, *Invitation to Discrete
Mathematics*, 2nd ed., Proposition 2.6.2). -/
theorem centralBinom_lt_four_pow_div_sqrt {m : ℕ} (hm : 1 ≤ m) :
    (centralBinom m : ℝ) < 4 ^ m / Real.sqrt (2 * m) := by
  sorry

/-- `C(n, k) ≤ exp(n H(k / n))`, where `H(x) = −x log x − (1 − x) log(1 − x)` is the binary
entropy. -/
theorem choose_le_exp_mul_binEntropy (n k : ℕ) :
    (n.choose k : ℝ) ≤ Real.exp (n * Real.binEntropy (k / n)) := by
  sorry

end Nat
