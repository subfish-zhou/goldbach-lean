import AnalyticNumberTheory.Sieve.W1LemmaB
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-! # W2 weight-cancellation lemmas

In primitive-character large-sieve and all-character weighted
assembly, the reciprocal factors `φ(q)/q` and `q/φ(q)` occur
alongside weights such as `μ²·3^ω`. Their product is 1.
This module proves only the three algebraic cancellation identities;
it does not by itself transfer a primitive-character theorem to
an all-character mean.

All three require `q ≥ 1`, ensuring `φ(q) ≠ 0` by `Nat.totient_pos`:

* `totient_div_q_mul_q_div_totient_eq_one` (W2a):
  `(φ(q)/q)·q / φ(q) = 1`.
* `q_div_totient_mul_totient_div_q_eq_one` (W2b):
  `(q/φ(q))·φ(q) / q = 1`, the symmetric form.
* `mul_totient_div_q_mul_q_div_totient` (W2c):
  `w·(φ(q)/q)·(q/φ(q)) = w`, by W2a and ring algebra.
-/

namespace AnalyticNumberTheory.Sieve

/-- **W2a**, left-associated cancellation:
`((φ(q):ℝ)/q · q) / φ(q) = 1` for `q ≥ 1`.
Use `field_simp` with `q ≠ 0` and `φ(q) ≠ 0`,
the latter from `Nat.totient_pos`. -/
theorem totient_div_q_mul_q_div_totient_eq_one {q : ℕ} (hq : 1 ≤ q) :
    ((Nat.totient q : ℝ) / (q : ℝ) * (q : ℝ) / (Nat.totient q : ℝ)) = 1 := by
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqpos)
  have hφR : (Nat.totient q : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hqpos).ne'
  field_simp [hqR, hφR]

/-- **W2b**, symmetric cancellation:
`((q:ℝ)/φ(q) · φ(q)) / q = 1` for `q ≥ 1`.
As in W2a, use `field_simp` with `q ≠ 0` and `φ(q) ≠ 0`. -/
theorem q_div_totient_mul_totient_div_q_eq_one {q : ℕ} (hq : 1 ≤ q) :
    ((q : ℝ) / (Nat.totient q : ℝ) * (Nat.totient q : ℝ) / (q : ℝ)) = 1 := by
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqpos)
  have hφR : (Nat.totient q : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hqpos).ne'
  field_simp [hqR, hφR]

/-- **W2c**: for `q ≥ 1` and any real weight `w`,
`w·(φ(q)/q)·(q/φ(q)) = w`.
Use `mul_div_assoc` to put the inner product in W2a's
left-associated form, cancel it to 1, and finish with ring algebra. -/
theorem mul_totient_div_q_mul_q_div_totient {q : ℕ} (hq : 1 ≤ q) (w : ℝ) :
    w * ((Nat.totient q : ℝ) / (q : ℝ)) * ((q : ℝ) / (Nat.totient q : ℝ)) = w := by
  have hinner :
      ((Nat.totient q : ℝ) / (q : ℝ)) * ((q : ℝ) / (Nat.totient q : ℝ)) = 1 := by
    rw [← mul_div_assoc]
    exact totient_div_q_mul_q_div_totient_eq_one hq
  rw [mul_assoc, hinner]
  ring

end AnalyticNumberTheory.Sieve
