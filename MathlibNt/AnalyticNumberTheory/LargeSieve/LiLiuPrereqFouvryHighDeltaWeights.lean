import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySmallDelta
import MathlibNt.AnalyticNumberTheory.LargeSieve.LcmWeightBounds


/-!
# Logarithmic lcm-weight sum and the very-large-gcd zero mode

The symmetric inequality `2 |c_q c_r| ≤ c_q² + c_r²` pays the two modulus
weights by a single divisor moment. No submultiplicativity of `tau_j` at
noncoprime arguments, and no arithmetic-progression input, is assumed.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

noncomputable section


/-- The gcd harmonic row sum is paid by `tau_2(q)`, independently of
any modulus coefficient or coprimality restriction. -/
theorem sum_gcd_div_le_tau_log {L : ℝ} (hL : 1 ≤ L)
    (Q : Finset ℕ) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊) {q : ℕ} (hq : 0 < q) :
    (∑ r ∈ Q, (q.gcd r : ℝ) / r) ≤
      (fouvryTau 2 q : ℝ) * (1 + Real.log L) := by
  exact MathlibNt.AnalyticNumberTheory.LargeSieve.LcmWeightBounds.sum_gcd_div_le_tau_log hL Q hQ hq


theorem sum_one_div_lcm_le_tau_log {L : ℝ} (hL : 1 ≤ L)
    (Q : Finset ℕ) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊) {q : ℕ} (hq : 0 < q) :
    (∑ r ∈ Q, (1 : ℝ) / (q.lcm r : ℝ)) ≤
      (fouvryTau 2 q : ℝ) / q * (1 + Real.log L) := by
  exact MathlibNt.AnalyticNumberTheory.LargeSieve.LcmWeightBounds.sum_one_div_lcm_le_tau_log hL Q hQ hq

/-- Fully evaluated double lcm sum for arbitrary signed fixed-order
modulus weights. Even order zero is allowed. -/
theorem sum_abs_lcm_weight_le_log (j : ℕ) {L : ℝ} (hL : 1 ≤ L)
    (Q : Finset ℕ) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊) (c : ℕ → ℝ)
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) :
    (∑ q ∈ Q, ∑ r ∈ Q, |c q * c r / (q.lcm r : ℝ)|) ≤
      (1 + Real.log L) ^ (2 * j ^ 2 + 1) := by
  exact MathlibNt.AnalyticNumberTheory.LargeSieve.LcmWeightBounds.sum_abs_lcm_weight_le_log j hL Q hQ c hc


end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
