import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighDelta
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

private theorem sum_div_multiples_le_log {L : ℝ} (hL : 1 ≤ L)
    {d : ℕ} (hd : 0 < d) :
    (∑ r ∈ Ioc 0 ⌊L⌋₊, if d ∣ r then (d : ℝ) / r else 0) ≤ 1 + Real.log L := by
  exact MathlibNt.AnalyticNumberTheory.LargeSieve.LcmWeightBounds.sum_div_multiples_le_log hL hd

/-- The gcd harmonic row sum is paid by `tau_2(q)`, independently of
any modulus coefficient or coprimality restriction. -/
theorem sum_gcd_div_le_tau_log {L : ℝ} (hL : 1 ≤ L)
    (Q : Finset ℕ) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊) {q : ℕ} (hq : 0 < q) :
    (∑ r ∈ Q, (q.gcd r : ℝ) / r) ≤
      (fouvryTau 2 q : ℝ) * (1 + Real.log L) := by
  exact MathlibNt.AnalyticNumberTheory.LargeSieve.LcmWeightBounds.sum_gcd_div_le_tau_log hL Q hQ hq

private theorem one_div_lcm_eq_gcd_div {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0) :
    (1 : ℝ) / (q.lcm r : ℝ) = (q.gcd r : ℝ) / ((q : ℝ) * r) := by
  exact MathlibNt.AnalyticNumberTheory.LargeSieve.LcmWeightBounds.one_div_lcm_eq_gcd_div hq hr

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

/-- The actual very-large-gcd remainder, uniformly for every integer residue
and signed beta/modulus weights. This is the endpoint `δ > T`, not `δ > log^B`. -/
theorem smoothWULargeDelta_abs_le_highDelta
   {k : ℕ} (hk : 1 ≤ k) (j : ℕ)
   {T L : ℝ} (hT : 1 ≤ T) (hL : 1 ≤ L)
   (M : ℝ) (N Q : Finset ℕ)
   (hN : N ⊆ Ioc 0 ⌊T⌋₊) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊)
   (β c : ℕ → ℝ) (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
   (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (a : ℤ) :
   |smoothWULargeDelta M T N Q β c a| ≤
     |M * dyadicCutoffMass| * T * (1 + Real.log T) ^ (k ^ 2 - 1) *
       (1 + Real.log L) ^ (2 * j ^ 2 + 1) := by
 let V := T * (1 + Real.log T) ^ (k ^ 2 - 1)
 have hV : 0 ≤ V := by
   dsimp [V]
   have := Real.log_nonneg hT
   positivity
 have hcov {q r : ℕ} (hδ : T < (q.gcd r : ℝ)) :
     |betaCovariance N β q r| ≤ V :=
   (betaCovariance_abs_le_highDelta (by linarith) N hN β hδ).trans
     (sum_alpha_sq_le_fouvryTau hk hT N hN β hβ)
 unfold smoothWULargeDelta
 rw [abs_mul]
 calc
   _ ≤ |M * dyadicCutoffMass| *
       (∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
         |c q * c r / (q.lcm r : ℝ)| * V) := by
     apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
     apply (abs_sum_le_sum_abs _ _).trans
     apply sum_le_sum
     intro q _
     apply (abs_sum_le_sum_abs _ _).trans
     apply sum_le_sum
     intro r _
     split_ifs with hδ
     · rw [abs_mul]
       exact mul_le_mul_of_nonneg_left (hcov hδ) (abs_nonneg _)
     · simpa only [abs_zero] using mul_nonneg (abs_nonneg _) hV
   _ = |M * dyadicCutoffMass| *
       ((∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
         |c q * c r / (q.lcm r : ℝ)|) * V) := by simp only [sum_mul]
   _ ≤ |M * dyadicCutoffMass| * ((1 + Real.log L) ^ (2 * j ^ 2 + 1) * V) := by
     apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
     apply mul_le_mul_of_nonneg_right _ hV
     exact sum_abs_lcm_weight_le_log j hL (reducedModuli Q a)
       ((filter_subset _ _).trans hQ) c (fun q hq => hc q (mem_filter.mp hq).1)
   _ = _ := by dsimp [V]; ring

end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
