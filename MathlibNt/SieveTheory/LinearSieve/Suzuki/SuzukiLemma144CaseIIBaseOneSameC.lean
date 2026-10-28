import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIFinalBoundary

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- At depth one the finite continuous source layer is the literal initial
function `(3-s)/s` throughout the low strip. -/
theorem finiteSourceLayer_one_eq_lowStrip {s : ℝ} (hs3 : s ≤ 3) :
    finiteSourceLayer 1 2 1 s = (3 - s) / s := by
  simp [finiteSourceLayer, suzukiLayer, baseLower, dPowDensity,
    intervalIntegral.integral_const]
  norm_num at hs3 ⊢
  rw [min_eq_left hs3]
  rw [div_eq_mul_inv, mul_comm]

/-- The Section 13 plus-hat initial condition at `β=2`, written in the
normalization occurring in the depth-one error envelope. -/
theorem section13Hat_plus_initial_lowStrip
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {s : ℝ} (hs : 0 < s) (hs3 : s ≤ 3) :
    H.Tplus s = 1 / s ^ 2 := by
  have hi := hH.initial_plus s hs (by norm_num at hs3 ⊢; exact hs3)
  simp only [weightedHat, Section13HatLayers.T] at hi
  norm_num at hi
  apply (mul_left_cancel₀ (sq_pos_of_pos hs).ne')
  calc
    s ^ 2 * H.Tplus s = 1 := hi
    _ = s ^ 2 * (1 / s ^ 2) := by field_simp

/-- On the low strip the exact hat initial value gives the uniform lower bound
`1/s` for the depth-one production error envelope. -/
theorem one_div_le_errorEnvelope_one_lowStrip
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {D d s : ℝ} (hD : 1 < D) (hs : 0 < s) (hs3 : s ≤ 3) :
    1 / s ≤ errorEnvelope H 1 D d s := by
  have hlog : 0 < Real.log D := Real.log_pos hD
  have hbase : 1 ≤ 1 + s ^ d / Real.log D := by
    have hp : 0 ≤ s ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg hs.le _) hlog.le
    linarith
  have hrpow : 1 ≤ (1 + s ^ d / Real.log D) ^ s := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hbase hs.le
  rw [errorEnvelope_odd (by decide : Odd 1),
    section13Hat_plus_initial_lowStrip hH hs hs3]
  calc
    1 / s = 1 * (1 / s) := by ring
    _ ≤ (1 + s ^ d / Real.log D) ^ s * (1 / s) :=
      mul_le_mul_of_nonneg_right hrpow (by positivity)
    _ = (1 + s ^ d / Real.log D) ^ s * s * (1 / s ^ 2) := by
      field_simp [hs.ne']


/-- The Euler product multiplying both base-one brackets is nonnegative. -/
theorem suzukiVProduct_nonneg (S : BoundingSieve) (x : ℝ) :
    0 ≤ suzukiVProduct S x := by
  exact (suzukiVProduct_pos S x).le


end MathlibNt.SieveTheory
