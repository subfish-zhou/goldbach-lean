import F1LowerResidualAssembly

noncomputable section
open Real Set MeasureTheory FirstIntegralRecovery FirstCRationalPayment
open Wu2008DoubleSieve SharpLogRecurrence F1RemainingRecovery F1UnpaidRecovery
open F1FixedSquareRecovery
open scoped Interval
namespace F1SecondLogRecovery

/-- The actual second main-log error, never a second copy of the full kernel. -/
def secondExact (u : ℝ) : ℝ := splitL (u-1)/u *
  (log (((1327:ℝ)/200-1)/(u+1))-splitL (((1327:ℝ)/200-1)/(u+1)))

/-- Retain the term that the old augmented_kernel proof discarded. -/
theorem augmented_retained {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    (1+secondFactorRatio)*(2*momentWeight u/momentDenom u)+secondExact u ≤
      cExactKernel (1327/200) u-cLowerKernel (1327/200) u := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hu' : u ∈ Icc 2 ((1327:ℝ)/200-2) := by constructor <;> linarith [hu.1,hu.2]
  have hp := first_log_augmented hu
  have hl := ratio_log_payment hu'
  have hlin : 0 ≤ 2*((1327:ℝ)/200-2-u)/((1327:ℝ)/200+u) := by
    apply div_nonneg (by linarith [hu.2]) (by linarith [hu.1])
  have herr : 0 ≤ (log (u-1)-splitL (u-1))/u :=
    div_nonneg (sub_nonneg.mpr (splitL_le_log (by linarith [hu.1]))) hu0.le
  have hprod := mul_le_mul (div_le_div_of_nonneg_right hp hu0.le) hl hlin herr
  have hid : ((1+secondFactorRatio)*((u-2)^5/((u+2)^3*(u^2+16*u+4))))/u *
      (2*((1327:ℝ)/200-2-u)/((1327:ℝ)/200+u)) =
      (1+secondFactorRatio)*(2*momentWeight u/momentDenom u) := by
    dsimp [momentWeight,momentDenom]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hid] at hprod
  have heq : cExactKernel (1327/200) u-cLowerKernel (1327/200) u =
      (log (u-1)-splitL (u-1))/u*log (((1327:ℝ)/200-1)/(u+1))+secondExact u := by
    unfold cExactKernel cLowerKernel secondExact
    ring
  rw [heq]
  linarith only [hprod]

theorem square_retained {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    (1+secondFactorRatio)*
      ((4*momentA*momentWeight u-2*momentA^2*(momentWeight u*momentDenom u))+
        squareLower u)+secondExact u ≤
      cExactKernel (1327/200) u-cLowerKernel (1327/200) u := by
  have h := mul_le_mul_of_nonneg_left (fixed_square_lower hu)
    (show 0 ≤ 1+secondFactorRatio by linarith only [secondFactorRatio_pos])
  linarith only [h,augmented_retained hu]

theorem secondExact_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    0 ≤ secondExact u := by
  have hu' : u ∈ Icc 2 ((1327:ℝ)/200-2) := by constructor <;> linarith [hu.1,hu.2]
  exact mul_nonneg (div_nonneg (splitL_nonneg (by linarith [hu.1]))
    (by linarith [hu.1])) (sub_nonneg.mpr (splitL_le_log (ratio_ge_one hu')))

/-- Both already prescribed factors of LA retain their linear lowerLog term. -/
theorem splitL_linear {u : ℝ} (hu : 2 ≤ u) :
    2*(u-2)/(u+2)+2*(u-2)/(3*u-2) ≤ splitL (u-1) := by
  have hu0 : u ≠ 0 := by linarith
  have hp : u+2 ≠ 0 := by linarith
  have hq : 3*u-2 ≠ 0 := by linarith
  have ha : 0 ≤ (u-2)/(u+2) := div_nonneg (by linarith) (by linarith)
  have hb : 0 ≤ (u-2)/(3*u-2) := div_nonneg (by linarith) (by linarith)
  have heq : splitL (u-1) =
      2*((u-2)/(u+2))+2*((u-2)/(u+2))^3/3+
      (2*((u-2)/(3*u-2))+2*((u-2)/(3*u-2))^3/3) := by
    have he1 : (((1+(u-1))/2)-1)/(((1+(u-1))/2)+1) = (u-2)/(u+2) := by
      rw [show (1+(u-1))/2-1 = (u-2)/2 by ring,
        show (1+(u-1))/2+1 = (u+2)/2 by ring]
      exact div_div_div_cancel_right₀ (by norm_num : (2:ℝ) ≠ 0) _ _
    have he2 : (2*(u-1)/(1+(u-1))-1)/(2*(u-1)/(1+(u-1))+1) = (u-2)/(3*u-2) := by
      have he : 1+(u-1)=u := by ring
      rw [he]
      field_simp [hu0]
      ring
    unfold splitL lowerLog
    rw [he1,he2]
  rw [heq]
  have ha3 : 0 ≤ 2*((u-2)/(u+2))^3/3 := by positivity
  have hb3 : 0 ≤ 2*((u-2)/(3*u-2))^3/3 := by positivity
  simp only [mul_div_assoc]
  linarith only [ha3,hb3]

end F1SecondLogRecovery
