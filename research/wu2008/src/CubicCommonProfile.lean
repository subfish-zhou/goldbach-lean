import OriginalSigmaCubicOuterPayment

namespace CubicCommonProfile
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals OriginalProfileSigmaPayment
open OriginalSigmaStrength OriginalSigmaCubicRestoration Wu04WholeCollection
open scoped Interval BigOperators
noncomputable section

def cubicNumerator (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9, z k*(cubicOuterPrimitive (upperNode k)-cubicOuterPrimitive (upperLeft k))
def cubicPaidNumerator (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9, z k*cubicCellPaid (upperLeft k) (upperNode k)
def fullNumerator (z : Fin 9 → ℝ) : ℝ :=
  RetainedCommonProfile.paidNumerator z+cubicPaidNumerator z
def fullD0 : ℝ := retainedPaid 3+cubicPaid 3
def actualLower (z : Fin 9 → ℝ) : ℝ := fullNumerator z/(1-D0)
def finiteLower (z : Fin 9 → ℝ) : ℝ := fullNumerator z/(1-fullD0)

theorem fullD0_le : fullD0≤D0 := by
  have h := fullPaid_le_sigma (t := 3) (by norm_num)
  norm_num only [show (3:ℝ)+2=5 by norm_num,show (3:ℝ)+1=4 by norm_num] at h
  exact h

theorem fullD0_lt_one : fullD0<1 := fullD0_le.trans_lt D0_lt_one

theorem cubicNumerator_integral (z : Fin 9 → ℝ) :
    cubicNumerator z = ∫ t in (1:ℝ)..3, nineProfile z t*cubicWeight t := by
  rw [profile_integral_cells z le_rfl (by norm_num [upperNode])
    (cubicWeight_continuous (by norm_num) (by norm_num))]
  apply Finset.sum_congr rfl
  intro k _
  have hb := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [cubicWeight_integral (by linarith [hb.1] : 0<cellLeft 1 k) hb.2.1,he]

theorem cubicPaidNumerator_le {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    cubicPaidNumerator z ≤ cubicNumerator z := by
  apply Finset.sum_le_sum
  intro k _
  have hc := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [he] at hc
  exact mul_le_mul_of_nonneg_left
    (cubicCellPaid_le (by linarith [hc.1]) (by linarith [hc.1,hc.2.1])) (hz k)

/-- The two original L summands jointly pay the same actual profile and denominator. -/
theorem actualLower_le_profile {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    actualLower z ≤ aProfile (nineProfile z) := by
  rw [actualLower,aProfile_eq]
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr D0_lt_one).le
  apply le_trans (b := RetainedCommonProfile.numerator z+cubicNumerator z)
    (add_le_add (RetainedCommonProfile.paidNumerator_le hz) (cubicPaidNumerator_le hz))
  rw [RetainedCommonProfile.numerator_integral,cubicNumerator_integral]
  have hp := nineProfile_integrable z
  have hl := hp.mul_continuousOn (retainedWeight_continuous (by norm_num) (by norm_num))
  have hc := hp.mul_continuousOn (cubicWeight_continuous (by norm_num) (by norm_num))
  rw [← intervalIntegral.integral_add hl hc]
  apply intervalIntegral.integral_mono_on (by norm_num) (hl.add hc)
    ((profile_div_integrable hp).mul_continuousOn original_sigma_continuous)
  intro t ht
  have ht0 : 0<t := by linarith [ht.1]
  have h := mul_le_mul_of_nonneg_left (fullPaid_le_sigma ht.1)
    (div_nonneg (nineProfile_nonneg hz t) ht0.le)
  convert h using 1 <;> first | rfl | skip
  unfold retainedWeight cubicWeight
  ring

theorem finiteLower_le_profile {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k)
    (hn : 0≤fullNumerator z) : finiteLower z ≤ aProfile (nineProfile z) := by
  apply le_trans (b := actualLower z) _ (actualLower_le_profile hz)
  apply div_le_div_of_nonneg_left hn (sub_pos.mpr D0_lt_one)
  linarith only [fullD0_le]

end
end CubicCommonProfile
