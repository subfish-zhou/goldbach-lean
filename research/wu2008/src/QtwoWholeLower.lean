import QtwoWeightedPayment

namespace QtwoWholeLower
open Real Wu2008DoubleSieve PositiveCoreResume PositiveSecondPayment
open FixedCoefficientUpperEnclosure (a b)
noncomputable section

def classicalFloor : ℝ := GlobalLogRelationPayment.lowerRational+QtwoWeightedMoment.gain/4+
  BaseSharedSlack.gain+SixthRetainedSlack.gain

/-- All old negative slots stay in the existing signed identity. The old sixth
improvement is not used here, so it can subsequently be replaced by Cinf once. -/
theorem classical_floor : classicalFloor < JointHMotherPayment.unroundedCoefficient := by
  have he := GlobalLowerSlack.actual_minus_lowerRational
  obtain ⟨hb,hh,hm,hl,hj,hjp,h5,h5r,h6,h6r,h4⟩ := GlobalLowerSlack.component_nonnegative
  have hf := QtwoWeightedPayment.gain_paid
  have hs := BaseSharedSlack.block_payment
  have ha := GlobalLowerSlack.payment_nonnegative.1
  have hr := SixthRetainedSlack.retained_strict
  unfold BaseSharedSlack.block at hs
  unfold GlobalLowerSlack.realSlack at he
  unfold classicalFloor
  linarith only [he,hj,hjp,h5r,h6,h6r,h4,hf,hs,ha,hr]

/-- Exact complete coefficient; both old positive payments and the intermediate
GammaLog6 cancel, while the original 47/481250 debit remains. -/
theorem Qtwo_identity : PositiveTwoPayment.Qtwo =
    JointHMotherPayment.unroundedCoefficient+(FeedbackLimit.Cinf-47/481250)/4+
      2*(U8CanonicalMother.L-U8CanonicalMother.I)+
      (fifthGain-fifthHGain)/4+2*(secondGain-BaseHGain.originalGain) := by
  have hi := U8ActualThreshold.actual_identity
  have hl := LogP2.coefficient_difference
  unfold PositiveTwoPayment.Qtwo Qpositive fifthIncrement FeedbackLimit.Qinf
  linarith only [hi,hl]

/-- Preserve the full newly paid positive integral and Cinf in the complete lower. -/
def fullFloor : ℝ := classicalFloor+(FeedbackLimit.Cinf-47/481250)/4+
  U8ActualThreshold.gainLower+(fifthGain-fifthHGain)/4+
  2*(secondGain-BaseHGain.originalGain)

theorem full_floor : fullFloor < PositiveTwoPayment.Qtwo := by
  rw [Qtwo_identity]
  unfold fullFloor
  linarith only [classical_floor,U8ActualThreshold.exact_weight_gain_bounds.1]

/-- An entirely rational floor of the complete coefficient, not just a gain. -/
def rationalFloor : ℝ := classicalFloor-(47/481250)/4+U8ActualThreshold.gainLower+
  (4*fullSeed*(b-a)^2-fifthHGain)/4+2*(secondGain-BaseHGain.originalGain)

theorem rational_le_full : rationalFloor ≤ fullFloor := by
  have hf := fifth_gain_seed_lower
  have hc := FeedbackLimit.Cinf_nonneg
  unfold rationalFloor fullFloor
  change 4*fullSeed*(b-a)^2 ≤ fifthGain at hf
  linarith only [hf,hc]

theorem rational_floor : rationalFloor < PositiveTwoPayment.Qtwo := rational_le_full.trans_lt full_floor

/-- The exact remaining quantities, with no sign assigned to an unknown target gap. -/
def remainder : ℝ :=
  (GlobalLowerSlack.realSlack-QtwoWeightedMoment.gain+GlobalLowerSlack.analyticPaymentSlack)/4+
  GlobalLowerSlack.retainedPaymentSlack-BaseSharedSlack.gain-SixthRetainedSlack.gain+
  (2*(U8CanonicalMother.L-U8CanonicalMother.I)-U8ActualThreshold.gainLower)

theorem remainder_identity : PositiveTwoPayment.Qtwo-fullFloor = remainder := by
  have h := GlobalLowerSlack.actual_minus_lowerRational
  rw [Qtwo_identity]
  unfold fullFloor classicalFloor remainder
  linarith only [h]

theorem remainder_pos : 0 < remainder := by rw [← remainder_identity]; exact sub_pos.mpr full_floor

/-- The new full-weight classical gain is determined by the old exact rational
payment and the analytically derived weighted mean; no numerical quadrature. -/
theorem gain_exact_relation : QtwoWeightedMoment.gain = GlobalLowerSlack.fifthGain*
    b^2/QtwoWeightedMoment.meanXY := by
  unfold QtwoWeightedMoment.gain QtwoWeightedMoment.rate GlobalLowerSlack.fifthGain
    GlobalLowerSlack.densityRate
  field_simp [QtwoWeightedMoment.params.1.ne',
    (QtwoWeightedMoment.params.1.trans QtwoWeightedMoment.params.2.1).ne',
    QtwoWeightedMoment.params.2.2.1.ne']

theorem gain_strict : GlobalLowerSlack.fifthGain < QtwoWeightedMoment.gain := by
  rw [gain_exact_relation]
  apply (lt_div_iff₀ QtwoWeightedMoment.params.2.2.1).mpr
  exact mul_lt_mul_of_pos_left QtwoWeightedMoment.params.2.2.2 GlobalLowerSlack.fifthGain_pos

end
end QtwoWholeLower
