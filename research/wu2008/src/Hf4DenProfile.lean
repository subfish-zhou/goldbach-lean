import Hf4DenEndpoint

noncomputable section
namespace Hf4Den
open Real NodeExtension FirstFeedbackIntegrals ActualNineFeedback

/-- Exactly the latest paid numerator; no new sigma approximation. -/
def numerator : ℝ := CorrectionD0Joint.numerator+
  Hf4Refine.finiteVariation NineFeedbackStrength.originalH+
  Hf4Continue.newVariation NineFeedbackStrength.originalH

theorem numerator_pos : 0 < numerator := by
  have h := (lt_div_iff₀ (sub_pos.mpr D0FullDensity.finiteD_lt_one)).mp
    Hf4Continue.finiteProfile_pos
  simpa only [zero_mul, numerator] using h

theorem numerator_le_full : numerator ≤
    SigmaVariableFull.numerator NineFeedbackStrength.originalH+
      Hf4Continue.newVariation NineFeedbackStrength.originalH :=
  add_le_add ((add_le_add CorrectionD0Joint.numerator_le le_rfl).trans
    (Hf4Refine.old_numerator_add_payment_le CoupledIntegralRecovery.originalH_nonneg)) le_rfl

theorem numerator_le_actual : numerator ≤
    ∫ t in (1:ℝ)..3, nineProfile NineFeedbackStrength.originalH t/t*sigma 3 (t+2) (t+1) :=
  numerator_le_full.trans Hf4Continue.full_numerator_add_new_le

/-- Consume the existing full-D0 endpoint certificate, preserving its common max. -/
def profile : ℝ := numerator/(1-D0FullDensity.dPaid)

theorem profile_pos : 0 < profile :=
  div_pos numerator_pos (sub_pos.mpr D0FullDensity.dPaid_lt_one)

theorem old_profile_le : Hf4Continue.finiteProfile ≤ profile :=
  div_le_div_of_nonneg_left numerator_pos.le (sub_pos.mpr D0FullDensity.dPaid_lt_one)
    (by linarith only [D0FullDensity.finiteD_le_dPaid])

theorem profile_le_actual : profile ≤ aProfile (nineProfile NineFeedbackStrength.originalH) := by
  calc
    profile ≤ numerator/(1-D0) :=
      div_le_div_of_nonneg_left numerator_pos.le (sub_pos.mpr D0_lt_one)
        (by linarith only [D0FullDensity.dPaid_le])
    _ ≤ _ := by
      rw [aProfile_eq]
      exact div_le_div_of_nonneg_right numerator_le_actual (sub_pos.mpr D0_lt_one).le

/-- Explicit same-numerator denominator gain, not an unpaid integral renamed. -/
def denominatorGain : ℝ := numerator*(D0FullDensity.dPaid-D0FullDensity.finiteD)/
  ((1-D0FullDensity.dPaid)*(1-D0FullDensity.finiteD))

theorem denominatorGain_nonneg : 0 ≤ denominatorGain :=
  div_nonneg (mul_nonneg numerator_pos.le (sub_nonneg.mpr D0FullDensity.finiteD_le_dPaid))
    (mul_pos (sub_pos.mpr D0FullDensity.dPaid_lt_one)
      (sub_pos.mpr D0FullDensity.finiteD_lt_one)).le

theorem profile_balance : profile=Hf4Continue.finiteProfile+denominatorGain := by
  have hd := (sub_pos.mpr D0FullDensity.dPaid_lt_one).ne'
  have hf := (sub_pos.mpr D0FullDensity.finiteD_lt_one).ne'
  change numerator/(1-D0FullDensity.dPaid)=numerator/(1-D0FullDensity.finiteD)+denominatorGain
  unfold denominatorGain
  field_simp
  ring

/-- The full E endpoint certificate replaces the signed payment exactly once. -/
def terminal : ℝ := log 2*profile+TerminalECells.mass NineFeedbackStrength.originalH

theorem terminal_le_actual : terminal ≤ firstFeedback NineFeedbackStrength.originalH 3 3 := by
  have ha := mul_le_mul_of_nonneg_left profile_le_actual (log_nonneg (by norm_num : (1:ℝ)≤2))
  have he := TerminalECells.mass_le CoupledIntegralRecovery.originalH_nonneg
  unfold terminal
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  linarith only [ha,he]

theorem terminal_balance : terminal=Hf4Continue.terminal+
    log 2*denominatorGain+TerminalESigned.eUnpaid := by
  unfold terminal
  rw [profile_balance]
  unfold Hf4Continue.terminal TerminalESigned.eUnpaid
  ring

/-- Strict improvement comes from the actual original E endpoint slack. -/
theorem old_terminal_lt : Hf4Continue.terminal < terminal := by
  rw [terminal_balance]
  have hg := mul_nonneg (log_nonneg (by norm_num : (1:ℝ)≤2)) denominatorGain_nonneg
  linarith only [hg,original_eUnpaid_pos]

end Hf4Den
