import D0FullPaid

noncomputable section
namespace D0FullDensity
open Real Set MeasureTheory NodeExtension ActualNineFeedback FirstFeedbackIntegrals
open scoped Interval

/-- The original unspent density is retained on the whole original interval. -/
def densityUnpaid : ℝ := ∫ v in (3:ℝ)..5,
  (log (4/(v-1))-RemainingHf.splitLower (4/(v-1)))/v

theorem densityUnpaid_eq : densityUnpaid=D0-fullMass := by
  have hi : IntervalIntegrable (fun v : ℝ => log (4/(v-1))/v) volume 3 5 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := by norm_num)
    intro v hv
    have hv0 : 0<v := by linarith [hv.1]
    have hv1 : 0<v-1 := by linarith [hv.1]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  rw [← density_integral]
  change densityUnpaid=(∫ v in (3:ℝ)..5, log (4/(v-1))/v)-(∫ v in (3:ℝ)..5,density v)
  rw [← intervalIntegral.integral_sub hi density_continuous.intervalIntegrable]
  unfold densityUnpaid density
  apply intervalIntegral.integral_congr
  intro v _
  ring

theorem densityUnpaid_nonneg : 0≤densityUnpaid := by
  rw [densityUnpaid_eq]
  exact sub_nonneg.mpr fullMass_le_D0

def endpointUnpaid : ℝ := fullMass-fullPaid

theorem endpointUnpaid_nonneg : 0≤endpointUnpaid := sub_nonneg.mpr fullPaid_le

theorem original_D0_balance : D0=fullPaid+endpointUnpaid+densityUnpaid := by
  rw [densityUnpaid_eq]
  unfold endpointUnpaid
  ring

theorem finiteD_le_dPaid : finiteD≤dPaid := max_le_max le_rfl fullPaid_le

theorem finiteProfile_le_full : finiteProfile≤profileLower :=
  div_le_div_of_nonneg_left paidNumerator_pos.le (sub_pos.mpr dPaid_lt_one)
    (by linarith only [finiteD_le_dPaid])

theorem finiteTerminal_le_full : finiteTerminal≤terminalLower := by
  unfold finiteTerminal terminalLower terminalAt
  exact add_le_add (mul_le_mul_of_nonneg_left finiteProfile_le_full
    SignedSigmaETerminal.logPayment_nonneg) le_rfl

/-- Keep the actual logarithm, full D0 primitive and already proved full E mass. -/
def retainedTerminal : ℝ := log 2*profileLower+TerminalECells.mass NineFeedbackStrength.originalH

theorem retainedTerminal_le_actual : retainedTerminal≤firstFeedback NineFeedbackStrength.originalH 3 3 := by
  have hs := mul_le_mul_of_nonneg_left profileLower_le (log_nonneg (by norm_num : (1:ℝ)≤2))
  have he := TerminalECells.mass_le CoupledIntegralRecovery.originalH_nonneg
  unfold retainedTerminal
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  linarith only [hs,he]

def profileLogUnpaid : ℝ := (log 2-RemainingHf.splitLower 2)*profileLower

theorem profileLogUnpaid_nonneg : 0≤profileLogUnpaid :=
  mul_nonneg (sub_nonneg.mpr (RemainingHf.splitLower_le (by norm_num : (1:ℝ)≤2))) profileLower_pos.le

theorem retainedTerminal_balance : retainedTerminal=terminalLower+profileLogUnpaid+TerminalESigned.eUnpaid := by
  unfold retainedTerminal terminalLower terminalAt profileLogUnpaid TerminalESigned.eUnpaid profileLower
  ring

theorem finiteTerminal_le_retained : finiteTerminal≤retainedTerminal := by
  rw [retainedTerminal_balance]
  linarith only [finiteTerminal_le_full,profileLogUnpaid_nonneg,TerminalESigned.eUnpaid_nonneg]

end D0FullDensity
