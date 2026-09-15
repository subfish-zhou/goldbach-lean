import CorrectionSigmaLogRemainders

noncomputable section
namespace CorrectionSigmaVariable
open Real Set MeasureTheory Wu2008DoubleSieve SharpLogRecurrence
open SigmaInnerEndpointRecovery OriginalSigmaStrength OriginalSigmaCubicRestoration
open F1FullRecoveryPayment
open scoped Interval

/-- The genuine unspent coefficient variation on the original sigma triangle. -/
def variation (t v : ℝ) : ℝ :=
  (SigmaJEndpoint.coefficient ((t+1)/(v-1))-beta t)*
    (upperLog ((t+1)/(v-1))-lowerLog ((t+1)/(v-1)))+
    F1LowerResidual.payment ((t+1)/(v-1))

def oldDensity (t v : ℝ) : ℝ :=
  ((1-beta t)*lowerLog ((t+1)/(v-1))+beta t*upperLog ((t+1)/(v-1)))/v

theorem argument_bounds {t v : ℝ} (ht : 1 ≤ t) (hv : v ∈ Icc 3 (t+2)) :
    1 ≤ (t+1)/(v-1) ∧ (t+1)/(v-1) ≤ (t+1)/2 := by
  have hv1 : 0<v-1 := by linarith [hv.1]
  constructor
  · exact (one_le_div hv1).mpr (by linarith [hv.2])
  · apply (div_le_div_iff₀ hv1 (by norm_num : (0:ℝ)<2)).mpr
    nlinarith [hv.1]

theorem variation_nonneg {t v : ℝ} (ht : 1 ≤ t) (hv : v ∈ Icc 3 (t+2)) :
    0 ≤ variation t v := by
  obtain ⟨hx,hxB⟩ := argument_bounds ht hv
  have hc := SigmaJEndpoint.coefficient_antitone hx hxB
  have hg : 0 ≤ upperLog ((t+1)/(v-1))-lowerLog ((t+1)/(v-1)) :=
    (log_lower hx).trans (log_upper hx) |> sub_nonneg.mpr
  have hp : 0 ≤ F1LowerResidual.payment ((t+1)/(v-1)) := by
    unfold F1LowerResidual.payment F1LowerResidual.denom
    positivity
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hc) hg) hp

theorem density_balance (t v : ℝ) :
    RemainingHf.basicLower ((t+1)/(v-1))/v=oldDensity t v+variation t v/v := by
  unfold RemainingHf.basicLower lowerGapPayment oldDensity variation SigmaJEndpoint.coefficient
  ring

/-- No new log envelope, order or cut: this consumes the actual unused original payment. -/
theorem strengthened_density_le {t v : ℝ} (ht : 1 ≤ t) (hv : v ∈ Icc 3 (t+2)) :
    oldDensity t v+variation t v/v ≤ log ((t+1)/(v-1))/v := by
  rw [← density_balance]
  exact div_le_div_of_nonneg_right (RemainingHf.basicLower_le (argument_bounds ht hv).1)
    (by linarith [hv.1])

end CorrectionSigmaVariable
