import Phase10LogBounds
import ParentPhase9HalfWeight

namespace Wu2008DoubleSieve.Phase10
open HighSixPhase9
noncomputable section

/-- The original first functional retains its literal outer factor one half. -/
theorem retained_log_first_functional {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    sourceP-penalty δ*envelopeE + amplitude δ*(289/5200) +
      (1/2)*(amplitude δ*L) ≤ amplitude δ := by
  have hf := wuImprovementLimit_firstFunctionalGain
    (s := (13/5 : ℝ)) (t := (179/50 : ℝ)) hδ (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hH := H_quadratic hδ hδhi (s := (179/50 : ℝ)) ⟨by norm_num,by norm_num⟩
  have hi := weighted_h_log_lower hδ hδhi
  have hp := psi_delta_raw hδ hδhi
  norm_num only at hf hH
  dsimp [amplitude] at *
  linarith only [hf,hH,hi,hp]

theorem amplitude_log_closed {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    (sourceP-penalty δ*envelopeE)/(1-rhoLog) ≤ amplitude δ := by
  apply (div_le_iff₀ (sub_pos.mpr rhoLog_bounds.2)).2
  have hr := retained_log_first_functional hδ hδhi
  unfold rhoLog
  linarith only [hr]

def gLog : ℝ := Cgeo*sourceP/(1-rhoLog)
def penaltyLog : ℝ := Cgeo*envelopeE/(1-rhoLog)

theorem gLog_pos : 0 < gLog := by
  apply div_pos (mul_pos Cgeo_pos (by norm_num [sourceP]))
    (sub_pos.mpr rhoLog_bounds.2)

theorem penaltyLog_pos : 0 < penaltyLog := by
  apply div_pos (mul_pos Cgeo_pos (by norm_num [envelopeE]))
    (sub_pos.mpr rhoLog_bounds.2)

/-- The full original delta penalty survives the logarithmic feedback closure. -/
theorem gain_log_with_penalty {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    gLog-penalty δ*penaltyLog ≤ SingleUpperHIntegral.gainH34 δ/4 := by
  have hi := (mul_le_mul_of_nonneg_left (amplitude_log_closed hδ hδhi) Cgeo_pos.le).trans
    (actual_low_H_amplitude_lower hδ hδhi)
  have he : gLog-penalty δ*penaltyLog =
      Cgeo*((sourceP-penalty δ*envelopeE)/(1-rhoLog)) := by
    unfold gLog penaltyLog
    ring
  rwa [he]

/-- A uniform linear bound is used only when selecting delta before the threshold. -/
theorem gain_log_linear_error {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    gLog-((100/49)*penaltyLog)*δ ≤ SingleUpperHIntegral.gainH34 δ/4 := by
  have hp := mul_le_mul_of_nonneg_right (ParentPhase9HalfWeight.penalty_le hδ hδhi)
    penaltyLog_pos.le
  have hi := gain_log_with_penalty hδ hδhi
  nlinarith only [hp,hi]

/-- The improvement is strict relative to the accepted half-weight constant. -/
theorem gLog_strict : ParentPhase9HalfWeight.gainConstant < gLog := by
  have hr : ParentPhase9HalfWeight.feedbackRho < rhoLog := by
    unfold ParentPhase9HalfWeight.feedbackRho rhoLog
    linarith only [L_strict]
  unfold ParentPhase9HalfWeight.gainConstant gLog
  exact div_lt_div_of_pos_left (mul_pos Cgeo_pos (by norm_num [sourceP]))
    (sub_pos.mpr rhoLog_bounds.2) (by linarith only [hr])

end
end Wu2008DoubleSieve.Phase10
