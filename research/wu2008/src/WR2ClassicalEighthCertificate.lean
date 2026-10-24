import WR2ClassicalEighthRawCertificate
import WR2ClassicalEighthCorrectionCertificate
import Wu08TerminalAlignment
noncomputable section
namespace WuPaper.ClassicalEighth
theorem eighth_main_upper : Wu08TerminalAlignment.eighthMain ≤ (13199:ℝ)/2500 := by
  have hr := raw_upper
  have hc := ClassicalEighthCorrection.correction_lower
  unfold Wu08TerminalAlignment.eighthMain
  linarith only [hr,hc]
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.eighth_main_upper
