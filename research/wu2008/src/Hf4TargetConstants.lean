import Hf4FullProfile

noncomputable section
namespace Hf4Target
open Real

theorem original_threshold : NineFeedbackStrength.originalH 8 = (72943/10000000 : ℝ) := by
  change (0.0072943 : ℝ) = 72943/10000000
  norm_num

theorem radical_bounds : (3872983346207/1000000000000 : ℝ) < TerminalE.radical ∧
    TerminalE.radical < 3872983346208/1000000000000 := by
  have hp := TerminalE.radical_pos
  have hs := TerminalE.radical_sq
  constructor <;> nlinarith only [hp, hs]

theorem log_two_bounds : (6931/10000 : ℝ) < log 2 ∧ log 2 < 6932/10000 := by
  have hL := RemainingHf.splitLower_le (by norm_num : (1 : ℝ) ≤ 2)
  have hU := Wu2008DoubleSieve.HighSharedKernelMagnitude.log_two_refined.2
  norm_num [RemainingHf.splitLower, RemainingHf.basicLower,
    Wu04FactorEnvelopes.leftFactor, Wu04FactorEnvelopes.rightFactor,
    Wu2008DoubleSieve.SharpLogRecurrence.lowerLog,
    Wu2008DoubleSieve.SharpLogRecurrence.upperLog,
    F1FullRecoveryPayment.lowerGapPayment, F1LowerResidual.payment,
    F1LowerResidual.denom] at hL
  constructor <;> linarith only [hL,hU]

end Hf4Target
