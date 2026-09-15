import W14FifthGainV3
import Wu08FourMotherTerminal

noncomputable section
open Real Wu2008DoubleSieve
open SharpMassBalance FifthLogTotalMagnitude

namespace WuTarget.W14

def secondLower : ℝ := 8*lo (103/25)

def fifthQuadratic : ℝ := 2*f0/a+4*slope*b/a^2

def fifthLinear : ℝ := 4*slope*(b-a)/a^2

def fifthLower : ℝ := fifthQuadratic*dLower^2-fifthLinear*dUpper

def block : ℝ := Wu08TerminalAlignment.secondMain+Wu08TerminalAlignment.fifthMain+
  8*PositiveSecondPayment.secondGain+PositiveCoreResume.fifthGain

def exactLower : ℝ := secondLower+fifthLower+
  8*PositiveSecondPayment.secondGain+fifthGainLower

theorem second_lower_with_recurrence :
    secondLower+8*Wu08OriginalFirstSteps.C (103/25) ≤ Wu08TerminalAlignment.secondMain := by
  have h := (endpoint_logs (by norm_num : (3 : ℝ) ≤ 103/25)).1
  norm_num only [show (103/25 : ℝ)-1=78/25 by norm_num] at h
  rw [Wu08TerminalAlignment.second_exact]
  unfold secondLower
  linarith only [h]

theorem fifth_payment_signs :
    0 ≤ fifthQuadratic ∧ 0 ≤ fifthLinear ∧ 0 ≤ dLower := by
  norm_num [fifthQuadratic, fifthLinear, f0, slope, lo, dLower,
    FifthClassicalShape.q, SharpLogRecurrence.lowerLog, s0, a, b,
    truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem fifth_lower : fifthLower ≤ Wu08TerminalAlignment.fifthMain := by
  have hl := log_ratio_bounds
  have hs := fifth_payment_signs
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.2.2 hl.1 2) hs.1
  have hn := mul_le_mul_of_nonneg_left hl.2 hs.2.1
  have he : endpoint (f0/a) (slope/a^2) =
      fifthQuadratic*(log b-log a)^2-fifthLinear*(log b-log a) := by
    unfold endpoint fifthQuadratic fifthLinear
    ring
  have hi := integral_bounds.1
  rw [he] at hi
  have hd := FifthActualIntegralRecovery.integral_distance.1
  unfold fifthLower Wu08TerminalAlignment.fifthMain
  linarith only [hp, hn, hi, hd]

theorem block_lower_retained :
    secondLower+fifthLower+8*PositiveSecondPayment.secondGain+
      PositiveCoreResume.fifthGain+8*Wu08OriginalFirstSteps.C (103/25) ≤ block := by
  unfold block
  linarith only [second_lower_with_recurrence, fifth_lower]

theorem block_lower : exactLower ≤ block := by
  have hc := Wu08OriginalFirstSteps.C_nonneg (by norm_num : (4 : ℝ) ≤ 103/25)
  unfold exactLower
  linarith only [block_lower_retained, fifth_gain_lower, hc]

theorem second_lower_exact : secondLower = 2397094349/263424000 := by
  norm_num [secondLower, lo, SharpLogRecurrence.lowerLog]

theorem fifth_lower_exact : fifthLower =
    434461939561019874125799419294056644337159802853296197124/
      268438702578293960879080582261444586162642656112408018625 := by
  norm_num [fifthLower, fifthQuadratic, fifthLinear, f0, slope, lo, dLower, dUpper,
    FifthClassicalShape.q, JointLogTotalComparison.V,
    SharpLogRecurrence.lowerLog, SharpLogRecurrence.upperLog, s0, a, b,
    truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem second_gain_exact : 8*PositiveSecondPayment.secondGain = 12167/41015625 := by
  norm_num [PositiveSecondPayment.secondGain]

theorem exact_lower_value : exactLower =
    122180445556278729807321768301500737169323609401420476174742971323611/
      11398981066284674754769277845149982906810457749157294102892000000000 := by
  rw [exactLower, second_lower_exact, fifth_lower_exact, second_gain_exact,
    fifth_gain_lower_exact]
  norm_num

theorem exact_lower_gt : (535927/50000 : ℝ) < exactLower := by
  rw [exact_lower_value]
  norm_num

theorem block_gt : (535927/50000 : ℝ) <
    Wu08TerminalAlignment.secondMain+Wu08TerminalAlignment.fifthMain+
      8*PositiveSecondPayment.secondGain+PositiveCoreResume.fifthGain :=
  exact_lower_gt.trans_le block_lower

theorem normalized_block_gt : (535927/200000 : ℝ) < block/4 := by
  have h := block_gt
  change (535927/50000 : ℝ) < block at h
  linarith only [h]

end WuTarget.W14
