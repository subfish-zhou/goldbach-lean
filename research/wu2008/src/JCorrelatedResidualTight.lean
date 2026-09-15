import JFourRemainingMagnitude

namespace Wu2008DoubleSieve.JCorrelatedResidualTight
open Real SharpLogRecurrence SharpJBalance JCubicPrimitive JCubicActualMass
open JFourRemainingMagnitude
noncomputable section

/-- The coefficient in the original complete L-envelope FTC. -/
def C (v : ℝ) : ℝ := 2*v+(2/3)*v^3
def R (v w l r : ℝ) : ℝ :=
  2*(v-w)*(1/(1-r)-1/(1-l))+(2/3)*(rationalPart v w r-rationalPart v w l)

/-- Collect the very same log-two occurrences before any endpoint payment. -/
def qTwo : ℝ := SignedTotalCorrelation.jTwo-16*C (1/3)-8*C (1-2*s)
def lowerRest : ℝ :=
  16*(C 1*(lowerLog ((1/3)/s)+lowerLog ((1-s)/(2/3)))+R 1 3 s (1/3))+
  8*(C (1/3)*lowerLog (crossRatio a (1/3)/4)+R (1/3) 1 a (1/3))+
  8*(C (1-2*s)*(lowerLog ((s/b)/2)+lowerLog ((1-b)/(1-s)))+R (1-2*s) 1 b s)

def twoUpper : ℝ := JointLogTotalComparison.V (4/3)+JointLogTotalComparison.V (3/2)

/-- This rational endpoint retains the full FTC rational parts and pays only
    after collecting signs. The previously earned recovery is charged once. -/
def cap : ℝ := UnroundedPayments.weightedJUpper-
  SignedTotalCorrelation.jTwo*upperLog 2-JointJLossStrength.fixedRecovery-
  lowerRest+qTwo*twoUpper

theorem cross_log {l r : ℝ} (hl : 0 < l) (hr : 0 < r)
    (hl1 : l < 1) (hr1 : r < 1) :
    log (crossRatio l r) = log (r/l)+log ((1-l)/(1-r)) := by
  have h1 : 1-l ≠ 0 := by linarith
  have h2 : 1-r ≠ 0 := by linarith
  dsimp [crossRatio]
  rw [log_div (mul_ne_zero hr.ne' h1) (mul_ne_zero hl.ne' h2),
    log_mul hr.ne' h1,log_mul hl.ne' h2,log_div hr.ne' hl.ne',log_div h1 h2]
  ring

theorem log_two_upper : log 2 ≤ twoUpper := by
  have h1 := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 4/3)
  have h2 := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 3/2)
  have he : log (2:ℝ) = log (4/3)+log (3/2) := by
    rw [← log_mul (by norm_num : (4/3:ℝ) ≠ 0) (by norm_num : (3/2:ℝ) ≠ 0)]
    norm_num
  rw [he]
  exact add_le_add h1 h2

/-- Original complete FTC lower endpoint with all three original multiplicities. -/
theorem collected_lower :
    lowerRest+(16*C (1/3)+8*C (1-2*s))*log 2 ≤ jLowerReal := by
  have hs0 : 0 < s := by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha]
  have hs1 : s < 1 := by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha]
  have hb0 : 0 < b := by norm_num [b,ninthProfileK2]
  have hb1 : b < 1 := by norm_num [b,ninthProfileK2]
  have h71 := log_lower (t := (1/3)/s)
    (by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha])
  have h72 := log_lower (t := (1-s)/(2/3))
    (by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha])
  have h8 := log_lower (t := crossRatio a (1/3)/4)
    (by norm_num [crossRatio,a,SeventhEighth.alpha])
  have h91 := log_lower (t := (s/b)/2)
    (by norm_num [s,b,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have h92 := log_lower (t := (1-b)/(1-s))
    (by norm_num [s,b,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  unfold jLowerReal fullMass
  rw [cross_log hs0 (by norm_num : (0:ℝ) < 1/3) hs1 (by norm_num),
    log_split_four (by norm_num [crossRatio,a,SeventhEighth.alpha] :
      0 < crossRatio a (1/3)),
    cross_log hb0 hs0 hb1 hs1,log_split_two (div_pos hs0 hb0)]
  norm_num [lowerRest,C,R,rationalPart,s,b,a,SeventhEighth.sigma,
    SeventhEighth.alpha,ninthProfileK2,lowerLog,crossRatio] at h71 h72 h8 h91 h92 ⊢
  linarith only [h71,h72,h8,h91,h92]

theorem qTwo_positive : 0 < qTwo := by
  norm_num [qTwo,C,SignedTotalCorrelation.jTwo,ninthA,s,SeventhEighth.sigma,SeventhEighth.alpha]

/-- No correlation or ninth recovery is discarded or subtracted twice. -/
theorem complete_real_cap_le : jCapReal ≤ cap := by
  have hl := collected_lower
  have hr := JointJLossStrength.fixedRecovery_le_recovery
  have h2 := mul_le_mul_of_nonneg_left log_two_upper qTwo_positive.le
  unfold cap jCapReal SignedTotalCorrelation.d2 SignedTotalCorrelation.e2 qTwo at *
  linarith only [hl,hr,h2]

/-- A real upper bound on the actual original J loss, not a target hypothesis. -/
theorem actual_remaining_interval : 0 ≤ jRemaining ∧ jRemaining ≤ cap :=
  ⟨j_remaining_real_interval.1,j_remaining_real_interval.2.trans complete_real_cap_le⟩

theorem cap_size : cap < (3037/100000:ℝ) := by
  norm_num [cap,lowerRest,qTwo,C,R,twoUpper,JointLogTotalComparison.V,
    UnroundedPayments.weightedJUpper,UnroundedPayments.j7Upper,UnroundedPayments.j8Upper,
    UnroundedPayments.j9Upper,SignedTotalCorrelation.jTwo,ninthA,
    JointJLossStrength.fixedRecovery,JointJLossStrength.massPayment,
    rationalPart,crossRatio,upperLog,lowerLog,s,b,a,
    SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2]

theorem actual_remaining_magnitude :
    0 ≤ AnalyticTotalThreshold.jLoss-JointJLossStrength.recovery ∧
    AnalyticTotalThreshold.jLoss-JointJLossStrength.recovery < 3037/100000 :=
  ⟨actual_remaining_interval.1,actual_remaining_interval.2.trans_lt cap_size⟩

/-- The actual J lower endpoint is retained, not replaced by a positivity claim. -/
theorem actual_J_lower :
    lowerRest+(16*C (1/3)+8*C (1-2*s))*log 2 ≤ actualJ :=
  collected_lower.trans complete_j_lower

/-- Direct quarter-weight consumer for the parent's original seven-error ledger. -/
theorem mother_J_error_interval :
    0 ≤ (AnalyticTotalThreshold.jLoss-JointJLossStrength.recovery)/4 ∧
    (AnalyticTotalThreshold.jLoss-JointJLossStrength.recovery)/4 < 3037/400000 := by
  have h := actual_remaining_magnitude
  constructor <;> linarith only [h.1,h.2]

end
end Wu2008DoubleSieve.JCorrelatedResidualTight
