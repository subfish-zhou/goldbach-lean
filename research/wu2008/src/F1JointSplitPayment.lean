import F1JointCommonLogs

namespace F1JointSplit
open Real Wu2008DoubleSieve SharpLogRecurrence FirstCRationalPayment
open F1JointFTC F1UnpaidRecovery F1RemainingRecovery F1SecondLogRecovery
noncomputable section

def splitLow (x : ℝ) : ℝ := F1JointFTC.low ((1+x)/2)+F1JointFTC.low (2*x/(1+x))
def splitHigh (x : ℝ) : ℝ := F1JointFTC.high ((1+x)/2)+F1JointFTC.high (2*x/(1+x))

theorem splitLow_le {x : ℝ} (hx : 1 ≤ x) : splitLow x ≤ log x := by
  rw [FirstIntegralRecovery.split_log_identity hx]
  exact add_le_add (low_le_log (FirstIntegralRecovery.split_arguments hx).1)
    (low_le_log (FirstIntegralRecovery.split_arguments hx).2)

theorem le_splitHigh {x : ℝ} (hx : 1 ≤ x) : log x ≤ splitHigh x := by
  rw [FirstIntegralRecovery.split_log_identity hx]
  exact add_le_add (log_le_high (FirstIntegralRecovery.split_arguments hx).1)
    (log_le_high (FirstIntegralRecovery.split_arguments hx).2)

def paid (c x : ℝ) : ℝ := if 0 ≤ c then c*splitLow x else c*splitHigh x

theorem paid_le (c : ℝ) {x : ℝ} (hx : 1 ≤ x) : paid c x ≤ c*log x := by
  by_cases hc : 0 ≤ c
  · simpa [paid,hc] using mul_le_mul_of_nonneg_left (splitLow_le hx) hc
  · simpa [paid,hc] using mul_le_mul_of_nonpos_left (le_splitHigh hx) (le_of_not_ge hc)

def twoUpper : ℝ := min (JointLogTotalComparison.V 2-upperTwoPayment) (splitHigh 2)

theorem log_two_le : log 2 ≤ twoUpper := by
  unfold twoUpper
  exact le_min (by linarith only [upperTwoPayment_le]) (le_splitHigh (by norm_num))

def jointLower : ℝ :=
  (1+residueB)*twoUpper+paid (1+residueB) (3/2)+paid 1 (1127/600)+
  paid commonA (3884129/3606400)+paid commonAC (4508/2927)+
  paid (-residueB) (2400/2381)+paid residueD (4508/3981)+rationalEndpointPart+
  (1+secondFactorRatio)*(paid partA (927/400)+paid partB (2254/1727)+
    paid (partF/2) quadraticRatio+paid ((partG-8*partF)/(2*root)) radicalRatio+F1JointFTC.rationalPart)+
  secondPayment+EJoint.payment

theorem jointLower_le_mass : jointLower ≤ F1JointFTC.jointMass := by
  have h0 := mul_le_mul_of_nonpos_left log_two_le residue_signs.2.2.2.1
  have h1 := paid_le (1+residueB) (by norm_num : (1:ℝ) ≤ 3/2)
  have h2 := paid_le 1 (by norm_num : (1:ℝ) ≤ 1127/600)
  have h3 := paid_le commonA (by norm_num : (1:ℝ) ≤ 3884129/3606400)
  have h4 := paid_le commonAC (by norm_num : (1:ℝ) ≤ 4508/2927)
  have h5 := paid_le (-residueB) (by norm_num : (1:ℝ) ≤ 2400/2381)
  have h6 := paid_le residueD (by norm_num : (1:ℝ) ≤ 4508/3981)
  have h7 := paid_le partA (by norm_num : (1:ℝ) ≤ 927/400)
  have h8 := paid_le partB (by norm_num : (1:ℝ) ≤ 2254/1727)
  have h9 := paid_le (partF/2) (by norm_num [quadraticRatio] : 1 ≤ quadraticRatio)
  have h10 := paid_le ((partG-8*partF)/(2*root)) radicalRatio_ge_one
  have hi := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add h7 h8) h9) h10)
    (show 0 ≤ 1+secondFactorRatio by linarith only [secondFactorRatio_pos])
  unfold jointLower F1JointFTC.jointMass
  linarith only [h0,h1,h2,h3,h4,h5,h6,hi]

theorem jointLower_le_actual : 8*jointLower ≤ Wu08TerminalAlignment.firstMain := by
  linarith only [jointLower_le_mass,jointMass_le_actual]

end
end F1JointSplit
