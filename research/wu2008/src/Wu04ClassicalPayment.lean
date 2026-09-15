import Wu04ClassicalTelescope

namespace Wu04ClassicalPayment
open Wu2008DoubleSieve Real SecondFunctionalParameters SharpLogRecurrence JointLogTotalComparison
open Wu04ClassicalTelescope Wu04FullPsiLower
noncomputable section

def lowerCertificate : ℝ := Wu04ClassicalTelescope.rationalPart +
  (4-ds)*lowerLog (6/5) + (6-ds-dk)*lowerLog (17/16) +
  (17/3-ds-dk)*lowerLog (190/153) + (23/3-ds-dk)*lowerLog (20/19) +
  (1/3-ds-dk)*V (253/200) + (1/3-ds)*V (254/253) -
  ds*V (177/127) - V (10/9)

def upperCertificate : ℝ := Wu04ClassicalTelescope.rationalPart +
  (4-ds)*V (6/5) + (6-ds-dk)*V (17/16) +
  (17/3-ds-dk)*V (190/153) + (23/3-ds-dk)*V (20/19) +
  (1/3-ds-dk)*lowerLog (253/200) + (1/3-ds)*lowerLog (254/253) -
  ds*lowerLog (177/127) - lowerLog (10/9)

theorem endpoint_payments : lowerCertificate ≤ collected ∧ collected ≤ upperCertificate := by
  have h1 := And.intro (log_lower (by norm_num : (1:ℝ)≤6/5)) (log_le_V (by norm_num : (1:ℝ)≤6/5))
  have h2 := And.intro (log_lower (by norm_num : (1:ℝ)≤17/16)) (log_le_V (by norm_num : (1:ℝ)≤17/16))
  have h3 := And.intro (log_lower (by norm_num : (1:ℝ)≤190/153)) (log_le_V (by norm_num : (1:ℝ)≤190/153))
  have h4 := And.intro (log_lower (by norm_num : (1:ℝ)≤20/19)) (log_le_V (by norm_num : (1:ℝ)≤20/19))
  have h5 := And.intro (log_lower (by norm_num : (1:ℝ)≤253/200)) (log_le_V (by norm_num : (1:ℝ)≤253/200))
  have h6 := And.intro (log_lower (by norm_num : (1:ℝ)≤254/253)) (log_le_V (by norm_num : (1:ℝ)≤254/253))
  have h7 := And.intro (log_lower (by norm_num : (1:ℝ)≤177/127)) (log_le_V (by norm_num : (1:ℝ)≤177/127))
  have h8 := And.intro (log_lower (by norm_num : (1:ℝ)≤10/9)) (log_le_V (by norm_num : (1:ℝ)≤10/9))
  unfold lowerCertificate upperCertificate collected
  norm_num only [ds,dk,Wu04FullPsiSharp.d,row1]
  constructor
  · linarith only [h1.1,h2.1,h3.1,h4.1,h5.2,h6.2,h7.2,h8.2]
  · linarith only [h1.2,h2.2,h3.2,h4.2,h5.1,h6.1,h7.1,h8.1]

theorem rational_bracket :
    (235359:ℝ)/1000000 ≤ lowerCertificate ∧ upperCertificate ≤ (235478:ℝ)/1000000 := by
  norm_num [lowerCertificate,upperCertificate,Wu04ClassicalTelescope.rationalPart,ds,dk,Wu04FullPsiSharp.d,row1,
    lowerLog,upperLog,V]

/-- Brackets the entire inherited analytic lower function, not the actual B from above. -/
theorem first_lower_function_bracket :
    (235359:ℝ)/1000000 ≤ classicalLower row1 ∧
    classicalLower row1 ≤ (235478:ℝ)/1000000 := by
  rw [first_classical_telescope]
  exact ⟨rational_bracket.1.trans endpoint_payments.1,
    endpoint_payments.2.trans rational_bracket.2⟩

/-- Full B: both actual J integrals and all three signed L integrals are retained. -/
theorem first_classical_stronger : (235359:ℝ)/1000000 ≤
    Wu08OriginalPsiRecovery.classicalNumerator row1 :=
  first_lower_function_bracket.1.trans (four_classical_lower 0)

/-- No further endpoint-only precision can make THIS inherited analytic lower function
pay the sufficient target while C remains at the inherited 80922 cap. Not an actual-Psi obstruction. -/
theorem endpoint_only_strategy_residual :
    (5*(15826357:ℝ)/1000000000+2*(80922/1000000))-classicalLower row1 ≥
      (1099557:ℝ)/200000000 := by
  have h := first_lower_function_bracket.2
  linarith only [h]

#print axioms endpoint_payments
#print axioms rational_bracket
#print axioms first_classical_stronger
#print axioms endpoint_only_strategy_residual
end
end Wu04ClassicalPayment
