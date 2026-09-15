import Wu04ClassicalPayment

namespace Wu04StrongPsiConsumer
open Wu2008DoubleSieve ActualNineFeedback NodeExtension
open SecondFunctionalParameters Wu08OriginalPsiRecovery
open Wu04ClassicalPayment Wu04FullPsiCostCertificate Wu04FullPsiMass
noncomputable section

/-- The stronger classical payment and the COMPLETE inherited main/tail costs in one formula. -/
theorem first_full_stronger : (14703:ℝ)/200000 ≤
    classicalNumerator row1-2*coupledCostMass row1 := by
  have hb := first_classical_stronger
  have hc := first_cost_rational
  linarith only [hb,hc]

/-- Actual positive-delta consumer: Gamma9, six lower triples, all four-prime terms,
both legal high histories, and all nine feedback coordinates are unchanged. -/
theorem first_actual_stronger {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/10) :
    (235359:ℝ)/5000000-2*(80922/1000000)/(5*(1-2*δ))+
      coupledFeedback row1 (actualNine δ) ≤ wuImprovementLimit true δ row1.s := by
  have h := original_logs_actual_lower (coupledRow_geometry 0) hd hh
  change classicalNumerator row1/5-2*coupledCostMass row1/(5*(1-2*δ))+
    coupledFeedback row1 (actualNine δ) ≤ wuImprovementLimit true δ row1.s at h
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left first_cost_rational (by norm_num : (0:ℝ)≤2))
    (show 0 ≤ 5*(1-2*δ) by linarith)
  have hb := first_classical_stronger
  linarith only [h,hc,hb]

/-- Unrounded analytic version also remains wired to the actual positive-delta source. -/
theorem first_actual_unrounded {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/10) :
    lowerCertificate/5-2*fullCostPolynomial row1/(5*(1-2*δ))+
      coupledFeedback row1 (actualNine δ) ≤ wuImprovementLimit true δ row1.s := by
  have h := Wu04FullPsiLower.four_actual_inputs 0 hd hh
  change Wu04FullPsiLower.classicalLower row1/5-
    2*fullCostPolynomial row1/(5*(1-2*δ))+
    coupledFeedback row1 (actualNine δ) ≤ wuImprovementLimit true δ row1.s at h
  have hb := endpoint_payments.1
  rw [← Wu04ClassicalTelescope.first_classical_telescope] at hb
  linarith only [h,hb]

/-- Exact gain against the accepted old complete certificate. -/
theorem exact_gain_and_residual :
    (14703:ℝ)/200000-52808/1000000 = 20707/1000000 ∧
    5*(15826357:ℝ)/1000000000-14703/200000 = 1123357/200000000 ∧
    0 < (1123357:ℝ)/200000000 := by norm_num

/-- Literal remaining target, not a claimed counterexample or a dropped sup cost. -/
theorem first_actual_residual_identity :
    classicalNumerator row1-2*coupledCostMass row1-5*(15826357:ℝ)/1000000000 =
    (classicalNumerator row1-235359/1000000)+
    2*(80922/1000000-coupledCostMass row1)-1123357/200000000 := by ring

theorem first_slacks_nonnegative :
    0 ≤ classicalNumerator row1-235359/1000000 ∧
    0 ≤ 80922/1000000-coupledCostMass row1 :=
  ⟨sub_nonneg.mpr first_classical_stronger,sub_nonneg.mpr first_cost_rational⟩

/-- This is only a sufficient replacement of the whole cost cap, not a necessary
condition on the actual target and not an unpaid hypothesis disguised as a producer. -/
theorem sufficient_full_cost_target
    (hc : coupledCostMass row1 ≤ (31245443:ℝ)/400000000) :
    5*(15826357:ℝ)/1000000000 ≤ classicalNumerator row1-2*coupledCostMass row1 := by
  have hb := first_classical_stronger
  linarith only [hb,hc]

#print axioms first_full_stronger
#print axioms first_actual_stronger
#print axioms first_actual_unrounded
#print axioms first_actual_residual_identity
#print axioms first_slacks_nonnegative
#print axioms sufficient_full_cost_target
end
end Wu04StrongPsiConsumer
