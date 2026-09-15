import Wu04MainPayment

namespace Wu04MainConsumer
open Wu2008DoubleSieve ActualNineFeedback NodeExtension SecondFunctionalParameters
open Wu08OriginalPsiRecovery Wu04MainPayment Wu04MainProducer
noncomputable section

theorem first_classical : (239103:ℝ)/1000000 ≤ classicalNumerator row1 :=
  classical_rational.trans classical_payment

theorem first_cost : coupledCostMass row1 ≤ (80370:ℝ)/1000000 :=
  first_complete_cost.trans (first_rational_cap.trans cost_rational)

/-- Joint actual payment from the two new FTC integrals and all seven main triple costs. -/
theorem first_joint_paid : (78363:ℝ)/1000000 ≤ classicalNumerator row1-2*coupledCostMass row1 := by
  have hb := first_classical
  have hc := first_cost
  linarith only [hb,hc]

/-- A real payment in the exact parent-requested slack, not a nonnegativity placeholder. -/
theorem first_parent_slack_paid : (303:ℝ)/62500 ≤
    (classicalNumerator row1-235359/1000000)+2*(80922/1000000-coupledCostMass row1) := by
  have h := first_joint_paid
  linarith only [h]

theorem first_actual {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    (239103:ℝ)/5000000-2*(80370/1000000)/(5*(1-2*δ))+
      coupledFeedback row1 (actualNine δ) ≤ wuImprovementLimit true δ row1.s := by
  have h := original_logs_actual_lower (coupledRow_geometry 0) hd hh
  change classicalNumerator row1/5-2*coupledCostMass row1/(5*(1-2*δ))+
    coupledFeedback row1 (actualNine δ) ≤ wuImprovementLimit true δ row1.s at h
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left first_cost (by norm_num : (0:ℝ)≤2))
    (show 0≤5*(1-2*δ) by linarith)
  have hb := first_classical
  linarith only [h,hc,hb]

/-- The full exact certificates also feed the original positive-delta source. -/
theorem first_actual_exact {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    classicalPaid/5-2*rationalCap/(5*(1-2*δ))+
      coupledFeedback row1 (actualNine δ) ≤ wuImprovementLimit true δ row1.s := by
  have h := Wu04MainProducer.first_actual_unrounded hd hh
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left first_rational_cap (by norm_num : (0:ℝ)≤2))
    (show 0≤5*(1-2*δ) by linarith)
  have hb := classical_payment
  linarith only [h,hc,hb]

/-- The remaining certificate gap is stated honestly. This is not an upper bound on actual Psi. -/
theorem residual_identity :
    classicalNumerator row1-2*coupledCostMass row1-5*(15826357:ℝ)/1000000000 =
    (classicalNumerator row1-239103/1000000)+
      2*(80370/1000000-coupledCostMass row1)-153757/200000000 := by ring

theorem remaining_slacks_nonnegative :
    0≤classicalNumerator row1-239103/1000000 ∧ 0≤80370/1000000-coupledCostMass row1 :=
  ⟨sub_nonneg.mpr first_classical,sub_nonneg.mpr first_cost⟩

#print axioms first_joint_paid
#print axioms first_parent_slack_paid
#print axioms first_actual
#print axioms first_actual_exact
#print axioms residual_identity
end
end Wu04MainConsumer
