import Wu04CurveCost

namespace Wu04CurvePaid
open Wu2008DoubleSieve SecondFunctionalParameters
open ActualNineFeedback NodeExtension Wu08OriginalPsiRecovery
open SharpLogRecurrence JointLogTotalComparison Wu04CurveCost
noncomputable section

/-- The original first-row publication target. -/
def publication : ℝ := 15826357/1000000000

/-- This slack is defined by the full paid cost, not by a numerical oracle. -/
def slack : ℝ := 239555/1000000-2*costCap-5*publication

/-- Exact rational identity checked by Lean after all fixed envelopes are expanded. -/
theorem slack_exact : slack =
    (30025778365423505329324936643900717340958341359093729258724467702577878026766591836228366841431231451593064769568589830338701838060871728561477295446144931001 : ℝ)/
    4985821164989758721571953693053034043771248064928523375293595597887523258406365538762575643822890983180999496071171584192607345877708459025759187569941356800000000 := by
  rw [slack,costCap,Wu04CurveMass.gain_exact]
  norm_num [publication,Wu04RecoverComplete.costCap,Wu04RecoverCost.costCap,Wu04ThreeCost.costCap,
    Wu04RecoverRectangle.gain,Wu04RecoverRectangle.massLower,
    Wu04RecoverRectangle.a,Wu04RecoverRectangle.b,Wu04RecoverRectangle.c,
    Wu04RecoverRectangle.f,Wu04RecoverRectangle.r,
    Wu04RecoverGammaMass.gain,Wu04RecoverGammaMass.massLower,
    Wu04RecoverGamma.d,Wu04RecoverGamma.lo,Wu04RecoverGamma.hi,Wu04RecoverGamma.r,
    Wu04WholeCostPaid.costCap,Wu04WholeCostPaid.tripleCap,Wu04WholeCostPaid.fourCap,
    Wu04WholeCostPaid.lx,Wu04WholeCostPaid.ux,Wu04WholeCostPaid.ly,Wu04WholeCostPaid.uy,
    Wu04WholeCostPaid.lz,Wu04WholeCostPaid.uz,Wu04WholeCostPaid.lw,Wu04WholeCostPaid.uw,
    Wu04ThreeMass.gain,Wu04ThreeMass.massLower,Wu04MainTail.cap,Wu04ThreeTail.cap,row1,
    Wu04FactorEnvelopes.lower,Wu04FactorEnvelopes.upper,
    Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,V,lowerLog,upperLog]

theorem slack_pos : 0<slack := by rw [slack_exact]; norm_num

/-- Literal B minus twice the complete cost: the full first-row target is paid. -/
theorem publication_budget_with_slack : 5*publication+slack ≤
    classicalNumerator row1-2*coupledCostMass row1 := by
  have hb := Wu04WholeReversePaid.first_classical
  have hc := complete_cost_paid
  unfold slack
  linarith only [hb,hc]

theorem publication_budget : 5*((15826357 : ℝ)/1000000000) ≤
    classicalNumerator row1-2*coupledCostMass row1 := by
  have h := publication_budget_with_slack
  change 5*publication≤_
  linarith only [h,slack_pos]

/-- The genuine positive-delta debit is retained, including its denominator. -/
def deltaDebit (δ : ℝ) : ℝ := 4*δ*costCap/(5*(1-2*δ))

theorem actual_with_slack {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    publication+slack/5-deltaDebit δ+coupledFeedback row1 (actualNine δ) ≤
      wuImprovementLimit true δ row1.s := by
  have h := original_logs_actual_lower (coupledRow_geometry 0) hd hh
  change classicalNumerator row1/5-2*coupledCostMass row1/(5*(1-2*δ))+
    coupledFeedback row1 (actualNine δ)≤wuImprovementLimit true δ row1.s at h
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left complete_cost_paid (by norm_num : (0:ℝ)≤2))
    (show 0≤5*(1-2*δ) by linarith)
  have hb := Wu04WholeReversePaid.first_classical
  have he : publication+slack/5-deltaDebit δ =
      (239555:ℝ)/5000000-2*costCap/(5*(1-2*δ)) := by
    unfold slack deltaDebit
    have hn : 1-2*δ ≠ 0 := by linarith
    field_simp
    ring
  rw [he]
  linarith only [h,hc,hb]

/-- Actual strong first row for every permitted positive delta, with the necessary debit. -/
theorem actual_publication {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    (15826357:ℝ)/1000000000-deltaDebit δ+coupledFeedback row1 (actualNine δ) ≤
      wuImprovementLimit true δ row1.s := by
  have h := actual_with_slack hd hh
  change publication-deltaDebit δ+coupledFeedback row1 (actualNine δ)≤_
  linarith only [h,slack_pos]

end
end Wu04CurvePaid
