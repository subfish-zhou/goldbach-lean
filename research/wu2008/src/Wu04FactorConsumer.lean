import Wu04FactorJPrimitive

namespace Wu04FactorConsumer
open Wu2008DoubleSieve Real SecondFunctionalParameters ActualNineFeedback NodeExtension
open Wu08OriginalPsiRecovery SharpLogRecurrence JointLogTotalComparison
noncomputable section

/-- Both original J intervals and both positively oriented L intervals use the fixed
one-factorization kernels. The kappa2<3 term retains its previously proved payment. -/
def classicalCertificate : ℝ :=
  Wu04FactorJPrimitive.lowerJ row1.s row1.S+
  Wu04FactorJPrimitive.lowerJ row1.kappa3 row1.kappa1-
  2*Wu04FactorLPrimitive.upperL row1.S-2*Wu04FactorLPrimitive.upperL row1.kappa1+
  2*lowerLog (20/19)-V (10/9)

theorem classical_lower : classicalCertificate≤classicalNumerator row1 := by
  have hj := Wu04FactorJPrimitive.actual_lower
    (by norm_num [row1] : 2<row1.s) (by norm_num [row1] : row1.s≤row1.S)
    (by norm_num [Wu04MainClassical.a,row1]) (by norm_num [Wu04MainClassical.a,row1])
  have hk := Wu04FactorJPrimitive.actual_lower
    (by norm_num [row1] : 2<row1.kappa3) (by norm_num [row1] : row1.kappa3≤row1.kappa1)
    (by norm_num [Wu04MainClassical.a,row1]) (by norm_num [Wu04MainClassical.a,row1])
  have hl := Wu04FactorLPrimitive.actual_upper (by norm_num [row1] : 3≤row1.S)
  have hm := Wu04FactorLPrimitive.actual_upper (by norm_num [row1] : 3≤row1.kappa1)
  have hn := (Wu04FullPsiClassical.l_small_upper (by norm_num [row1] : 2<row1.kappa2)
    (by norm_num [row1])).trans Wu04FullPsiLower.first_small_L_bound
  unfold classicalCertificate classicalNumerator
  linarith only [hj,hk,hl,hm,hn]

/-- Complete actual cost: Γ9 and six lower triples at the proved cap; every fourprime
and U20 retained, with the two true suprema bounded independently upstream. -/
theorem first_joint_exact :
    classicalCertificate-2*Wu04MainProducer.completeCap≤
      classicalNumerator row1-2*coupledCostMass row1 := by
  have hb := classical_lower
  have hc := Wu04MainProducer.first_complete_cost
  linarith only [hb,hc]

/-- Actual positive-delta source, not a delta-zero limit assumption.
This theorem does not assert the unresolved publication comparison. -/
theorem first_actual {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    classicalCertificate/5-2*Wu04MainProducer.completeCap/(5*(1-2*δ))+
      coupledFeedback row1 (actualNine δ)≤wuImprovementLimit true δ row1.s := by
  have h := Wu04MainProducer.first_actual_unrounded hd hh
  have hb := classical_lower
  linarith only [h,hb]

/-- All already-paid rational main costs can also be consumed without discarding
any of the original actual feedback or legal high terms. -/
theorem first_actual_rational_cost {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    classicalCertificate/5-2*Wu04MainProducer.rationalCap/(5*(1-2*δ))+
      coupledFeedback row1 (actualNine δ)≤wuImprovementLimit true δ row1.s := by
  have h := first_actual hd hh
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left Wu04MainProducer.first_rational_cap (by norm_num : (0:ℝ)≤2))
    (show 0≤5*(1-2*δ) by linarith)
  linarith only [h,hc]

end
end Wu04FactorConsumer
