import Wu04WholeReversePaid

namespace Wu04WholeCostPaid
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
open SecondFunctionalParameters Wu04FullPsiMass Wu04FactorEnvelopes
open ActualNineFeedback NodeExtension Wu08OriginalPsiRecovery
noncomputable section

def lx : ℝ := lower (454/353)
def ux : ℝ := upper (454/353)
def ly : ℝ := lower (353/290)
def uy : ℝ := upper (353/290)
def lz : ℝ := lower (145/122)
def uz : ℝ := upper (145/122)
def lw : ℝ := lower (61/55)
def uw : ℝ := upper (61/55)

theorem first_log_bounds :
    lx≤x row1 ∧ x row1≤ux ∧ ly≤y row1 ∧ y row1≤uy ∧
    lz≤z row1 ∧ z row1≤uz ∧ lw≤w row1 ∧ w row1≤uw := by
  have hx := And.intro (lower_le_log (by norm_num : (1:ℝ)≤454/353)) (log_le_upper (by norm_num : (1:ℝ)≤454/353))
  have hy := And.intro (lower_le_log (by norm_num : (1:ℝ)≤353/290)) (log_le_upper (by norm_num : (1:ℝ)≤353/290))
  have hz := And.intro (lower_le_log (by norm_num : (1:ℝ)≤145/122)) (log_le_upper (by norm_num : (1:ℝ)≤145/122))
  have hw := And.intro (lower_le_log (by norm_num : (1:ℝ)≤61/55)) (log_le_upper (by norm_num : (1:ℝ)≤61/55))
  norm_num [x,y,z,w,row1] at *
  exact ⟨hx.1,hx.2,hy.1,hy.2,hz.1,hz.2,hw.1,hw.2⟩

def tripleCap : ℝ :=
  (353/100-290/100+2*(244/100))*uy+
  (2*(353/100)-290/100+244/100)*uz+(454/100-290/100)*uw-
  (244/100)*ly*lw+(353/100)*ux*uz+(220/100-290/100)*lx-2*(353/100-244/100)

def fourCap : ℝ :=
  (290/100+2*(244/100))*uz+(290/100-244/100)*uw-
  (244/100)*lz*lw+(220/100/2)*uz^2-3*(290/100-244/100)+
  (244/100+220/100)*uy*uw-2*(244/100-220/100)*ly

def costCap : ℝ := Wu04MainTail.cap*tripleCap+fourCap+207/8318750

theorem polynomials_bounded : triplePolynomial row1≤tripleCap ∧ fourPolynomial row1≤fourCap := by
  obtain ⟨hxL,hxU,hyL,hyU,hzL,hzU,hwL,hwU⟩ := first_log_bounds
  have hlx : 0≤lx := by norm_num [lx,lower,leftFactor,rightFactor,lowerLog]
  have hly : 0≤ly := by norm_num [ly,lower,leftFactor,rightFactor,lowerLog]
  have hlz : 0≤lz := by norm_num [lz,lower,leftFactor,rightFactor,lowerLog]
  have hlw : 0≤lw := by norm_num [lw,lower,leftFactor,rightFactor,lowerLog]
  have hux : 0≤ux := hlx.trans (hxL.trans hxU)
  have huy : 0≤uy := hly.trans (hyL.trans hyU)
  have hdyw := mul_le_mul hyL hwL hlw (hly.trans hyL)
  have hdxz := mul_le_mul hxU hzU (hlz.trans hzL) hux
  have hdzw := mul_le_mul hzL hwL hlw (hlz.trans hzL)
  have hdywU := mul_le_mul hyU hwU (hlw.trans hwL) huy
  have hdz2 := pow_le_pow_left₀ (hlz.trans hzL) hzU 2
  constructor
  · unfold triplePolynomial tripleCap
    norm_num only [row1] at *
    nlinarith only [hxL,hyU,hzU,hwU,hdyw,hdxz]
  · unfold fourPolynomial fourCap
    norm_num only [row1] at *
    nlinarith only [hyL,hzU,hwU,hdzw,hdywU,hdz2]

theorem complete_cap_paid : Wu04MainProducer.completeCap≤costCap := by
  have ht := mul_le_mul_of_nonneg_left polynomials_bounded.1
    (by norm_num [Wu04MainTail.cap] : 0≤Wu04MainTail.cap)
  have hf := polynomials_bounded.2
  have hu := Wu04CoupledCostProducer.first_U20_rational
  unfold Wu04MainProducer.completeCap costCap
  linarith only [ht,hf,hu]

theorem actual_cost_paid : coupledCostMass row1≤costCap :=
  Wu04MainProducer.first_complete_cost.trans complete_cap_paid

theorem cost_rational : costCap≤(80362:ℝ)/1000000 := by
  norm_num [costCap,Wu04MainTail.cap,tripleCap,fourCap,lx,ux,ly,uy,lz,uz,lw,uw,
    lower,upper,leftFactor,rightFactor,V,lowerLog,upperLog]

theorem first_cost : coupledCostMass row1≤(80362:ℝ)/1000000 := actual_cost_paid.trans cost_rational

theorem first_joint_paid : (78831:ℝ)/1000000≤classicalNumerator row1-2*coupledCostMass row1 := by
  have hb := Wu04WholeReversePaid.first_classical
  have hc := first_cost
  linarith only [hb,hc]

theorem first_actual {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    (239555:ℝ)/5000000-2*(80362/1000000)/(5*(1-2*δ))+
      coupledFeedback row1 (actualNine δ)≤wuImprovementLimit true δ row1.s := by
  have h := original_logs_actual_lower (coupledRow_geometry 0) hd hh
  change classicalNumerator row1/5-2*coupledCostMass row1/(5*(1-2*δ))+
    coupledFeedback row1 (actualNine δ)≤wuImprovementLimit true δ row1.s at h
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left first_cost (by norm_num : (0:ℝ)≤2))
    (show 0≤5*(1-2*δ) by linarith)
  have hb := Wu04WholeReversePaid.first_classical
  linarith only [h,hc,hb]

theorem exact_actual {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    Wu04WholeReversePaid.classicalPaid/5-2*costCap/(5*(1-2*δ))+
      coupledFeedback row1 (actualNine δ)≤wuImprovementLimit true δ row1.s := by
  have h := original_logs_actual_lower (coupledRow_geometry 0) hd hh
  change classicalNumerator row1/5-2*coupledCostMass row1/(5*(1-2*δ))+
    coupledFeedback row1 (actualNine δ)≤wuImprovementLimit true δ row1.s at h
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left actual_cost_paid (by norm_num : (0:ℝ)≤2))
    (show 0≤5*(1-2*δ) by linarith)
  have hb := Wu04WholeReversePaid.classical_payment
  linarith only [h,hc,hb]

theorem residual_identity :
    classicalNumerator row1-2*coupledCostMass row1-5*(15826357:ℝ)/1000000000 =
      (classicalNumerator row1-239555/1000000)+
      2*(80362/1000000-coupledCostMass row1)-60157/200000000 := by ring

end
end Wu04WholeCostPaid
