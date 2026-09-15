import Wu04FullPsiMass
import JointLogTotalComparison

namespace Wu04FullPsiCostCertificate
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
open SecondFunctionalParameters Wu04FullPsiMass
noncomputable section

def lx : ℝ := lowerLog (454/353)
def ux : ℝ := V (454/353)
def ly : ℝ := lowerLog (353/290)
def uy : ℝ := V (353/290)
def lz : ℝ := lowerLog (145/122)
def uz : ℝ := V (145/122)
def lw : ℝ := lowerLog (61/55)
def uw : ℝ := V (61/55)

theorem first_log_bounds :
    lx ≤ x row1 ∧ x row1 ≤ ux ∧ ly ≤ y row1 ∧ y row1 ≤ uy ∧
    lz ≤ z row1 ∧ z row1 ≤ uz ∧ lw ≤ w row1 ∧ w row1 ≤ uw := by
  have hx := And.intro (log_lower (by norm_num : (1:ℝ)≤454/353)) (log_le_V (by norm_num : (1:ℝ)≤454/353))
  have hy := And.intro (log_lower (by norm_num : (1:ℝ)≤353/290)) (log_le_V (by norm_num : (1:ℝ)≤353/290))
  have hz := And.intro (log_lower (by norm_num : (1:ℝ)≤145/122)) (log_le_V (by norm_num : (1:ℝ)≤145/122))
  have hw := And.intro (log_lower (by norm_num : (1:ℝ)≤61/55)) (log_le_V (by norm_num : (1:ℝ)≤61/55))
  norm_num [x,y,z,w,row1] at *
  exact ⟨hx.1,hx.2,hy.1,hy.2,hz.1,hz.2,hw.1,hw.2⟩

def tripleCap : ℝ :=
  (353/100-290/100+2*(244/100))*uy +
  (2*(353/100)-290/100+244/100)*uz + (454/100-290/100)*uw -
  (244/100)*ly*lw + (353/100)*ux*uz + (220/100-290/100)*lx -
  2*(353/100-244/100)

def fourCap : ℝ :=
  (290/100+2*(244/100))*uz + (290/100-244/100)*uw -
  (244/100)*lz*lw + (220/100/2)*uz^2 - 3*(290/100-244/100) +
  (244/100+220/100)*uy*uw - 2*(244/100-220/100)*ly

def costCap : ℝ := (4/7)*tripleCap + fourCap + 207/8318750

theorem first_polynomials_bounded :
    triplePolynomial row1 ≤ tripleCap ∧ fourPolynomial row1 ≤ fourCap := by
  obtain ⟨hxL,hxU,hyL,hyU,hzL,hzU,hwL,hwU⟩ := first_log_bounds
  have hlx : 0 ≤ lx := by norm_num [lx,lowerLog]
  have hly : 0 ≤ ly := by norm_num [ly,lowerLog]
  have hlz : 0 ≤ lz := by norm_num [lz,lowerLog]
  have hlw : 0 ≤ lw := by norm_num [lw,lowerLog]
  have hux : 0 ≤ ux := hlx.trans (hxL.trans hxU)
  have huy : 0 ≤ uy := hly.trans (hyL.trans hyU)
  have huz : 0 ≤ uz := hlz.trans (hzL.trans hzU)
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

theorem first_cost_cap : ActualNineFeedback.coupledCostMass row1 ≤ costCap := by
  have h := original_cost_polynomial 0
  change ActualNineFeedback.coupledCostMass row1 ≤ fullCostPolynomial row1 at h
  have hp := first_polynomials_bounded
  have hu := Wu04CoupledCostProducer.first_U20_rational
  unfold fullCostPolynomial at h
  unfold costCap
  linarith only [h,hp.1,hp.2,hu]

theorem cost_cap_rational : costCap ≤ (80922:ℝ)/1000000 := by
  norm_num [costCap,tripleCap,fourCap,lx,ux,ly,uy,lz,uz,lw,uw,V,lowerLog,upperLog]

theorem first_cost_rational : ActualNineFeedback.coupledCostMass row1 ≤ (80922:ℝ)/1000000 :=
  first_cost_cap.trans cost_cap_rational

#print axioms first_log_bounds
#print axioms first_cost_rational
end
end Wu04FullPsiCostCertificate
