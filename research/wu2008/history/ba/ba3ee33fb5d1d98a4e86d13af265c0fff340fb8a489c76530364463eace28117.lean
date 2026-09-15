import E10FourRoot

noncomputable section
open Real Wu2008DoubleSieve FourRoughClosedMass

namespace WuTarget.E10FourMajor

def z0 : ℝ := (alpha+3*beta)/4
def slope : ℝ := z0/(lam-z0)
def crossCap : ℝ :=
  SharpLogRecurrence.upperLog ((lam-z0)/beta)-
    slope*SharpLogRecurrence.lowerLog (beta/z0)
def recipCoeff (i : Fin 5) : ℝ :=
  ![1/beta,1/beta,1/(2*beta),1/(6*beta),1/(24*alpha)] i
def capTerm (i : Fin 5) : ℝ :=
  (4/7)*recipCoeff i*
    (crossCap*W13Tight.momentUpper (i.val+2)/(i.val+2 : ℝ)+
      (1+slope)*W13Tight.momentUpper (i.val+3)/(2*(i.val+3 : ℝ)))
def pairCap : ℝ := ∑ i : Fin 5, capTerm i

theorem fixed_geometry_major :
    0 < alpha ∧ alpha ≤ beta ∧ alpha ≤ z0 ∧ z0 ≤ beta ∧
    beta ≤ lam-beta ∧ 0 < beta ∧ 0 < z0 ∧ 0 < lam-z0 := by
  norm_num [alpha,beta,lam,z0,truncatedSixthLowerAlpha,
    truncatedSixthLowerBeta,truncatedSixthLowerLambda]

theorem slope_pos : 0 < slope := by
  unfold slope
  exact div_pos fixed_geometry_major.2.2.2.2.2.2.1
    fixed_geometry_major.2.2.2.2.2.2.2

theorem crossCap_pos : 0 < crossCap := by
  norm_num [crossCap,slope,z0,SharpLogRecurrence.upperLog,SharpLogRecurrence.lowerLog,
    alpha,beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

theorem recipCoeff_pos (i : Fin 5) : 0 < recipCoeff i := by
  fin_cases i <;>
    norm_num [recipCoeff,alpha,beta,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem pairCap_lt_target : pairCap < (7/10 : ℝ) := by
  norm_num [pairCap,capTerm,Fin.sum_univ_succ,recipCoeff,crossCap,slope,z0,
    W13Tight.momentUpper,W13Tight.discount,W13Tight.primitive,
    W13.h,W13.d,W13.k,W13.cut,FourLogAffine.u,
    SharpLogRecurrence.upperLog,SharpLogRecurrence.lowerLog,
    alpha,beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

end WuTarget.E10FourMajor
