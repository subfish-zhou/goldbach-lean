import Wu04FirstCertificate

namespace Wu04FirstPublication
open Wu2008DoubleSieve ActualNineFeedback Real
open Wu04FirstCore Wu04FirstClassical Wu04FirstCertificate Wu04FirstCost
open Wu04RemainingStrongClassical Wu04WholeCollection Wu04FactorEnvelopes
open SharpLogRecurrence JointLogTotalComparison
noncomputable section

def slack (i : Fin 4) : ℝ := Wu04FirstCertificate.base i-publication i.castSucc

theorem slack_zero : 0<slack (0 : Fin 4) := by
  simp only [slack,Wu04FirstCertificate.base,Wu04FirstCertificate.costCap,massCap,
    Wu04FirstMass.gain,Wu04FirstMass.massLower,Wu04FirstCost.lo,Wu04FirstCost.hi,Wu04FirstCost.cut,
    classicalPaid,jPaid,lPaid,firstNode,firstS,publication,
    Fin.castSucc_zero,Matrix.cons_val_zero]
  norm_num [slack,Wu04FirstCertificate.base,Wu04FirstCertificate.costCap,massCap,
    Wu04FirstMass.gain,Wu04FirstMass.massLower,Wu04RecoverGamma.d,
    lo,hi,cut,firstNode,firstS,publication,classicalPaid,jPaid,lPaid,
    Wu04WholePayment.paidJ,Wu04WholePayment.paidL,Wu04MainClassical.a,
    chainLow,chainUp,paid,signedLow,low,up,ratio,yl,yu,rest,pay,upperPay,
    Wu04MainPayment.pK,Wu04MainPayment.qK,Wu04MainPayment.lK,Wu04MainPayment.uK,
    Wu04FactorJPrimitive.c0,Wu04FactorJPrimitive.c1,Wu04FactorJPrimitive.cubic,
    Wu04FactorJPrimitive.h2,Wu04FactorJPrimitive.h3,Wu04FactorLPrimitive.rationalPart,
    Wu04MainTail.cap,Wu04ThreeTail.cap,lower,upper,leftFactor,rightFactor,lowerLog,V,upperLog]

theorem slack_one : 0<slack (1 : Fin 4) := by
  simp only [slack,Wu04FirstCertificate.base,Wu04FirstCertificate.costCap,massCap,
    Wu04FirstMass.gain,Wu04FirstMass.massLower,Wu04FirstCost.lo,Wu04FirstCost.hi,Wu04FirstCost.cut,
    classicalPaid,jPaid,lPaid,firstNode,firstS,publication]
  norm_num [slack,Wu04FirstCertificate.base,Wu04FirstCertificate.costCap,massCap,
    Wu04FirstMass.gain,Wu04FirstMass.massLower,Wu04RecoverGamma.d,
    lo,hi,cut,firstNode,firstS,publication,classicalPaid,jPaid,lPaid,
    Wu04WholePayment.paidJ,Wu04WholePayment.paidL,Wu04MainClassical.a,
    chainLow,chainUp,paid,signedLow,low,up,ratio,yl,yu,rest,pay,upperPay,
    Wu04MainPayment.pK,Wu04MainPayment.qK,Wu04MainPayment.lK,Wu04MainPayment.uK,
    Wu04FactorJPrimitive.c0,Wu04FactorJPrimitive.c1,Wu04FactorJPrimitive.cubic,
    Wu04FactorJPrimitive.h2,Wu04FactorJPrimitive.h3,Wu04FactorLPrimitive.rationalPart,
    Wu04MainTail.cap,Wu04ThreeTail.cap,lower,upper,leftFactor,rightFactor,lowerLog,V,upperLog]

theorem slack_two : 0<slack (Fin.succ (Fin.succ (0 : Fin 2))) := by
  simp only [slack,Wu04FirstCertificate.base,Wu04FirstCertificate.costCap,massCap,
    Wu04FirstMass.gain,Wu04FirstMass.massLower,Wu04FirstCost.lo,Wu04FirstCost.hi,Wu04FirstCost.cut,
    classicalPaid,jPaid,lPaid,firstNode,firstS,publication,
    Fin.castSucc_zero,Fin.castSucc_succ,Matrix.cons_val_zero,Matrix.cons_val_succ]
  norm_num [slack,Wu04FirstCertificate.base,Wu04FirstCertificate.costCap,massCap,
    Wu04FirstMass.gain,Wu04FirstMass.massLower,Wu04RecoverGamma.d,
    lo,hi,cut,firstNode,firstS,publication,classicalPaid,jPaid,lPaid,
    Wu04WholePayment.paidJ,Wu04WholePayment.paidL,Wu04MainClassical.a,
    chainLow,chainUp,paid,signedLow,low,up,ratio,yl,yu,rest,pay,upperPay,
    Wu04MainPayment.pK,Wu04MainPayment.qK,Wu04MainPayment.lK,Wu04MainPayment.uK,
    Wu04FactorJPrimitive.c0,Wu04FactorJPrimitive.c1,Wu04FactorJPrimitive.cubic,
    Wu04FactorJPrimitive.h2,Wu04FactorJPrimitive.h3,Wu04FactorLPrimitive.rationalPart,
    Wu04MainTail.cap,Wu04ThreeTail.cap,lower,upper,leftFactor,rightFactor,lowerLog,V,upperLog]

theorem slack_three : 0<slack (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1)))) := by
  simp only [slack,Wu04FirstCertificate.base,Wu04FirstCertificate.costCap,massCap,
    Wu04FirstMass.gain,Wu04FirstMass.massLower,Wu04FirstCost.lo,Wu04FirstCost.hi,Wu04FirstCost.cut,
    classicalPaid,jPaid,lPaid,firstNode,firstS,publication,
    Fin.castSucc_zero,Fin.castSucc_succ,Matrix.cons_val_zero,Matrix.cons_val_succ]
  norm_num [slack,Wu04FirstCertificate.base,Wu04FirstCertificate.costCap,massCap,
    Wu04FirstMass.gain,Wu04FirstMass.massLower,Wu04RecoverGamma.d,
    lo,hi,cut,firstNode,firstS,publication,classicalPaid,jPaid,lPaid,
    Wu04WholePayment.paidJ,Wu04WholePayment.paidL,Wu04MainClassical.a,
    chainLow,chainUp,paid,signedLow,low,up,ratio,yl,yu,rest,pay,upperPay,
    Wu04MainPayment.pK,Wu04MainPayment.qK,Wu04MainPayment.lK,Wu04MainPayment.uK,
    Wu04FactorJPrimitive.c0,Wu04FactorJPrimitive.c1,Wu04FactorJPrimitive.cubic,
    Wu04FactorJPrimitive.h2,Wu04FactorJPrimitive.h3,Wu04FactorLPrimitive.rationalPart,
    Wu04MainTail.cap,Wu04ThreeTail.cap,lower,upper,leftFactor,rightFactor,lowerLog,V,upperLog]

end
end Wu04FirstPublication
