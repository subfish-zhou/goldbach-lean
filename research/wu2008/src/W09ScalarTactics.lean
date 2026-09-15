import NineLiteral

namespace WuTarget.W09
open Wu2008DoubleSieve ActualNineFeedback
open Wu04RemainingCore Wu04RemainingStrongCompleteCost
open Wu04RemainingStrongClassical Wu04FactorEnvelopes Wu04WholeCollection
open SharpLogRecurrence JointLogTotalComparison

macro "w09_remaining_scalar" : tactic => `(tactic| (
  simp only [Wu04RemainingStrongPublication.slack,costCap,
    Wu04RemainingStrongPrefixCost.costCap,
    Wu04RemainingStrongGammaMass.gain,Wu04RemainingStrongGammaMass.massLower,
    Wu04RemainingStrongGamma.lo,Wu04RemainingStrongGamma.hi,Wu04RemainingStrongGamma.cut,
    Wu04RemainingStrongFourthMass.gain,Wu04RemainingStrongFourthMass.rectLower,
    Wu04RemainingStrongFourthMass.curveLower,Wu04RemainingStrongFourthVolume.area,
    Wu04RemainingStrongFourth.a,Wu04RemainingStrongFourth.b,Wu04RemainingStrongFourth.c,
    Wu04RemainingStrongFourth.f,Wu04RemainingStrongFourth.r,Wu04RemainingStrongFourth.rc,
    Wu04RemainingStrongFourth.v,publication,row,coupledRow,SecondFunctionalPositive.parameters,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  norm_num [certificate,jS,jK,lS,lK,chainLow,chainUp,Wu04RemainingClassical.lCertificate,
    Wu04WholePayment.paidJ,Wu04WholePayment.paidL,Wu04MainClassical.a,
    paid,signedLow,low,up,ratio,yl,yu,rest,pay,upperPay,
    Wu04MainPayment.pS,Wu04MainPayment.qS,Wu04MainPayment.pK,Wu04MainPayment.qK,
    Wu04MainPayment.lS,Wu04MainPayment.uS,Wu04MainPayment.lK,Wu04MainPayment.uK,
    Wu04FactorJPrimitive.c0,Wu04FactorJPrimitive.c1,Wu04FactorJPrimitive.cubic,
    Wu04FactorJPrimitive.h2,Wu04FactorJPrimitive.h3,Wu04FactorLPrimitive.rationalPart,
    Wu04RemainingEnvelope.costCap,Wu04RemainingEnvelope.tripleCap,Wu04RemainingEnvelope.fourCap,
    Wu04RemainingEnvelope.highCap,Wu04RemainingEnvelope.lx,Wu04RemainingEnvelope.ux,
    Wu04RemainingEnvelope.ly,Wu04RemainingEnvelope.uy,Wu04RemainingEnvelope.lz,Wu04RemainingEnvelope.uz,
    Wu04RemainingEnvelope.lw,Wu04RemainingEnvelope.uw,Wu04RemainingStrongThird.gain,
    Wu04RemainingStrongThird.massLower,Wu04MainTail.cap,Wu04ThreeTail.cap,Wu04RecoverGamma.d,
    lower,upper,leftFactor,rightFactor,lowerLog,V,upperLog,
    SecondFunctionalParameters.row2,SecondFunctionalParameters.row3,SecondFunctionalParameters.row4]
))

open Wu04FirstClassical Wu04FirstCertificate Wu04FirstCost

macro "w09_first_scalar" : tactic => `(tactic| (
  simp only [Wu04FirstPublication.slack,Wu04FirstCertificate.base,
    Wu04FirstCertificate.costCap,massCap,Wu04FirstMass.gain,Wu04FirstMass.massLower,
    Wu04FirstCost.lo,Wu04FirstCost.hi,Wu04FirstCost.cut,
    classicalPaid,jPaid,lPaid,firstNode,firstS,Wu04FirstCore.publication,
    Fin.castSucc_zero,Fin.castSucc_succ,Matrix.cons_val_zero,Matrix.cons_val_succ]
  norm_num [Wu04FirstPublication.slack,Wu04FirstCertificate.base,
    Wu04FirstCertificate.costCap,massCap,
    Wu04FirstMass.gain,Wu04FirstMass.massLower,Wu04RecoverGamma.d,
    lo,hi,cut,firstNode,firstS,Wu04FirstCore.publication,classicalPaid,jPaid,lPaid,
    Wu04WholePayment.paidJ,Wu04WholePayment.paidL,Wu04MainClassical.a,
    chainLow,chainUp,paid,signedLow,low,up,ratio,yl,yu,rest,pay,upperPay,
    Wu04MainPayment.pK,Wu04MainPayment.qK,Wu04MainPayment.lK,Wu04MainPayment.uK,
    Wu04FactorJPrimitive.c0,Wu04FactorJPrimitive.c1,Wu04FactorJPrimitive.cubic,
    Wu04FactorJPrimitive.h2,Wu04FactorJPrimitive.h3,Wu04FactorLPrimitive.rationalPart,
    Wu04MainTail.cap,Wu04ThreeTail.cap,lower,upper,leftFactor,rightFactor,lowerLog,V,upperLog]
))

end WuTarget.W09
