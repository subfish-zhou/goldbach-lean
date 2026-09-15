import NineLiteral

namespace WuTarget.W09
open Wu2008DoubleSieve ActualNineFeedback
open Wu04RemainingCore Wu04RemainingStrongCompleteCost
open Wu04RemainingStrongClassical Wu04FactorEnvelopes Wu04WholeCollection
open SharpLogRecurrence JointLogTotalComparison

example : True := by
  have h : (![Wu04RemainingStrongPublication.slack 0,
      Wu04RemainingStrongPublication.slack 1,
      Wu04RemainingStrongPublication.slack 2] : Fin 3 → ℝ) =
      ![Wu04RemainingStrongPublication.slack 0,
        Wu04RemainingStrongPublication.slack 1,
        Wu04RemainingStrongPublication.slack 2] := rfl
  conv_lhs at h =>
    norm_num [Wu04RemainingStrongPublication.slack,costCap,
      Wu04RemainingStrongPrefixCost.costCap,
      Wu04RemainingStrongGammaMass.gain,Wu04RemainingStrongGammaMass.massLower,
      Wu04RemainingStrongGamma.lo,Wu04RemainingStrongGamma.hi,Wu04RemainingStrongGamma.cut,
      Wu04RemainingStrongFourthMass.gain,Wu04RemainingStrongFourthMass.rectLower,
      Wu04RemainingStrongFourthMass.curveLower,Wu04RemainingStrongFourthVolume.area,
      Wu04RemainingStrongFourth.a,Wu04RemainingStrongFourth.b,Wu04RemainingStrongFourth.c,
      Wu04RemainingStrongFourth.f,Wu04RemainingStrongFourth.r,Wu04RemainingStrongFourth.rc,
      Wu04RemainingStrongFourth.v,publication,row,coupledRow,SecondFunctionalPositive.parameters,
      certificate,jS,jK,lS,lK,chainLow,chainUp,Wu04RemainingClassical.lCertificate,
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
  trace_state
  trivial

open Wu04FirstClassical Wu04FirstCertificate Wu04FirstCost

example : True := by
  have h : (![Wu04FirstPublication.slack 0,Wu04FirstPublication.slack 1,
      Wu04FirstPublication.slack 2,Wu04FirstPublication.slack 3] : Fin 4 → ℝ) =
      ![Wu04FirstPublication.slack 0,Wu04FirstPublication.slack 1,
        Wu04FirstPublication.slack 2,Wu04FirstPublication.slack 3] := rfl
  conv_lhs at h =>
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
  trace_state
  trivial

end WuTarget.W09
