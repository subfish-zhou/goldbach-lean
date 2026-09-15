import Wu04RemainingStrongCompleteCost

namespace Wu04RemainingStrongPublication
open Wu2008DoubleSieve Wu04RemainingCore Wu04RemainingStrongCompleteCost
open Wu04RemainingStrongClassical Wu04FactorEnvelopes Wu04WholeCollection
open SharpLogRecurrence JointLogTotalComparison
noncomputable section

def slack (i : Fin 3) : ℝ := certificate (row i)-2*costCap i-5*publication i

/-- Compare only after all genuine domain gains have entered the complete paid cost. -/
theorem slack_zero : 0<slack (0 : Fin 3) := by
  simp only [slack,costCap,Wu04RemainingStrongPrefixCost.costCap,
    Wu04RemainingStrongGammaMass.gain,Wu04RemainingStrongGammaMass.massLower,
    Wu04RemainingStrongGamma.lo,Wu04RemainingStrongGamma.hi,Wu04RemainingStrongGamma.cut,
    Wu04RemainingStrongFourthMass.gain,Wu04RemainingStrongFourthMass.rectLower,
    Wu04RemainingStrongFourthMass.curveLower,Wu04RemainingStrongFourthVolume.area,
    Wu04RemainingStrongFourth.a,Wu04RemainingStrongFourth.b,Wu04RemainingStrongFourth.c,
    Wu04RemainingStrongFourth.f,Wu04RemainingStrongFourth.r,Wu04RemainingStrongFourth.rc,
    Wu04RemainingStrongFourth.v,publication,row,ActualNineFeedback.coupledRow,SecondFunctionalPositive.parameters,
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

theorem slack_one : 0<slack (Fin.succ (0 : Fin 2)) := by
  simp only [slack,costCap,Wu04RemainingStrongPrefixCost.costCap,
    Wu04RemainingStrongGammaMass.gain,Wu04RemainingStrongGammaMass.massLower,
    Wu04RemainingStrongGamma.lo,Wu04RemainingStrongGamma.hi,Wu04RemainingStrongGamma.cut,
    Wu04RemainingStrongFourthMass.gain,Wu04RemainingStrongFourthMass.rectLower,
    Wu04RemainingStrongFourthMass.curveLower,Wu04RemainingStrongFourthVolume.area,
    Wu04RemainingStrongFourth.a,Wu04RemainingStrongFourth.b,Wu04RemainingStrongFourth.c,
    Wu04RemainingStrongFourth.f,Wu04RemainingStrongFourth.r,Wu04RemainingStrongFourth.rc,
    Wu04RemainingStrongFourth.v,publication,row,ActualNineFeedback.coupledRow,SecondFunctionalPositive.parameters,
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

theorem slack_two : 0<slack (Fin.succ (Fin.succ (0 : Fin 1))) := by
  simp only [slack,costCap,Wu04RemainingStrongPrefixCost.costCap,
    Wu04RemainingStrongGammaMass.gain,Wu04RemainingStrongGammaMass.massLower,
    Wu04RemainingStrongGamma.lo,Wu04RemainingStrongGamma.hi,Wu04RemainingStrongGamma.cut,
    Wu04RemainingStrongFourthMass.gain,Wu04RemainingStrongFourthMass.rectLower,
    Wu04RemainingStrongFourthMass.curveLower,Wu04RemainingStrongFourthVolume.area,
    Wu04RemainingStrongFourth.a,Wu04RemainingStrongFourth.b,Wu04RemainingStrongFourth.c,
    Wu04RemainingStrongFourth.f,Wu04RemainingStrongFourth.r,Wu04RemainingStrongFourth.rc,
    Wu04RemainingStrongFourth.v,publication,row,ActualNineFeedback.coupledRow,SecondFunctionalPositive.parameters,
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
  norm_num [Fin.ext_iff]

theorem slack_pos (i : Fin 3) : 0<slack i := by
  have h : ∀ i : Fin 3,0<slack i := by
    simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,and_true]
    exact ⟨slack_zero,slack_one,slack_two⟩
  exact h i

end
end Wu04RemainingStrongPublication
