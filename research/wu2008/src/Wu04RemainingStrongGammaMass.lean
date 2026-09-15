import Wu04RemainingStrongGamma

namespace Wu04RemainingStrongGammaMass
open Wu2008DoubleSieve Set MeasureTheory Real Wu04RemainingCore Wu04RemainingStrongGamma
open SecondFunctionalGeometricMass SecondFunctionalJointTail
noncomputable section

/-- Exact selected-square cap mass at the forced original endpoints. -/
theorem mass_exact (i : Fin 3) :
    (∫ a in lo i..cut i,∫ b in a..cut i,∫ c in cut i..hi i,Wu04RecoverGamma.W a b c)=
    log (hi i/cut i)*(1/lo i-(1+log (cut i/lo i))/cut i) := by
  have g := geometry i
  have hr := g.2.1.trans g.2.2.1
  have hh := hr.trans g.2.2.2
  have inner (a b : ℝ) (ha : lo i≤a) (hb : lo i≤b) :
      (∫ c in cut i..hi i,Wu04RecoverGamma.W a b c)=log (hi i/cut i)/a/b^2 := by
    calc
      _ = ∫ c in cut i..hi i,(1/(a*b^2))*(1/c) := by
        apply intervalIntegral.integral_congr
        intro c hc
        rw [uIcc_of_le g.2.2.2.le] at hc
        rw [show Wu04RecoverGamma.W a b c=1/(a*b^2*c) from
          Omega3ElementaryRegularity.extension_eq (g.1.trans ha) (g.1.trans hb)
            ((g.1.trans g.2.2.1.le).trans hc.1)]
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul,integral_one_div_of_pos hr hh]; ring
  have middle (a : ℝ) (ha : a∈Icc (lo i) (cut i)) :
      (∫ b in a..cut i,∫ c in cut i..hi i,Wu04RecoverGamma.W a b c)=
      log (hi i/cut i)/a*(1/a-1/cut i) := by
    calc
      _ = ∫ b in a..cut i,(log (hi i/cut i)/a)*(1/b^2) := by
        apply intervalIntegral.integral_congr
        intro b hb
        rw [uIcc_of_le ha.2] at hb
        dsimp only
        rw [inner a b ha.1 (ha.1.trans hb.1)]
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul,
        Wu04RecoverGammaMass.invsq_integral (g.2.1.trans_le ha.1) ha.2]
  have hi1 : IntervalIntegrable (fun a : ℝ => 1/a) volume (lo i) (cut i) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le g.2.2.1.le]
    exact continuousOn_const.div continuousOn_id (fun a ha => (g.2.1.trans_le ha.1).ne')
  calc
    _ = log (hi i/cut i)*((∫ a in lo i..cut i,1/a^2)-
        (1/cut i)*(∫ a in lo i..cut i,1/a)) := by
      rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub
        (Wu04RecoverGammaMass.invsq_integrable g.2.1 g.2.2.1.le) (hi1.const_mul _),
        ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro a ha
      rw [uIcc_of_le g.2.2.1.le] at ha
      dsimp only
      rw [middle a ha]
      ring
    _ = _ := by rw [Wu04RecoverGammaMass.invsq_integral g.2.1 g.2.2.1.le,
      integral_one_div_of_pos g.2.1 hr]; ring

def massLower (i : Fin 3) : ℝ := Wu04FactorEnvelopes.lower (hi i/cut i)*
  (1/lo i-(1+Wu04FactorEnvelopes.upper (cut i/lo i))/cut i)
def gain (i : Fin 3) : ℝ := Wu04RecoverGamma.d*massLower i

theorem factor_pos (i : Fin 3) :
    0<1/lo i-(1+Wu04FactorEnvelopes.upper (cut i/lo i))/cut i := by
  revert i
  simp only [lo,hi,cut,row,ActualNineFeedback.coupledRow,SecondFunctionalPositive.parameters,
    Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,Matrix.cons_val_zero,Matrix.cons_val_succ]
  norm_num [SecondFunctionalParameters.row2,SecondFunctionalParameters.row3,SecondFunctionalParameters.row4,
    Wu04FactorEnvelopes.upper,Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,
    SharpLogRecurrence.lowerLog,SharpLogRecurrence.upperLog,JointLogTotalComparison.V]

theorem lower_pos (i : Fin 3) : 0<Wu04FactorEnvelopes.lower (hi i/cut i) := by
  revert i
  simp only [hi,cut,row,ActualNineFeedback.coupledRow,SecondFunctionalPositive.parameters,
    Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,Matrix.cons_val_zero,Matrix.cons_val_succ]
  norm_num [SecondFunctionalParameters.row2,SecondFunctionalParameters.row3,SecondFunctionalParameters.row4,
    Wu04FactorEnvelopes.lower,Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,
    SharpLogRecurrence.lowerLog]

theorem gain_pos (i : Fin 3) : 0<gain i :=
  mul_pos Wu04RecoverGamma.d_pos (mul_pos (lower_pos i) (factor_pos i))

theorem mass_paid (i : Fin 3) : massLower i≤
    ∫ a in lo i..cut i,∫ b in a..cut i,∫ c in cut i..hi i,Wu04RecoverGamma.W a b c := by
  rw [mass_exact]
  have g := geometry i
  have hr := g.2.1.trans g.2.2.1
  have hl := Wu04FactorEnvelopes.lower_le_log ((one_le_div hr).mpr g.2.2.2.le)
  have hu := Wu04FactorEnvelopes.log_le_upper ((one_le_div g.2.1).mpr g.2.2.1.le)
  have hm := div_le_div_of_nonneg_right (add_le_add_right hu 1) hr.le
  exact mul_le_mul hl (by linarith only [hm]) (factor_pos i).le ((lower_pos i).le.trans hl)

/-- Linearity through continuous nested extensions on arbitrary original endpoints. -/
theorem deficit_identity (i : Fin 3) (φ : ℝ) :
    (∫ a in lo i..hi i,∫ b in a..hi i,∫ c in b..hi i,Wu04RecoverGamma.D φ a b c)=
    Wu04MainTail.cap*Elementary.elementaryMomentOne 1 (lo i) (hi i)-
      omega3XIntegral (row i).kappa3 (row i).kappa1 φ := by
  have g := geometry i
  have inner (a b : ℝ) : (∫ c in b..hi i,Wu04RecoverGamma.D φ a b c)=
      Wu04MainTail.cap*(∫ c in b..hi i,Wu04RecoverGamma.W a b c)-
      ∫ c in b..hi i,omega3XIntegralKernelExtension φ a b c := by
    have hw : Continuous (fun c => Wu04RecoverGamma.W a b c) :=
      Wu04RecoverGamma.W_cont.comp (show Continuous (fun c : ℝ => (a,b,c)) by fun_prop)
    have hk : Continuous (fun c => omega3XIntegralKernelExtension φ a b c) :=
      omega3XIntegralKernelExtension_continuous.comp (f:=fun c : ℝ => (φ,a,b,c)) (by fun_prop)
    unfold Wu04RecoverGamma.D
    rw [intervalIntegral.integral_sub ((hw.const_mul _).intervalIntegrable _ _)
      (hk.intervalIntegrable _ _),intervalIntegral.integral_const_mul]
  have middle (a : ℝ) : (∫ b in a..hi i,∫ c in b..hi i,Wu04RecoverGamma.D φ a b c)=
      Wu04MainTail.cap*(∫ b in a..hi i,∫ c in b..hi i,Wu04RecoverGamma.W a b c)-
      ∫ b in a..hi i,∫ c in b..hi i,omega3XIntegralKernelExtension φ a b c := by
    have hw : Continuous (fun b => ∫ c in b..hi i,Wu04RecoverGamma.W a b c) :=
      (Omega3ElementaryRegularity.inner_continuous (hi i)).comp
        (show Continuous (fun b : ℝ => (a,b)) by fun_prop)
    have hk : Continuous (fun b => ∫ c in b..hi i,omega3XIntegralKernelExtension φ a b c) :=
      omega3XIntegral_innerExtension_continuous.comp (f:=fun b : ℝ => (φ,hi i,a,b)) (by fun_prop)
    simp_rw [inner]
    rw [intervalIntegral.integral_sub ((hw.const_mul _).intervalIntegrable _ _)
      (hk.intervalIntegrable _ _),intervalIntegral.integral_const_mul]
  have hw : Continuous (fun a => ∫ b in a..hi i,∫ c in b..hi i,Wu04RecoverGamma.W a b c) :=
    Omega3ElementaryRegularity.middle_continuous (hi i)
  have hk : Continuous (fun a => ∫ b in a..hi i,∫ c in b..hi i,omega3XIntegralKernelExtension φ a b c) :=
    omega3XIntegral_middleExtension_continuous.comp (f:=fun a : ℝ => (φ,hi i,a)) (by fun_prop)
  simp_rw [middle]
  rw [intervalIntegral.integral_sub ((hw.const_mul _).intervalIntegrable _ _)
    (hk.intervalIntegrable _ _),intervalIntegral.integral_const_mul]
  have hw' : (∫ a in lo i..hi i,∫ b in a..hi i,∫ c in b..hi i,Wu04RecoverGamma.W a b c)=
      Elementary.elementaryMomentOne 1 (lo i) (hi i) := by
    calc
      _ = ∫ a in lo i..hi i,∫ b in a..hi i,∫ c in b..hi i,(1:ℝ)/(a*b^2*c) := by
        apply intervalIntegral.integral_congr
        intro a ha
        rw [uIcc_of_le (g.2.2.1.trans g.2.2.2).le] at ha
        exact Omega3ElementaryRegularity.middle_eq (g.1.trans ha.1) ha.2
      _ = _ := Omega3ElementaryMass.nested_eq_elementary g.2.1 (g.2.2.1.trans g.2.2.2).le
  rw [hw']
  change _-omega3XIntegralExtension (lo i) (hi i) φ=_
  rw [omega3XIntegralExtension_eq g.1 (g.2.2.1.trans g.2.2.2).le]
  rfl

theorem remaining_omega (i : Fin 3) {φ : ℝ} (hφ : 2≤φ) :
    omega3XIntegral (row i).kappa3 (row i).kappa1 φ≤
    Wu04MainTail.cap*Elementary.elementaryMomentOne 1 (lo i) (hi i)-gain i := by
  have hd := deficit_paid i hφ
  rw [deficit_identity] at hd
  have hm := mul_le_mul_of_nonneg_left (mass_paid i) Wu04RecoverGamma.d_pos.le
  unfold gain
  linarith only [hd,hm]
end
end Wu04RemainingStrongGammaMass
