import Wu04RecoverGamma

namespace Wu04RecoverGammaMass
open Wu2008DoubleSieve Wu04RecoverGamma Set MeasureTheory Real
open SecondFunctionalParameters SecondFunctionalGeometricMass SecondFunctionalJointTail
open SharpLogRecurrence JointLogTotalComparison
noncomputable section

theorem invsq_integral {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ t in a..b, (1:ℝ)/t^2)=1/a-1/b := by
  simpa [FullReduction.logMoment, Elementary.elementaryMomentZero, Elementary.momentPolynomial] using
    Elementary.logMoment_zero_eq 0 ha hab

theorem invsq_integrable {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    IntervalIntegrable (fun t : ℝ => (1:ℝ)/t^2) volume a b := by
  simpa only [pow_zero] using Elementary.logPower_intervalIntegrable 0 ha hab

theorem blockInner_exact {a b : ℝ} (ha : lo≤a) (hb : lo≤b) :
    blockInner a b=log (hi/r)/a/b^2 := by
  unfold blockInner
  have he : (∫ c in r..hi, W a b c) = ∫ c in r..hi, (1/(a*b^2))*(1/c) := by
    apply intervalIntegral.integral_congr
    intro c hc
    rw [uIcc_of_le geometry.2.2.2.1.le] at hc
    rw [show W a b c=1/(a*b^2*c) from Omega3ElementaryRegularity.extension_eq
      (geometry.1.trans ha) (geometry.1.trans hb) ((geometry.1.trans geometry.2.2.1.le).trans hc.1)]
    ring
  rw [he,intervalIntegral.integral_const_mul,
    integral_one_div_of_pos (geometry.2.1.trans geometry.2.2.1)
      (geometry.2.1.trans (geometry.2.2.1.trans geometry.2.2.2.1))]
  ring

theorem blockMiddle_exact {a : ℝ} (ha : a∈Icc lo r) :
    blockMiddle a=log (hi/r)/a*(1/a-1/r) := by
  unfold blockMiddle
  have he : (∫ b in a..r, blockInner a b) = ∫ b in a..r, (log (hi/r)/a)*(1/b^2) := by
    apply intervalIntegral.integral_congr
    intro b hb
    rw [uIcc_of_le ha.2] at hb
    rw [blockInner_exact ha.1 (ha.1.trans hb.1)]
    ring
  rw [he,intervalIntegral.integral_const_mul,invsq_integral (geometry.2.1.trans_le ha.1) ha.2]

theorem block_mass_exact : (∫ a in lo..r, blockMiddle a)=
    log (hi/r)*(1/lo-(1+log (r/lo))/r) := by
  have hrec : IntervalIntegrable (fun a : ℝ => 1/a) volume lo r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le geometry.2.2.1.le]
    exact continuousOn_const.div continuousOn_id (fun a ha => (geometry.2.1.trans_le ha.1).ne')
  have he : (∫ a in lo..r, blockMiddle a)=
      log (hi/r)*((∫ a in lo..r, 1/a^2)-(1/r)*(∫ a in lo..r, 1/a)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (invsq_integrable geometry.2.1 geometry.2.2.1.le)
      (hrec.const_mul (1/r)),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro a ha
    rw [uIcc_of_le geometry.2.2.1.le] at ha
    rw [blockMiddle_exact ha]
    ring
  rw [he,invsq_integral geometry.2.1 geometry.2.2.1.le,
    integral_one_div_of_pos geometry.2.1 (geometry.2.1.trans geometry.2.2.1)]
  ring

def massLower : ℝ := Wu04FactorEnvelopes.lower (hi/r)*
  (1/lo-(1+Wu04FactorEnvelopes.upper (r/lo))/r)
def gain : ℝ := d*massLower

theorem massLower_pos : 0<massLower := by
  norm_num [massLower,lo,hi,r,row1,Wu04FactorEnvelopes.lower,Wu04FactorEnvelopes.upper,
    Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,V,lowerLog,upperLog]

theorem mass_paid : massLower≤∫ a in lo..r, blockMiddle a := by
  rw [block_mass_exact]
  have hl := Wu04FactorEnvelopes.lower_le_log (by norm_num [hi,r,row1] : 1≤hi/r)
  have hu := Wu04FactorEnvelopes.log_le_upper (by norm_num [lo,hi,r,row1] : 1≤r/lo)
  have hl0 : 0≤Wu04FactorEnvelopes.lower (hi/r) := by
    norm_num [hi,r,row1,Wu04FactorEnvelopes.lower,Wu04FactorEnvelopes.leftFactor,
      Wu04FactorEnvelopes.rightFactor,lowerLog]
  have hm0 : 0≤1/lo-(1+Wu04FactorEnvelopes.upper (r/lo))/r := by
    norm_num [lo,hi,r,row1,Wu04FactorEnvelopes.upper,Wu04FactorEnvelopes.leftFactor,
      Wu04FactorEnvelopes.rightFactor,V,lowerLog,upperLog]
  have hm : 1/lo-(1+Wu04FactorEnvelopes.upper (r/lo))/r≤1/lo-(1+log (r/lo))/r := by
    have h := div_le_div_of_nonneg_right (add_le_add_right hu 1)
      (geometry.2.1.trans geometry.2.2.1).le
    linarith only [h]
  exact mul_le_mul hl hm hm0 (hl0.trans hl)

theorem gain_pos : 0<gain := mul_pos d_pos massLower_pos

theorem inner_identity (phi a b : ℝ) : inner phi a b =
    Wu04MainTail.cap*(∫ c in b..hi, W a b c)-
      ∫ c in b..hi, omega3XIntegralKernelExtension phi a b c := by
  have hw : Continuous (fun c => W a b c) := W_cont.comp
    (show Continuous (fun c : ℝ => (a,b,c)) by fun_prop)
  have hk : Continuous (fun c => omega3XIntegralKernelExtension phi a b c) :=
    omega3XIntegralKernelExtension_continuous.comp (f := fun c : ℝ => (phi,a,b,c)) (by fun_prop)
  exact (intervalIntegral.integral_sub ((hw.const_mul _).intervalIntegrable _ _)
    (hk.intervalIntegrable _ _)).trans (by rw [intervalIntegral.integral_const_mul])

theorem middle_identity (phi a : ℝ) : middle phi a =
    Wu04MainTail.cap*(∫ b in a..hi, ∫ c in b..hi, W a b c)-
      ∫ b in a..hi, ∫ c in b..hi, omega3XIntegralKernelExtension phi a b c := by
  have hw : Continuous (fun b => ∫ c in b..hi, W a b c) :=
    (Omega3ElementaryRegularity.inner_continuous hi).comp
      (show Continuous (fun b : ℝ => (a,b)) by fun_prop)
  have hk : Continuous (fun b => ∫ c in b..hi, omega3XIntegralKernelExtension phi a b c) :=
    omega3XIntegral_innerExtension_continuous.comp (f := fun b : ℝ => (phi,hi,a,b)) (by fun_prop)
  unfold middle
  simp_rw [inner_identity]
  rw [intervalIntegral.integral_sub ((hw.const_mul _).intervalIntegrable _ _) (hk.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]

theorem deficit_identity (phi : ℝ) : (∫ a in lo..hi, middle phi a)=
    Wu04MainTail.cap*Elementary.elementaryMomentOne 1 lo hi-
      omega3XIntegral row1.kappa3 row1.kappa1 phi := by
  have hw : Continuous (fun a => ∫ b in a..hi, ∫ c in b..hi, W a b c) :=
    Omega3ElementaryRegularity.middle_continuous hi
  have hk : Continuous (fun a => ∫ b in a..hi, ∫ c in b..hi, omega3XIntegralKernelExtension phi a b c) :=
    omega3XIntegral_middleExtension_continuous.comp (f := fun a : ℝ => (phi,hi,a)) (by fun_prop)
  simp_rw [middle_identity]
  rw [intervalIntegral.integral_sub ((hw.const_mul _).intervalIntegrable _ _) (hk.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  have he : (∫ a in lo..hi, ∫ b in a..hi, ∫ c in b..hi, W a b c)=
      Elementary.elementaryMomentOne 1 lo hi := by
    calc
      _ = ∫ a in lo..hi, ∫ b in a..hi, ∫ c in b..hi, (1:ℝ)/(a*b^2*c) := by
        apply intervalIntegral.integral_congr
        intro a ha
        rw [uIcc_of_le (geometry.2.2.1.trans geometry.2.2.2.1).le] at ha
        exact Omega3ElementaryRegularity.middle_eq (geometry.1.trans ha.1) ha.2
      _ = _ := Omega3ElementaryMass.nested_eq_elementary geometry.2.1
        (geometry.2.2.1.trans geometry.2.2.2.1).le
  rw [he]
  have heK := omega3XIntegralExtension_eq (φ:=phi) geometry.1
    (geometry.2.2.1.trans geometry.2.2.2.1).le
  change _ - omega3XIntegralExtension lo hi phi = _
  rw [heK]
  rfl

/-- Genuine independent Gamma9 pointwise gain, before taking its own supremum. -/
theorem first_omega {phi : ℝ} (hp : 2≤phi) :
    omega3XIntegral row1.kappa3 row1.kappa1 phi≤Wu04MainProducer.omegaCap-gain := by
  have h := deficit_paid hp
  rw [deficit_identity] at h
  have hm := mul_le_mul_of_nonneg_left mass_paid d_pos.le
  change omega3XIntegral row1.kappa3 row1.kappa1 phi≤
    Wu04MainTail.cap*Elementary.elementaryMomentOne 1 lo hi-gain
  unfold gain
  linarith only [h,hm]
end
end Wu04RecoverGammaMass
