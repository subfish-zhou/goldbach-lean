import CoupledGateActualAssembly

namespace CoupledMiddleGateRecovery
open Real Set MeasureTheory Wu2008DoubleSieve MotherPair NodeExtension ActualNineFeedback
open GatedDensityPayment FiniteEndpointPayment CoupledHGateRecovery
open scoped Interval BigOperators
noncomputable section

/-- Exact constant cross-ratio forced by the middle branch. -/
def middleRatio (p : SecondFunctionalParameters) : ℝ := (p.kappa1-1)/(p.kappa2-1)

theorem middle_geometry {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (ha : 1≤upperSwitch p) {v : ℝ}
    (hv : v∈Icc (upperSwitch p) (lowerSwitch p)) :
    feedbackLower p .gammaEight v=(1-1/p.kappa2)/(v+1) ∧
    feedbackUpper p .gammaEight v=(1-1/p.kappa1)/(v+1) := by
  have hk2 : 2<p.kappa2 := by
    linarith [hp.two_lt_s,hp.mother.s_le_kappa3,hp.mother.kappa3_lt_kappa2]
  have hk1 : 0<p.kappa1 := by linarith [hp.mother.kappa2_lt_kappa1]
  have hk20 : 0<p.kappa2 := by linarith
  have hS : 0<p.S := by linarith [hp.three_le_S]
  have hv1 : 0<v+1 := by linarith [hv.1]
  have hv2 : 0<v+2 := by linarith [hv.1]
  have hhalf : (1:ℝ)/2≤1-1/p.kappa2 := by
    have h : 1/p.kappa2≤(1:ℝ)/2 := (div_le_iff₀ hk20).mpr (by linarith)
    linarith
  have hl : 1/p.S≤(1-1/p.kappa2)/(v+1) := by
    apply (div_le_div_iff₀ hS hv1).mpr
    have h := hv.2
    unfold lowerSwitch at h
    linarith
  have hh : 1/(2*(v+1))≤(1-1/p.kappa2)/(v+1) := by
    simpa only [div_div] using div_le_div_of_nonneg_right hhalf hv1.le
  have he : (1-1/p.kappa1)*p.kappa1=p.kappa1-1 := by field_simp
  have hu : (1-1/p.kappa1)/(v+1)≤1/p.kappa1 := by
    apply (div_le_div_iff₀ hv1 hk1).mpr
    rw [he]
    have h := hv.1
    unfold upperSwitch at h
    linarith
  have hu2 : (1-1/p.kappa1)/(v+1)≤1/(v+2) := by
    apply (div_le_div_iff₀ hv1 hv2).mpr
    apply le_of_mul_le_mul_right ?_ hk1
    have h := hv.1
    unfold upperSwitch at h
    calc
      (1-1/p.kappa1)*(v+2)*p.kappa1=(p.kappa1-1)*(v+2) := by rw [mul_right_comm,he]
      _≤(1*(v+1))*p.kappa1 := by nlinarith
  simp only [feedbackLower,feedbackUpper,upperP,upperQ,lowerQ]
  exact ⟨by rw [max_eq_left hh,max_eq_right hl],
    by rw [min_eq_left hu2,min_eq_right hu]⟩

theorem middle_ratio_eq {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (ha : 1≤upperSwitch p) {v : ℝ}
    (hv : v∈Icc (upperSwitch p) (lowerSwitch p)) :
    ratio (feedbackPole p .gammaEight v) (feedbackLower p .gammaEight v)
      (feedbackUpper p .gammaEight v)=middleRatio p := by
  obtain ⟨hl,hu⟩ := middle_geometry hp ha hv
  have hk2 : 1<p.kappa2 := by
    linarith [hp.two_lt_s,hp.mother.s_le_kappa3,hp.mother.kappa3_lt_kappa2]
  have hk1 : 0<p.kappa1 := by linarith [hp.mother.kappa2_lt_kappa1]
  have hv1 : v+1≠0 := by linarith [hv.1]
  rw [hl,hu]
  simp only [feedbackPole,ratio,middleRatio]
  field_simp [hk1.ne',ne_of_gt (by linarith : 0<p.kappa2),hv1,
    ne_of_gt (sub_pos.mpr hk2)]
  ring

theorem middle_log_pos {p : SecondFunctionalParameters} (hp : AnalyticParameters p) :
    0<log (middleRatio p) := by
  apply log_pos
  unfold middleRatio
  apply (one_lt_div (by linarith [hp.two_lt_s,hp.mother.s_le_kappa3,
    hp.mother.kappa3_lt_kappa2] : 0<p.kappa2-1)).mpr
  linarith [hp.mother.kappa2_lt_kappa1]

/-- Both ends of the original closed middle segment have an active strict gate. -/
theorem middle_kernel_eq {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (ha : 1≤upperSwitch p) (hb : lowerSwitch p≤3) {v : ℝ}
    (hv : v∈Icc (upperSwitch p) (lowerSwitch p)) :
    feedbackLogKernel p .gammaEight v=log (middleRatio p)/v := by
  obtain ⟨hl,hu⟩ := middle_geometry hp ha hv
  have hk2 : 0<p.kappa2 := by
    linarith [hp.two_lt_s,hp.mother.s_le_kappa3,hp.mother.kappa3_lt_kappa2]
  have hv1 : 0<v+1 := by linarith [hv.1]
  have hgate : feedbackLower p .gammaEight v<feedbackUpper p .gammaEight v := by
    rw [hl,hu]
    apply (div_lt_div_iff_of_pos_right hv1).mpr
    have h := one_div_lt_one_div_of_lt hk2 hp.mother.kappa2_lt_kappa1
    linarith
  rw [feedbackLogKernel,if_pos ⟨⟨ha.trans hv.1,hv.2.trans hb⟩,hgate⟩]
  change feedbackFactor p .gammaEight v*log (ratio (feedbackPole p .gammaEight v)
    (feedbackLower p .gammaEight v) (feedbackUpper p .gammaEight v))=_
  rw [middle_ratio_eq hp ha hv]
  simp only [feedbackFactor]
  ring

/-- Exact payment on the original two branch meetings; no endpoint enclosure. -/
def middlePayment (p : SecondFunctionalParameters) : ℝ :=
  log (middleRatio p)*(log (lowerSwitch p)-log (upperSwitch p))

theorem middle_integral {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (ha : 1≤upperSwitch p) (hab : upperSwitch p≤lowerSwitch p) (hb : lowerSwitch p≤3) :
    (∫ v in (upperSwitch p)..(lowerSwitch p),feedbackLogKernel p .gammaEight v)=
      middlePayment p := by
  have hcon : ContinuousOn (fun v : ℝ => log (middleRatio p)/v)
      (uIcc (upperSwitch p) (lowerSwitch p)) := by
    rw [uIcc_of_le hab]
    intro v hv
    apply ContinuousAt.continuousWithinAt
    have hv0 : v≠0 := by linarith [hv.1]
    fun_prop (disch := assumption)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v : ℝ => log (middleRatio p)*log v)
    (f' := fun v : ℝ => log (middleRatio p)/v)
    (a := upperSwitch p) (b := lowerSwitch p)
    (fun v hv => by
      rw [uIcc_of_le hab] at hv
      have hv0 : v≠0 := by linarith [hv.1]
      simpa only [div_eq_mul_inv] using (hasDerivAt_log hv0).const_mul (log (middleRatio p)))
    hcon.intervalIntegrable
  rw [intervalIntegral.integral_congr (fun v hv =>
    middle_kernel_eq hp ha hb (by simpa only [uIcc_of_le hab] using hv)),he]
  unfold middlePayment
  ring

end
end CoupledMiddleGateRecovery
