import FeedbackAlgebra
import MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainSource
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalSignedSource

namespace ActualNineFeedback
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension
open scoped Interval BigOperators

noncomputable def profileJ (z : Fin 9 → ℝ) (s S : ℝ) : ℝ :=
  ∫ u in (1 - 1 / s)..(1 - 1 / S),
    gProfile (nineProfile z) (S * u) / (u * (1 - u))

theorem gProfile_continuous (z : Fin 9 → ℝ) :
    ContinuousOn (gProfile (nineProfile z)) (Icc 2 4) := by
  have hi := profile_div_integrable (nineProfile_integrable z)
  have hc := intervalIntegral.continuousOn_primitive_interval_left
    ((intervalIntegrable_iff' (by finiteness)).mp hi)
  have hcomp : ContinuousOn (fun u => ∫ t in (u - 1)..3, nineProfile z t / t)
      (Icc 2 4) := by
    apply hc.comp (continuousOn_id.sub continuousOn_const)
    intro u hu
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
    change 1 ≤ u - 1 ∧ u - 1 ≤ 3
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  exact continuousOn_const.add hcomp

theorem gProfile_expansion (z : Fin 9 → ℝ) {u : ℝ} (hu : u ∈ Icc 2 4) :
    gProfile (nineProfile z) u =
      ∑ k : Fin 9, z k * gProfile (nineProfile (nodeBasis k)) u := by
  unfold gProfile
  rw [aProfile_expansion]
  have he := weighted_profile_expansion z (by linarith [hu.1] : 1 ≤ u - 1)
    (by linarith [hu.2] : u - 1 ≤ 3)
    (reciprocal_continuous (by linarith [hu.1] : 0 < u - 1) (by linarith [hu.2]))
  simp only [mul_one_div] at he
  rw [he, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem J_geometry {s S : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S - S / s) :
    1 - 1 / s ≤ 1 - 1 / S ∧
    ∀ u ∈ Icc (1 - 1 / s) (1 - 1 / S),
      0 < u ∧ u < 1 ∧ S * u ∈ Icc 2 4 := by
  have hs0 : 0 < s := by linarith
  have hS0 : 0 < S := by linarith
  have hinv : 1 / S ≤ 1 / s := one_div_le_one_div_of_le hs0 hsS
  refine ⟨by linarith, ?_⟩
  intro u hu
  have hinvs : 1 / s ≤ (1 : ℝ) / 2 := one_div_le_one_div_of_le (by norm_num) hs
  have hlo := mul_le_mul_of_nonneg_left hu.1 hS0.le
  have hhi := mul_le_mul_of_nonneg_left hu.2 hS0.le
  have hnorm : S * (1 - 1 / S) = S - 1 := by field_simp
  rw [hnorm] at hhi
  have hnorm2 : S * (1 - 1 / s) = S - S / s := by ring
  rw [hnorm2] at hlo
  exact ⟨by linarith [hu.1], by linarith [hu.2, one_div_pos.mpr hS0],
    hr.trans hlo, by linarith⟩

theorem profileJ_integrable (z : Fin 9 → ℝ) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S - S / s) :
    IntervalIntegrable (fun u => gProfile (nineProfile z) (S * u) / (u * (1 - u)))
      volume (1 - 1 / s) (1 - 1 / S) := by
  have hg := J_geometry hs hS hS5 hsS hr
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hg.1]
  apply ContinuousOn.div
  · exact (gProfile_continuous z).comp (continuousOn_const.mul continuousOn_id)
      (fun u hu => (hg.2 u hu).2.2)
  · exact continuousOn_id.mul (continuousOn_const.sub continuousOn_id)
  · intro u hu
    exact ne_of_gt (mul_pos (hg.2 u hu).1 (by linarith [(hg.2 u hu).2.1]))

theorem profileJ_nonneg {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S - S / s) : 0 ≤ profileJ z s S := by
  have hg := J_geometry hs hS hS5 hsS hr
  apply intervalIntegral.integral_nonneg hg.1
  intro u hu
  exact div_nonneg ((profiles_nonneg (fun t _ => nineProfile_nonneg hz t)).2.1 _
    (hg.2 u hu).2.2) (mul_nonneg (hg.2 u hu).1.le (by linarith [(hg.2 u hu).2.1]))

theorem profileJ_expansion (z : Fin 9 → ℝ) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S - S / s) :
    profileJ z s S = ∑ k : Fin 9, z k * profileJ (nodeBasis k) s S := by
  have hg := J_geometry hs hS hS5 hsS hr
  unfold profileJ
  calc
    _ = ∫ u in (1 - 1 / s)..(1 - 1 / S),
        ∑ k : Fin 9, z k *
          (gProfile (nineProfile (nodeBasis k)) (S * u) / (u * (1 - u))) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hg.1] at hu
      dsimp only
      rw [gProfile_expansion z (hg.2 u hu).2.2, Finset.sum_div]
      simp only [mul_div_assoc]
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum]
      · simp only [intervalIntegral.integral_const_mul]
      · intro k _
        exact (profileJ_integrable (nodeBasis k) hs hS hS5 hsS hr).const_mul _

theorem density_integrable (p : SecondFunctionalParameters) (hp : MotherPair.AnalyticParameters p) :
    Integrable (SecondFunctionalCoupledFeedback.density p) := by
  exact (((MotherPair.feedback_log_integrable hp .gammaFive).add
    (MotherPair.feedback_log_integrable hp .gammaSix)).add
    (MotherPair.feedback_log_integrable hp .gammaSeven)).add
    (MotherPair.feedback_log_integrable hp .gammaEight)

theorem density_profile_integrable (p : SecondFunctionalParameters)
    (hp : MotherPair.AnalyticParameters p) (z : Fin 9 → ℝ) :
    IntervalIntegrable (fun v => nineProfile z v * SecondFunctionalCoupledFeedback.density p v)
      volume 1 3 := by
  have hi : Integrable (fun v => nineProfile z v * SecondFunctionalCoupledFeedback.density p v) := by
    have he : (fun v => nineProfile z v * SecondFunctionalCoupledFeedback.density p v) =
        fun v => ∑ k : Fin 9, (Ioc (upperLeft k) (upperNode k)).indicator
          (fun v => z k * SecondFunctionalCoupledFeedback.density p v) v := by
      funext v
      unfold nineProfile
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hv : v ∈ Ioc (upperLeft k) (upperNode k) <;> simp [hv]
    rw [he]
    apply integrable_finsetSum
    intro k _
    exact ((density_integrable p hp).const_mul (z k)).indicator measurableSet_Ioc
  exact hi.intervalIntegrable

noncomputable def densityMoment (p : SecondFunctionalParameters) (z : Fin 9 → ℝ) : ℝ :=
  ∫ v in (1 : ℝ)..3, nineProfile z v * SecondFunctionalCoupledFeedback.density p v

theorem densityMoment_expansion (p : SecondFunctionalParameters)
    (hp : MotherPair.AnalyticParameters p) (z : Fin 9 → ℝ) :
    densityMoment p z = ∑ k : Fin 9, z k * densityMoment p (nodeBasis k) := by
  unfold densityMoment
  have he (v : ℝ) : nineProfile z v * SecondFunctionalCoupledFeedback.density p v =
      ∑ k : Fin 9, z k * (nineProfile (nodeBasis k) v * SecondFunctionalCoupledFeedback.density p v) := by
    rw [nineProfile_expansion, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul]
  · intro k _
    exact (density_profile_integrable p hp (nodeBasis k)).const_mul _

theorem profileJ_le_actual {δ s S : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S - S / s) :
    profileJ (actualNine δ) s S ≤ SecondFunctionalSignedCore.lowerGain δ s S := by
  have hg := J_geometry hs hS hS5 hsS hr
  apply intervalIntegral.integral_mono_on hg.1
    (profileJ_integrable _ hs hS hS5 hsS hr)
    (firstFunctionalGain_limit_intervalIntegrable hd (by linarith) hs hsS hS hS5)
  intro u hu
  exact div_le_div_of_nonneg_right
    ((actual_nine_extension hd hh).2.2.1 _ (hg.2 u hu).2.2)
    (mul_nonneg (hg.2 u hu).1.le (by linarith [(hg.2 u hu).2.1]))

theorem densityMoment_nonneg (p : SecondFunctionalParameters)
    (hp : MotherPair.AnalyticParameters p) {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    0 ≤ densityMoment p z := by
  apply intervalIntegral.integral_nonneg (by norm_num : (1 : ℝ) ≤ 3)
  intro v _
  exact mul_nonneg (nineProfile_nonneg hz v)
    (SecondFunctionalCoupledFeedback.density_nonnegative p hp v)

theorem densityMoment_le_actual (p : SecondFunctionalParameters)
    (hp : MotherPair.AnalyticParameters p) {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10) :
    densityMoment p (actualNine δ) ≤
      ∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v * SecondFunctionalCoupledFeedback.density p v := by
  have hh' : δ < 1 / 2 := by linarith
  have h5 := MotherPair.feedback_log_actual_integrable hp .gammaFive hd hh'
  have h6 := MotherPair.feedback_log_actual_integrable hp .gammaSix hd hh'
  have h7 := MotherPair.feedback_log_actual_integrable hp .gammaSeven hd hh'
  have h8 := MotherPair.feedback_log_actual_integrable hp .gammaEight hd hh'
  have hi : IntervalIntegrable (fun v => wuImprovementLimit true δ v *
      SecondFunctionalCoupledFeedback.density p v) volume 1 3 := by
    simpa only [SecondFunctionalCoupledFeedback.density, mul_add] using ((h5.add h6).add h7).add h8
  apply intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 3)
    (density_profile_integrable p hp _) hi
  intro v hv
  exact mul_le_mul_of_nonneg_right (nineProfile_le_actual hd hh hv)
    (SecondFunctionalCoupledFeedback.density_nonnegative p hp v)

end ActualNineFeedback
