import MathlibNt.Wu2008DoubleSieve.MotherPairGainIntegral
import MathlibNt.Wu2008DoubleSieve.Gamma5GainRectangleIntegral

namespace Wu2008DoubleSieve.MotherPair
open Set Real Filter MeasureTheory
open scoped Classical Topology Interval

/-- A continuous extension of the reciprocal mass density, not of the monotone H. -/
noncomputable def gainSmooth (p : SecondFunctionalParameters) (v : ℝ × ℝ) : ℝ :=
  1 / (max (1/p.S) v.1 * max (1/p.S) v.2 *
    max (1-2*(1/p.kappa3)) (1-v.1-v.2))

theorem gain_smooth_den_pos {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (v : ℝ × ℝ) : 0 < max (1/p.S) v.1 * max (1/p.S) v.2 *
    max (1-2*(1/p.kappa3)) (1-v.1-v.2) := by
  have he := gain_endpoint_order h .gammaFive
  have ha : 0 < 1/p.S := by linarith [he.1]
  have hg : 0 < 1-2*(1/p.kappa3) := by linarith [he.2.2.2.2.2.2]
  exact mul_pos (mul_pos (ha.trans_le (le_max_left _ _))
    (ha.trans_le (le_max_left _ _))) (hg.trans_le (le_max_left _ _))

theorem gain_smooth_continuous {p : SecondFunctionalParameters} (h : AnalyticParameters p) :
    Continuous (gainSmooth p) :=
  continuous_const.div (by fun_prop) (fun v => (gain_smooth_den_pos h v).ne')

theorem gain_smooth_bounds {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (v : ℝ × ℝ) : 0 ≤ gainSmooth p v ∧ gainSmooth p v ≤ 25/(1-2*(1/p.kappa3)) := by
  have he := gain_endpoint_order h .gammaFive
  have hx : (1/5:ℝ) ≤ max (1/p.S) v.1 := he.1.trans (le_max_left _ _)
  have hy : (1/5:ℝ) ≤ max (1/p.S) v.2 := he.1.trans (le_max_left _ _)
  have hg : 0 < 1-2*(1/p.kappa3) := by linarith [he.2.2.2.2.2.2]
  have hp : (1/25:ℝ) ≤ max (1/p.S) v.1 * max (1/p.S) v.2 := by
    nlinarith [mul_le_mul hx hy (by norm_num) (by linarith)]
  have hd := mul_le_mul hp (le_max_left (1-2*(1/p.kappa3)) (1-v.1-v.2))
    hg.le (by positivity : 0 ≤ max (1/p.S) v.1 * max (1/p.S) v.2)
  refine ⟨(one_div_pos.mpr (gain_smooth_den_pos h v)).le, ?_⟩
  exact (one_div_le_one_div_of_le (mul_pos (by norm_num) hg) hd).trans_eq (by field_simp)

theorem gain_smooth_eq {p : SecondFunctionalParameters} {t u : ℝ}
    (ht : t ∈ Icc (1/p.S) (1/p.kappa3)) (hu : u ∈ Icc (1/p.S) (1/p.kappa3)) :
    gainSmooth p (t,u) = 1/(t*u*(1-t-u)) := by
  simp only [gainSmooth, max_eq_right ht.1, max_eq_right hu.1,
    max_eq_right (show 1-2*(1/p.kappa3) ≤ 1-t-u by linarith [ht.2,hu.2])]

theorem gain_smooth_rectangle {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    {j : Term} (r : GainRectangle p j) :
    (∫ t in r.A..r.B, ∫ u in r.C..r.D, gainSmooth p (t,u)) =
      rectIntegral r.A r.B r.C r.D := by
  unfold rectIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc r.A r.B := by simpa only [uIcc_of_le r.A_lt_B.le] using ht
  dsimp only
  rw [max_eq_left (ht'.2.trans r.B_lt_C.le), min_eq_right r.C_lt_D.le]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc r.C r.D := by simpa only [uIcc_of_le r.C_lt_D.le] using hu
  have he := gain_endpoint_order h j
  exact gain_smooth_eq
    ⟨r.lowerP_lt_A.le.trans ht'.1,ht'.2.trans (r.B_lt_upperP.le.trans he.2.2.1)⟩
    ⟨he.2.2.2.1.trans (r.lowerQ_lt_C.le.trans hu'.1),
      hu'.2.trans (r.D_lt_upperQ.le.trans he.2.2.2.2.2.1)⟩

theorem gain_smooth_indicator {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    {j : Term} (r : GainRectangle p j) :
    (∫ v : ℝ × ℝ, (Ico r.A r.B ×ˢ Ico r.C r.D).indicator (gainSmooth p) v) =
      rectIntegral r.A r.B r.C r.D := by
  have hi : IntegrableOn (gainSmooth p) (Ico r.A r.B ×ˢ Ico r.C r.D) :=
    ((gain_smooth_continuous h).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)
  rw [integral_indicator (measurableSet_Ico.prod measurableSet_Ico)]
  rw [show (∫ v in Ico r.A r.B ×ˢ Ico r.C r.D, gainSmooth p v) =
      ∫ t in Ico r.A r.B, ∫ u in Ico r.C r.D, gainSmooth p (t,u) from setIntegral_prod _ hi]
  simp_rw [integral_Ico_eq_integral_Ioc]
  simp_rw [← intervalIntegral.integral_of_le r.C_lt_D.le]
  rw [← intervalIntegral.integral_of_le r.A_lt_B.le]
  exact gain_smooth_rectangle h r

end Wu2008DoubleSieve.MotherPair
