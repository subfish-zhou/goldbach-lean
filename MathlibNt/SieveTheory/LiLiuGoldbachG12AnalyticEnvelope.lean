import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpMassIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachS3CorrectionEvaluation

noncomputable section
open MeasureTheory Set
open scoped Interval
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open G12SharpQuadrature

namespace G12AnalyticCertificate

/-- The source degree-33 logarithmic envelope, with both inverse powers retained. -/
def upperDensity (u : ℝ) : ℝ :=
  (1/(4/33 : ℝ) + (S3Correction.L ((4/33 : ℝ)/u-1)-1)/u)/u

/-- This bound is pointwise on the whole original interval, not sampled. -/
theorem density_le_upperDensity {u : ℝ} (hu : u ∈ Icc (4/53 : ℝ) (4/33)) :
    density u ≤ upperDensity u := by
  have hp : 0 < u := by linarith [hu.1]
  have hx : 0 ≤ (4/33 : ℝ)/u-1 := by
    apply sub_nonneg.mpr
    exact (le_div_iff₀ hp).2 (by simpa using hu.2)
  have h := S3Correction.log_le_L hx
  rw [show (1 : ℝ)+((4/33 : ℝ)/u-1) = (4/33 : ℝ)/u by ring] at h
  exact div_le_div_of_nonneg_right
    (add_le_add_right (div_le_div_of_nonneg_right (sub_le_sub_right h 1) hp.le) _) hp.le

/-- Positivity is needed before replacing the external logarithmic factor. -/
theorem density_nonneg {u : ℝ} (hu : u ∈ Icc (4/53 : ℝ) (4/33)) :
    0 ≤ density u := by
  have hp : 0 < u := by linarith [hu.1]
  have h := Real.one_sub_inv_le_log_of_pos
    (div_pos (by norm_num : (0 : ℝ) < 4/33) hp)
  have hi : ((4/33 : ℝ)/u)⁻¹ = u/(4/33) := by simp [inv_div]
  rw [hi] at h
  have hd : 0 ≤ 1/(4/33 : ℝ) + (Real.log ((4/33 : ℝ)/u)-1)/u := by
    have ht : -(1/(4/33 : ℝ)) ≤ (Real.log ((4/33 : ℝ)/u)-1)/u := by
      apply (le_div_iff₀ hp).2
      nlinarith
    linarith
  exact div_nonneg hd hp.le

theorem continuousOn_upperDensity :
    ContinuousOn upperDensity (Icc (4/53 : ℝ) (4/33)) := by
  have hn : ∀ u ∈ Icc (4/53 : ℝ) (4/33), u ≠ 0 := by
    intro u hu
    linarith [hu.1]
  have hL : Continuous S3Correction.L :=
    continuous_iff_continuousAt.mpr (fun x => (S3Correction.L_deriv x).continuousAt)
  unfold upperDensity
  exact (continuousOn_const.add (((hL.comp_continuousOn
    ((continuousOn_const.div continuousOn_id hn).sub continuousOn_const)).sub
      continuousOn_const).div continuousOn_id hn)).div continuousOn_id hn

theorem low_continuous (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (4/53 : ℝ) (4/33))) :
    ContinuousOn (fun u => f u / (1-u)) (Icc (4/53 : ℝ) (1/10)) := by
  exact (hf.mono (Icc_subset_Icc le_rfl (by norm_num))).div
    (continuousOn_const.sub continuousOn_id) (fun u hu => by dsimp; linarith [hu.2])

/-- A logarithm-free rational-function upper integral; the original low factor is retained. -/
def upperMass : ℝ :=
  (561990/1000000 : ℝ) * (36/5) *
    (∫ u in (4/53 : ℝ)..(1/10), upperDensity u / (1-u)) +
  (564383/1000000 : ℝ) * 8 *
    (∫ u in (1/10 : ℝ)..(4/33), upperDensity u)

theorem upperMass_nonneg : 0 ≤ upperMass := by
  have hlow : 0 ≤ ∫ u in (4/53 : ℝ)..(1/10), upperDensity u / (1-u) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    have hu' : u ∈ Icc (4/53 : ℝ) (4/33) := ⟨hu.1, by linarith [hu.2]⟩
    exact div_nonneg ((density_nonneg hu').trans (density_le_upperDensity hu'))
      (by linarith [hu.2])
  have hhigh : 0 ≤ ∫ u in (1/10 : ℝ)..(4/33), upperDensity u := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    have hu' : u ∈ Icc (4/53 : ℝ) (4/33) := ⟨by linarith [hu.1], hu.2⟩
    exact (density_nonneg hu').trans (density_le_upperDensity hu')
  unfold upperMass
  positivity

/-- Direct consumption of the production sharp split; no mother mass is reconstructed. -/
theorem sharp_le_log_mul_upperMass :
    goldbachG12SharpIntegralConstant ≤ Real.log (9/4 : ℝ) * upperMass := by
  have hlo := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (4/53 : ℝ) ≤ 1/10)
    ((low_continuous density continuousOn_density).intervalIntegrable_of_Icc (by norm_num))
    ((low_continuous upperDensity continuousOn_upperDensity).intervalIntegrable_of_Icc
      (by norm_num)) (fun u hu => div_le_div_of_nonneg_right
        (density_le_upperDensity ⟨hu.1, by linarith [hu.2]⟩) (by linarith [hu.2]))
  have hhi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (1/10 : ℝ) ≤ 4/33)
    ((continuousOn_density.mono (Icc_subset_Icc (by norm_num) le_rfl)).intervalIntegrable_of_Icc
      (by norm_num))
    ((continuousOn_upperDensity.mono (Icc_subset_Icc (by norm_num) le_rfl)).intervalIntegrable_of_Icc
      (by norm_num)) (fun u hu => density_le_upperDensity ⟨by linarith [hu.1], hu.2⟩)
  unfold goldbachG12SharpIntegralConstant
  rw [sharp_integral_split]
  apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num))
  exact add_le_add (mul_le_mul_of_nonneg_left hlo (by norm_num))
    (mul_le_mul_of_nonneg_left hhi (by norm_num))

theorem external_log_le : Real.log (9/4 : ℝ) ≤ 2*S3Correction.L (1/2) := by
  have h := S3Correction.log_le_L (by norm_num : (0 : ℝ) ≤ 1/2)
  have he : Real.log (9/4 : ℝ) = 2*Real.log (3/2 : ℝ) := by
    rw [show (9/4 : ℝ) = (3/2)^2 by norm_num, Real.log_pow]
    norm_num
  rw [he]
  norm_num at h
  linarith

/-- Unconditional analytic upper bound, with no logarithms in its defining integrands. -/
theorem sharp_le_rationalIntegral :
    goldbachG12SharpIntegralConstant ≤ (2*S3Correction.L (1/2))*upperMass :=
  sharp_le_log_mul_upperMass.trans
    (mul_le_mul_of_nonneg_right external_log_le upperMass_nonneg)

end G12AnalyticCertificate
