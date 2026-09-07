import MathlibNt.SieveTheory.LiLiuGoldbachG12AnalyticEnvelope

noncomputable section
open MeasureTheory Set
open scoped Interval
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open G12SharpQuadrature

namespace G12AnalyticCertificate

/-- Analytic remainder bound for the imported polynomial, without coefficient enumeration. -/
theorem L_sub_log_le {x : ℝ} (hx : 0 ≤ x) :
    S3Correction.L x - Real.log (1+x) ≤ x^34/34 := by
  let F : ℝ → ℝ := fun y => y^34/34 - S3Correction.L y + Real.log (1+y)
  have hd : ∀ y ∈ Icc (0 : ℝ) x,
      HasDerivAt F (y^33 - S3Correction.dL y + 1/(1+y)) y := by
    intro y hy
    have hl : HasDerivAt (fun y : ℝ => Real.log (1+y)) (1/(1+y)) y := by
      convert (Real.hasDerivAt_log (by linarith [hy.1] : (1+y) ≠ 0)).comp y
        ((hasDerivAt_id y).const_add 1) using 1 <;> first | rfl | (simp only [mul_one, one_div])
    convert (((hasDerivAt_pow 34 y).div_const 34).sub (S3Correction.L_deriv y)).add hl
      using 1 <;> first | rfl | norm_num
  have hp : ∀ y ∈ Icc (0 : ℝ) x, 0 ≤ y^33 - S3Correction.dL y + 1/(1+y) := by
    intro y hy
    have hpos : 0 < 1+y := by linarith [hy.1]
    have he := S3Correction.L_residual y
    have hi : (1+y)*(y^33-S3Correction.dL y+1/(1+y)) = y^34 := by
      have hcancel : (1+y)*(1/(1+y)) = 1 := by field_simp
      nlinarith only [he, hcancel]
    exact (mul_nonneg_iff_of_pos_left hpos).mp (hi.symm ▸ pow_nonneg hy.1 34)
  have hm : MonotoneOn F (Icc (0 : ℝ) x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => hp y (interior_subset hy))
  have h := hm ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  have hz : F 0 = 0 := by simp [F, S3Correction.L_zero]
  rw [hz] at h
  dsimp [F] at h
  linarith

/-- Exact primitive of the original density, not of an altered continuous weight. -/
def densityPrimitive (u : ℝ) : ℝ :=
  (33/4 : ℝ)*Real.log u + (2-Real.log ((4/33 : ℝ)/u))/u

theorem densityPrimitive_deriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt densityPrimitive (density u) u := by
  have hn : u ≠ 0 := ne_of_gt hu
  have hb : (4/33 : ℝ)/u ≠ 0 := div_ne_zero (by norm_num) hn
  have hq := (hasDerivAt_const u (4/33 : ℝ)).div (hasDerivAt_id u) hn
  have hl := (Real.hasDerivAt_log hb).comp u hq
  have h := ((Real.hasDerivAt_log hn).const_mul (33/4 : ℝ)).add
    (((hasDerivAt_const u (2 : ℝ)).sub hl).div (hasDerivAt_id u) hn)
  convert h using 1 <;> first | rfl | (dsimp [density]; field_simp; ring)

/-- FTC eliminates the full high-branch density integral exactly. -/
theorem high_integral_exact :
    (∫ u in (1/10 : ℝ)..(4/33), density u) =
      densityPrimitive (4/33) - densityPrimitive (1/10) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    rw [uIcc_of_le (by norm_num : (1/10 : ℝ) ≤ 4/33)] at hu
    exact densityPrimitive_deriv (by linarith [hu.1])
  · exact (continuousOn_density.mono (Icc_subset_Icc (by norm_num) le_rfl)).intervalIntegrable_of_Icc
      (by norm_num)

/-- Pullback identity for the rational envelope, including the Jacobian. -/
theorem upperDensity_pullback {x : ℝ} (hx : 0 ≤ x) :
    upperDensity ((4/33)/(1+x)) * ((4/33)/(1+x)^2) =
      (33/4 : ℝ)*(S3Correction.L x - x/(1+x)) := by
  have hn : 1+x ≠ 0 := by linarith
  have he : (4/33 : ℝ)/((4/33)/(1+x))-1 = x := by field_simp; ring
  unfold upperDensity
  rw [he]
  field_simp [hn]
  ring

/-- The low pullback preserves exactly the original factor 1/(1-u). -/
theorem upperDensity_low_pullback {x : ℝ} (hx : 0 ≤ x) :
    (upperDensity ((4/33)/(1+x)) / (1-(4/33)/(1+x))) * ((4/33)/(1+x)^2) =
      (33/4 : ℝ)*((1+x)*S3Correction.L x-x)/(x+29/33) := by
  have hn : 1+x ≠ 0 := by linarith
  have hm : x+29/33 ≠ 0 := by linarith
  have h29 : 29+x*33 ≠ 0 := by linarith
  have he : (4/33 : ℝ)/((4/33)/(1+x))-1 = x := by field_simp; ring
  unfold upperDensity
  rw [he]
  field_simp [hn, hm, h29]
  ring_nf
  field_simp [h29]
  ring

end G12AnalyticCertificate
