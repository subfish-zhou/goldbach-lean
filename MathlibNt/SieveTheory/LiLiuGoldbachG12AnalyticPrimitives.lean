import MathlibNt.SieveTheory.LiLiuGoldbachG12AnalyticEnvelope

noncomputable section
open MeasureTheory Set
open scoped Interval
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open G12SharpQuadrature

namespace G12AnalyticCertificate


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
