import SigmaActualNineCellFTC

noncomputable section
namespace SigmaEndpointPayment
open Real Set MeasureTheory
open Wu2008DoubleSieve SharpLogRecurrence
open scoped Interval

/-- The denominator of the already proved, unspent inner residual. -/
theorem residual_denom_pos {x : ℝ} (hx : 1 ≤ x) :
    0 < F1LowerResidual.denom x := by
  unfold F1LowerResidual.denom
  positivity

theorem residual_denom_mono {x B : ℝ} (hx : 1 ≤ x) (hB : x ≤ B) :
    F1LowerResidual.denom x ≤ F1LowerResidual.denom B := by
  unfold F1LowerResidual.denom
  gcongr

/-- A uniform algebraic bound, with B supplied by the original cell endpoint. -/
theorem residual_lower {x B : ℝ} (hx : 1 ≤ x) (hB : x ≤ B) :
    (12/(210*F1LowerResidual.denom B))*(x-1)^7 ≤ F1LowerResidual.payment x := by
  have hnum : 12*(x-1)^7 ≤ (x-1)^7*(5*x+7) := by
    have hp : 0 ≤ (x-1)^7 := by positivity
    nlinarith only [mul_nonneg hp (show 0 ≤ 5*x+7-12 by linarith)]
  have hd := residual_denom_mono hx hB
  have hp := residual_denom_pos hx
  calc
    _ = (12*(x-1)^7)/(210*F1LowerResidual.denom B) := by ring
    _ ≤ (12*(x-1)^7)/(210*F1LowerResidual.denom x) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
    _ ≤ _ := div_le_div_of_nonneg_right hnum (by positivity)

/-- No sign loss: the other summand of the actual variation is nonnegative. -/
theorem residual_le_variation {t v : ℝ} (ht : 1 ≤ t) (hv : v ∈ Icc 3 (t+2)) :
    F1LowerResidual.payment ((t+1)/(v-1)) ≤ CorrectionSigmaVariable.variation t v := by
  obtain ⟨hx,hxB⟩ := CorrectionSigmaVariable.argument_bounds ht hv
  have hc := SigmaJEndpoint.coefficient_antitone hx hxB
  have hg : 0 ≤ upperLog ((t+1)/(v-1))-lowerLog ((t+1)/(v-1)) :=
    sub_nonneg.mpr ((log_lower hx).trans (log_upper hx))
  exact le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hc) hg)

/-- Only the actual right endpoint b is used; no new subdivision or order is chosen. -/
def residualCellFactor (b : ℝ) : ℝ :=
  (12/(210*F1LowerResidual.denom ((b+1)/2)))/(b+1)^7/(b+2)

theorem residualCellFactor_pos {b : ℝ} (hb : 1 ≤ b) : 0 < residualCellFactor b := by
  have hd := residual_denom_pos (show 1 ≤ (b+1)/2 by linarith)
  unfold residualCellFactor
  positivity

/-- Pay the entire original inner triangle by a polynomial moment. -/
theorem variation_density_lower {t b v : ℝ} (ht : 1 ≤ t) (htb : t ≤ b)
    (hv : v ∈ Icc 3 (t+2)) :
    residualCellFactor b*(t+2-v)^7 ≤ CorrectionSigmaVariable.variation t v/v := by
  have hb : 1 ≤ b := ht.trans htb
  have hv0 : 0 < v := by linarith [hv.1]
  have hv1 : 0 < v-1 := by linarith [hv.1]
  have hb1 : 0 < b+1 := by linarith
  have hq : 0 ≤ t+2-v := by linarith [hv.2]
  have hx := CorrectionSigmaVariable.argument_bounds ht hv
  have hxb : (t+1)/(v-1) ≤ (b+1)/2 := hx.2.trans (by linarith)
  have hr := residual_lower hx.1 hxb
  have he : (t+1)/(v-1)-1 = (t+2-v)/(v-1) := by field_simp; ring
  rw [he] at hr
  have hbase : (t+2-v)/(b+1) ≤ (t+2-v)/(v-1) :=
    div_le_div_of_nonneg_left hq hv1 (by linarith [hv.2])
  have hd := residual_denom_pos (show 1 ≤ (b+1)/2 by linarith)
  have hmul : (12/(210*F1LowerResidual.denom ((b+1)/2))) *
      ((t+2-v)/(b+1))^7 ≤ CorrectionSigmaVariable.variation t v := by
    apply le_trans (b := F1LowerResidual.payment ((t+1)/(v-1)))
    · apply le_trans (b := (12/(210*F1LowerResidual.denom ((b+1)/2))) *
        ((t+2-v)/(v-1))^7) _ hr
      gcongr
    · exact residual_le_variation ht hv
  have hdiv : ((12/(210*F1LowerResidual.denom ((b+1)/2))) *
      ((t+2-v)/(b+1))^7)/(b+2) ≤ CorrectionSigmaVariable.variation t v/v := by
    apply le_trans (b := ((12/(210*F1LowerResidual.denom ((b+1)/2))) *
      ((t+2-v)/(b+1))^7)/v)
    · apply div_le_div_of_nonneg_left (by positivity) hv0
      linarith [hv.2]
    · exact div_le_div_of_nonneg_right hmul hv0.le
  convert hdiv using 1
  unfold residualCellFactor
  rw [div_pow]
  ring

end SigmaEndpointPayment
