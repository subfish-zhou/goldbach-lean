import SigmaVariationHf4Payment

noncomputable section
namespace Hf4Next
open Real Set MeasureTheory SigmaEndpointPayment

/-- Homogeneous cancellation is performed before any denominator is frozen. -/
theorem residual_rescale {s u : ℝ} (hu : u ≠ 0) :
    F1LowerResidual.payment (s/u) =
      (s-u)^7*(5*s+7*u)/(210*(s^2*(s+u)^4*(s^2+8*s*u+u^2))) := by
  unfold F1LowerResidual.payment F1LowerResidual.denom
  field_simp

/-- All four coupled factors are bounded in the same coordinates. -/
theorem coupled_denom_upper {s u : ℝ} (hu : 0 ≤ u) (hus : u ≤ s) :
    s^2*(s+u)^4*(s^2+8*s*u+u^2) ≤ 160*s^8 := by
  have hs : 0 ≤ s := hu.trans hus
  have hq : s^2+8*s*u+u^2 ≤ 10*s^2 := by
    calc
      _ ≤ s^2+8*s*s+s^2 := by gcongr
      _ = _ := by ring
  calc
    _ ≤ s^2*(2*s)^4*(10*s^2) := by gcongr; linarith
    _ = _ := by ring

/-- The numerator and the original v denominator are kept coupled. -/
theorem coupled_ratio_lower {s u : ℝ} (hu : 2 ≤ u) (hus : u ≤ s) :
    12*s/(s+1) ≤ (5*s+7*u)/(u+1) := by
  have hs : 2 ≤ s := hu.trans hus
  apply (div_le_div_iff₀ (by linarith : 0 < s+1) (by linarith : 0 < u+1)).mpr
  nlinarith only [mul_nonneg (sub_nonneg.mpr hus) (show 0 ≤ 5*s-7 by linarith)]

def coupledCellFactor (b : ℝ) : ℝ := 1/(2800*(b+1)^7*(b+2))

theorem coupledCellFactor_pos {b : ℝ} (hb : 1 ≤ b) : 0 < coupledCellFactor b := by
  unfold coupledCellFactor
  positivity

/-- A coordinate-dependent lower bound, before the existing right endpoint is used. -/
theorem coupled_density_lower {t v : ℝ} (ht : 1 ≤ t) (hv : v ∈ Icc 3 (t+2)) :
    coupledCellFactor t*(t+2-v)^7 ≤ CorrectionSigmaVariable.variation t v/v := by
  let s := t+1
  let u := v-1
  have hu : 2 ≤ u := by dsimp [u]; linarith [hv.1]
  have hus : u ≤ s := by dsimp [u,s]; linarith [hv.2]
  have hs : 2 ≤ s := hu.trans hus
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith [hv.1]
  have hq : 0 ≤ (s-u)^7 := pow_nonneg (sub_nonneg.mpr hus) _
  have hd0 : 0 < s^2*(s+u)^4*(s^2+8*s*u+u^2) := by positivity
  have hd := coupled_denom_upper hu0.le hus
  have hr := coupled_ratio_lower hu hus
  have ha : (s-u)^7/(210*(160*s^8)) ≤
      (s-u)^7/(210*(s^2*(s+u)^4*(s^2+8*s*u+u^2))) :=
    div_le_div_of_nonneg_left hq (by positivity) (by gcongr)
  have hm := mul_le_mul ha hr (by positivity : 0 ≤ 12*s/(s+1))
    (by positivity : 0 ≤ (s-u)^7/(210*(s^2*(s+u)^4*(s^2+8*s*u+u^2))))
  have he : coupledCellFactor t*(t+2-v)^7 =
      ((s-u)^7/(210*(160*s^8)))*(12*s/(s+1)) := by
    dsimp [coupledCellFactor,s,u]
    field_simp
    ring
  rw [he]
  apply hm.trans
  have hres := div_le_div_of_nonneg_right (residual_le_variation ht hv) hv0.le
  convert hres using 1
  rw [show (t+1)/(v-1) = s/u from rfl, residual_rescale hu0.ne']
  dsimp [s,u]
  ring

theorem coupledCellFactor_antitone {t b : ℝ} (ht : 1 ≤ t) (htb : t ≤ b) :
    coupledCellFactor b ≤ coupledCellFactor t := by
  have hb : 1 ≤ b := ht.trans htb
  unfold coupledCellFactor
  apply div_le_div_of_nonneg_left zero_le_one (by positivity)
  gcongr

theorem variation_density_lower {t b v : ℝ} (ht : 1 ≤ t) (htb : t ≤ b)
    (hv : v ∈ Icc 3 (t+2)) :
    coupledCellFactor b*(t+2-v)^7 ≤ CorrectionSigmaVariable.variation t v/v := by
  apply le_trans _ (coupled_density_lower ht hv)
  exact mul_le_mul_of_nonneg_right (coupledCellFactor_antitone ht htb)
    (pow_nonneg (by linarith [hv.2]) _)

end Hf4Next
