import Hf4NextDensity

noncomputable section
namespace Hf4Next
open Real Set MeasureTheory SigmaEndpointPayment
open scoped Interval

/-- Exact amplification obtained by cancelling the moving denominator first. -/
def amplification (b : ℝ) : ℝ := F1LowerResidual.denom ((b+1)/2)/160

theorem factor_identity {b : ℝ} (hb : 1 ≤ b) :
    coupledCellFactor b = amplification b*residualCellFactor b := by
  have hd := residual_denom_pos (show 1 ≤ (b+1)/2 by linarith)
  unfold coupledCellFactor amplification residualCellFactor
  field_simp
  ring

theorem amplification_ge_one {b : ℝ} (hb : 1 ≤ b) : 1 ≤ amplification b := by
  have h := residual_denom_mono (x := 1) (B := (b+1)/2) le_rfl (by linarith)
  norm_num [F1LowerResidual.denom] at h
  unfold amplification F1LowerResidual.denom
  linarith only [h]

theorem amplification_gt_one {b : ℝ} (hb : 1 < b) : 1 < amplification b := by
  let x := (b+1)/2
  have hx : 1 < x := by dsimp [x]; linarith
  have hden : 160 < F1LowerResidual.denom x := by
    calc
      (160:ℝ) = (1:ℝ)^2*(1+1)^4*(1^2+8*1+1) := by norm_num
      _ < x^2*(x+1)^4*(x^2+8*x+1) := by gcongr
      _ = _ := rfl
  change 1 < F1LowerResidual.denom x/160
  linarith only [hden]

/-- Explicit finite payment, on the unchanged old cell. -/
def cellPayment (a b : ℝ) : ℝ :=
  coupledCellFactor b*((b-1)^9-(a-1)^9)/(72*b)

theorem cellPayment_eq_amplified {a b : ℝ} (hb : 1 ≤ b) :
    cellPayment a b = amplification b*SigmaEndpointPayment.cellPayment a b := by
  unfold cellPayment SigmaEndpointPayment.cellPayment
  rw [factor_identity hb]
  ring

theorem old_cellPayment_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    SigmaEndpointPayment.cellPayment a b ≤ cellPayment a b := by
  rw [cellPayment_eq_amplified (ha.trans hab)]
  exact le_mul_of_one_le_left (SigmaEndpointPayment.cellPayment_nonneg ha hab)
    (amplification_ge_one (ha.trans hab))

theorem cellPayment_nonneg {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ cellPayment a b :=
  (SigmaEndpointPayment.cellPayment_nonneg ha hab).trans (old_cellPayment_le ha hab)

theorem old_cellPayment_lt {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) :
    SigmaEndpointPayment.cellPayment a b < cellPayment a b := by
  have hp : 0 < SigmaEndpointPayment.cellPayment a b := by
    have hb : 1 < b := ha.trans_lt hab
    have hc := residualCellFactor_pos (ha.trans hab.le)
    have hpow : (a-1)^9 < (b-1)^9 := by gcongr
    unfold SigmaEndpointPayment.cellPayment
    positivity
  rw [cellPayment_eq_amplified (ha.trans hab.le)]
  exact lt_mul_of_one_lt_left hp (amplification_gt_one (ha.trans_lt hab))

/-- Reuse the already-paid seventh moment, with the new density estimate. -/
theorem variationMass_lower {t b : ℝ} (ht : 1 ≤ t) (htb : t ≤ b) :
    coupledCellFactor b*(t-1)^8/8 ≤ CorrectionSigmaVariable.variationMass t := by
  have hi : IntervalIntegrable (fun v : ℝ => coupledCellFactor b*(t+2-v)^7)
      volume 3 (t+2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hm := intervalIntegral.integral_mono_on (by linarith : (3:ℝ) ≤ t+2) hi
    (CorrectionSigmaVariable.variation_integrable ht)
    (fun v hv => Hf4Next.variation_density_lower ht htb hv)
  rw [intervalIntegral.integral_const_mul, SigmaEndpointPayment.inner_moment] at hm
  simpa only [CorrectionSigmaVariable.variationMass,mul_div_assoc] using hm

/-- The old outer polynomial is reused, not rebuilt or renamed as an FTC. -/
theorem amplified_outer_lower {t b : ℝ} (ht : 1 ≤ t) (htb : t ≤ b) :
    amplification b*outerResidual b t ≤ CorrectionSigmaVariable.variationMass t/t := by
  have hb : 1 ≤ b := ht.trans htb
  have hc := (coupledCellFactor_pos hb).le
  have hn : 0 ≤ coupledCellFactor b*(t-1)^8/8 := by positivity
  calc
    _ = (coupledCellFactor b*(t-1)^8/8)/b := by
      rw [factor_identity hb]
      unfold outerResidual
      ring
    _ ≤ (coupledCellFactor b*(t-1)^8/8)/t :=
      div_le_div_of_nonneg_left hn (by linarith) htb
    _ ≤ _ := div_le_div_of_nonneg_right (Hf4Next.variationMass_lower ht htb) (by linarith)

/-- Actual consumer of the new coupled density, reusing the frozen outer FTC. -/
theorem old_cell_add_payment_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    SigmaInnerProfile.cellIntegral a b + cellPayment a b ≤ SigmaVariableFull.cellMass a b := by
  have hi : IntervalIntegrable SigmaInnerProfile.weight volume a b :=
    (SigmaInnerProfile.weight_continuous (by linarith : 0<a) hab).intervalIntegrable
  have hj : IntervalIntegrable (outerResidual b) volume a b := by
    apply Continuous.intervalIntegrable
    unfold outerResidual
    fun_prop
  have hf : IntervalIntegrable SigmaVariableFull.weight volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro t ht
    have ht' : t ∈ Icc (1:ℝ) 3 := ⟨ha.trans ht.1,ht.2.trans hb⟩
    exact ((SigmaVariableFull.endpointMass_continuousAt ht').div continuousAt_id
      (show id t ≠ 0 by dsimp; linarith [ht'.1])).continuousWithinAt
  have hm := intervalIntegral.integral_mono_on hab (hi.add (hj.const_mul (amplification b))) hf
    (fun t ht => show SigmaInnerProfile.weight t + amplification b*outerResidual b t ≤
      SigmaVariableFull.weight t from by
        have ht' : t ∈ Icc (1:ℝ) 3 := ⟨ha.trans ht.1, ht.2.trans hb⟩
        rw [SigmaVariableFull.weight, SigmaVariableFull.endpointMass_eq ht',
          SigmaVariableFull.innerMass_balance ht', add_div]
        exact add_le_add le_rfl (amplified_outer_lower ht'.1 ht.2))
  rw [intervalIntegral.integral_add hi (hj.const_mul _),
    intervalIntegral.integral_const_mul, outerResidual_integral] at hm
  rw [cellPayment_eq_amplified (ha.trans hab)]
  exact hm

end Hf4Next
