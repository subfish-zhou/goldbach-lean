import SigmaVariationFiniteDensity

noncomputable section
namespace SigmaEndpointPayment
open Real Set MeasureTheory
open scoped Interval

/-- The exponent comes from the existing seventh-order residual, not a chosen expansion. -/
theorem inner_moment (t : ℝ) :
    (∫ v in (3:ℝ)..t+2, (t+2-v)^7) = (t-1)^8/8 := by
  have hd (v : ℝ) : HasDerivAt (fun w : ℝ => -(t+2-w)^8/8) ((t+2-v)^7) v := by
    convert ((((hasDerivAt_id v).const_sub (t+2)).pow 8).neg.div_const 8) using 1 <;>
      first | rfl | (dsimp; ring)
  have hi : IntervalIntegrable (fun v : ℝ => (t+2-v)^7) volume 3 (t+2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v) hi]
  ring

theorem variationMass_lower {t b : ℝ} (ht : 1 ≤ t) (htb : t ≤ b) :
    residualCellFactor b*(t-1)^8/8 ≤ CorrectionSigmaVariable.variationMass t := by
  have hi : IntervalIntegrable (fun v : ℝ => residualCellFactor b*(t+2-v)^7)
      volume 3 (t+2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hm := intervalIntegral.integral_mono_on (by linarith : (3:ℝ) ≤ t+2) hi
    (CorrectionSigmaVariable.variation_integrable ht)
    (fun v hv => variation_density_lower ht htb hv)
  rw [intervalIntegral.integral_const_mul,inner_moment] at hm
  simpa only [CorrectionSigmaVariable.variationMass,mul_div_assoc] using hm

def outerResidual (b t : ℝ) : ℝ := residualCellFactor b*(t-1)^8/(8*b)

theorem outerResidual_lower {t b : ℝ} (ht : 1 ≤ t) (htb : t ≤ b) :
    outerResidual b t ≤ CorrectionSigmaVariable.variationMass t/t := by
  have hb : 1 ≤ b := ht.trans htb
  have hc := (residualCellFactor_pos hb).le
  have hn : 0 ≤ residualCellFactor b*(t-1)^8/8 := by positivity
  calc
    _ = (residualCellFactor b*(t-1)^8/8)/b := by unfold outerResidual; ring
    _ ≤ (residualCellFactor b*(t-1)^8/8)/t :=
      div_le_div_of_nonneg_left hn (by linarith) htb
    _ ≤ _ := div_le_div_of_nonneg_right (variationMass_lower ht htb) (by linarith)

/-- An explicit finite amount on the unchanged original cell. -/
def cellPayment (a b : ℝ) : ℝ :=
  residualCellFactor b*((b-1)^9-(a-1)^9)/(72*b)

theorem outerResidual_integral (a b : ℝ) :
    (∫ t in a..b, outerResidual b t) = cellPayment a b := by
  have hd (t : ℝ) :
      HasDerivAt (fun u : ℝ => residualCellFactor b*(u-1)^9/(72*b)) (outerResidual b t) t := by
    convert ((((hasDerivAt_id t).sub_const 1).pow 9).const_mul
      (residualCellFactor b)).div_const (72*b) using 1 <;>
      first | rfl | (dsimp [outerResidual]; ring)
  have hi : IntervalIntegrable (outerResidual b) volume a b := by
    apply Continuous.intervalIntegrable
    unfold outerResidual
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
  unfold cellPayment
  ring

theorem cellPayment_nonneg {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ cellPayment a b := by
  have hb := ha.trans hab
  have hc := (residualCellFactor_pos hb).le
  have hp : (a-1)^9 ≤ (b-1)^9 := by gcongr
  unfold cellPayment
  positivity

/-- A genuine lower payment of the same full inner mass, not an endpoint renaming. -/
theorem old_weight_add_outerResidual_le {t b : ℝ} (ht : t ∈ Icc 1 3) (htb : t ≤ b) :
    SigmaInnerProfile.weight t + outerResidual b t ≤ SigmaVariableFull.weight t := by
  rw [SigmaVariableFull.weight,SigmaVariableFull.endpointMass_eq ht,
    SigmaVariableFull.innerMass_balance ht,add_div]
  exact add_le_add le_rfl (outerResidual_lower ht.1 htb)

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
    have h0 : t ≠ 0 := by linarith [ht'.1]
    exact ((SigmaVariableFull.endpointMass_continuousAt ht').div continuousAt_id h0).continuousWithinAt
  have hm := intervalIntegral.integral_mono_on hab (hi.add hj) hf
    (fun t ht => old_weight_add_outerResidual_le ⟨ha.trans ht.1,ht.2.trans hb⟩ ht.2)
  rw [intervalIntegral.integral_add hi hj,outerResidual_integral] at hm
  exact hm

end SigmaEndpointPayment
