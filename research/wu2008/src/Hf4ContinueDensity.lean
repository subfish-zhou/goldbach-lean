import Hf4ContinueResidual

noncomputable section
namespace Hf4Continue
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals
open scoped Interval

/-- The residual ratio is algebraically forced by the new denominator payment. -/
theorem denominatorPayment_ratio {x : ℝ} (hx : 1 ≤ x) :
    (x-1)/(4*x)*F1LowerResidual.payment x ≤ denominatorPayment x := by
  have hx0 : 0 < x := by linarith
  have hd : 0 < F1LowerResidual.denom x := by unfold F1LowerResidual.denom; positivity
  have he : denominatorPayment x-(x-1)/(4*x)*F1LowerResidual.payment x =
      (x-1)^8/(840*x*F1LowerResidual.denom x) := by
    unfold denominatorPayment F1LowerResidual.payment
    field_simp
    ring
  have hn : 0 ≤ (x-1)^8/(840*x*F1LowerResidual.denom x) := by positivity
  linarith only [he,hn]

/-- Both original coordinates remain coupled; the eighth power is forced, not chosen. -/
theorem new_inner_density_lower {t v : ℝ} (ht : 1 ≤ t) (hv : v ∈ Icc 3 (t+2)) :
    (Hf4Next.coupledCellFactor t/(4*(t+1)))*(t+2-v)^8 ≤
      denominatorPayment ((t+1)/(v-1))/v := by
  have hs : 0 < t+1 := by linarith
  have hu : 0 < v-1 := by linarith [hv.1]
  have hx := (CorrectionSigmaVariable.argument_bounds ht hv).1
  have hratio : (((t+1)/(v-1))-1)/(4*((t+1)/(v-1))) = (t+2-v)/(4*(t+1)) := by
    field_simp
    ring
  have hc : 0 ≤ (t+2-v)/(4*(t+1)) := div_nonneg (by linarith [hv.2]) (by positivity)
  have h1 := mul_le_mul_of_nonneg_left (Hf4Refine.residual_density_lower ht hv) hc
  have h2 := div_le_div_of_nonneg_right (denominatorPayment_ratio hx) (by linarith [hv.1] : 0 ≤ v)
  rw [hratio] at h2
  calc
    _ = ((t+2-v)/(4*(t+1)))*(Hf4Next.coupledCellFactor t*(t+2-v)^7) := by ring
    _ ≤ ((t+2-v)/(4*(t+1)))*(F1LowerResidual.payment ((t+1)/(v-1))/v) := h1
    _ ≤ _ := by simpa only [mul_div_assoc] using h2

theorem new_inner_moment (t : ℝ) :
    (∫ v in (3:ℝ)..t+2, (t+2-v)^8) = (t-1)^9/9 := by
  have hd (v : ℝ) : HasDerivAt (fun w : ℝ => -(t+2-w)^9/9) ((t+2-v)^8) v := by
    convert ((((hasDerivAt_id v).const_sub (t+2)).pow 9).neg).div_const 9 using 1 <;>
      first | rfl | (dsimp; ring)
  have hi : IntervalIntegrable (fun v : ℝ => (t+2-v)^8) volume 3 (t+2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v) hi]
  ring

/-- This is additional to the full basicLower kernel, not an increment of a lower bound alone. -/
theorem full_inner_add_payment_le_sigma {t : ℝ} (ht : t ∈ Icc 1 3) :
    SigmaVariableFull.innerMass t+
      (Hf4Next.coupledCellFactor t/(4*(t+1)))*((t-1)^9/9) ≤ sigma 3 (t+2) (t+1) := by
  have hi : IntervalIntegrable (fun v : ℝ => (t+2-v)^8) volume 3 (t+2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hm := intervalIntegral.integral_mono_on (by linarith [ht.1] : (3:ℝ) ≤ t+2)
    ((SigmaVariableFull.density_integrable ht.1).add (hi.const_mul _))
    (sigma_integrable (by norm_num) (by linarith [ht.1]) (by linarith [ht.1] : 0<t+1))
    (fun v hv => show SigmaVariableFull.density t v+
      (Hf4Next.coupledCellFactor t/(4*(t+1)))*(t+2-v)^8 ≤ log ((t+1)/(v-1))/v from by
        have h1 := new_inner_density_lower ht.1 hv
        have h2 := div_le_div_of_nonneg_right
          (denominatorPayment_le (CorrectionSigmaVariable.argument_bounds ht.1 hv).1)
          (by linarith [hv.1] : 0 ≤ v)
        unfold SigmaVariableFull.density SigmaVariableFull.argument
        rw [sub_div] at h2
        linarith only [h1,h2])
  rw [intervalIntegral.integral_add (SigmaVariableFull.density_integrable ht.1) (hi.const_mul _),
    SigmaVariableFull.density_integral ht, intervalIntegral.integral_const_mul, new_inner_moment] at hm
  exact hm

/-- New original-kernel loss; all outer factors t,t+1,t+2 remain moving. -/
def newDensity (t : ℝ) : ℝ := (t-1)^9/(100800*t*(t+1)^8*(t+2))

theorem full_weight_add_new_le {t : ℝ} (ht : t ∈ Icc 1 3) :
    SigmaVariableFull.weight t+newDensity t ≤ sigma 3 (t+2) (t+1)/t := by
  have h := div_le_div_of_nonneg_right (full_inner_add_payment_le_sigma ht) (by linarith [ht.1] : 0 ≤ t)
  rw [add_div] at h
  rw [SigmaVariableFull.weight, SigmaVariableFull.endpointMass_eq ht]
  have he : newDensity t =
      (Hf4Next.coupledCellFactor t/(4*(t+1)))*((t-1)^9/9)/t := by
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have h1 : t+1 ≠ 0 := by linarith [ht.1]
    have h2 : t+2 ≠ 0 := by linarith [ht.1]
    unfold newDensity Hf4Next.coupledCellFactor
    field_simp
    ring
  rw [he]
  exact h

theorem newDensity_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ newDensity t := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 ≤ t-1 := by linarith
  unfold newDensity
  positivity

theorem newDensity_pos {t : ℝ} (ht : 1 < t) : 0 < newDensity t := by
  have ht0 : 0 < t := by linarith
  unfold newDensity
  exact div_pos (pow_pos (sub_pos.mpr ht) _) (by positivity)

theorem newDensity_continuous {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ContinuousOn newDensity (uIcc a b) := by
  rw [uIcc_of_le hab]
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  have h1 : 0 < t+1 := by positivity
  have h2 : 0 < t+2 := by positivity
  unfold newDensity
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := positivity)

/-- Exact partial fractions of this new loss only. -/
theorem newDensity_partial_fractions {t : ℝ} (ht : 0 < t) :
    (t-1)^9/(t*(t+1)^8*(t+2)) =
      -1/(2*t)+19683/(2*(t+2))-9840/(t+1)+9824/(t+1)^2-
        9696/(t+1)^3+9152/(t+1)^4-7680/(t+1)^5+5120/(t+1)^6-
        2304/(t+1)^7+512/(t+1)^8 := by
  have h1 : t+1 ≠ 0 := by positivity
  have h2 : t+2 ≠ 0 := by positivity
  field_simp
  ring

def newPrimitive (t : ℝ) : ℝ :=
  -log t/2+(19683/2:ℝ)*log (t+2)-9840*log (t+1)-9824*(t+1)⁻¹+
    4848*((t+1)⁻¹)^2-(9152/3:ℝ)*((t+1)⁻¹)^3+
    1920*((t+1)⁻¹)^4-1024*((t+1)⁻¹)^5+384*((t+1)⁻¹)^6-(512/7:ℝ)*((t+1)⁻¹)^7

theorem newPrimitive_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt newPrimitive ((t-1)^9/(t*(t+1)^8*(t+2))) t := by
  have h1 : 0 < t+1 := by positivity
  have h2 : 0 < t+2 := by positivity
  have hi := ((hasDerivAt_id t).add_const 1).inv h1.ne'
  have hl := (((hasDerivAt_log ht.ne').neg).div_const 2).add
    ((((hasDerivAt_id t).add_const 2).log h2.ne').const_mul (19683/2:ℝ))
  have ha := (hl.sub ((((hasDerivAt_id t).add_const 1).log h1.ne').const_mul 9840)).sub
    (hi.const_mul 9824)
  have hb := (ha.add ((hi.pow 2).const_mul 4848)).sub ((hi.pow 3).const_mul (9152/3:ℝ))
  have hc := (hb.add ((hi.pow 4).const_mul 1920)).sub ((hi.pow 5).const_mul 1024)
  convert (hc.add ((hi.pow 6).const_mul 384)).sub ((hi.pow 7).const_mul (512/7:ℝ)) using 1 <;>
    first | rfl | (dsimp; rw [newDensity_partial_fractions ht]; field_simp; ring)

def newCellPayment (a b : ℝ) : ℝ := (newPrimitive b-newPrimitive a)/100800

theorem newDensity_integral {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, newDensity t) = newCellPayment a b := by
  have hd (t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivAt (fun u => newPrimitive u/100800) (newDensity t) t := by
    rw [uIcc_of_le hab] at ht
    convert (newPrimitive_hasDerivAt (show 0 < t by linarith [ht.1])).div_const 100800 using 1 <;>
      first | rfl | (dsimp [newDensity]; simp only [div_eq_mul_inv, mul_inv_rev]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (newDensity_continuous ha hab).intervalIntegrable]
  unfold newCellPayment
  ring

theorem newCellPayment_nonneg {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ newCellPayment a b := by
  rw [← newDensity_integral ha hab]
  exact intervalIntegral.integral_nonneg hab (fun t ht => newDensity_nonneg (ha.trans ht.1))

end Hf4Continue
