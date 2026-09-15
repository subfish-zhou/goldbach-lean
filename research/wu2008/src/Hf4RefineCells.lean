import Hf4RefineDensity

noncomputable section
namespace Hf4Refine
open Real Set MeasureTheory
open scoped Interval

/-- New mixed moment forced by the coefficient difference, not an order choice. -/
theorem coefficient_moment (t : ℝ) :
    (∫ v in (3:ℝ)..t+2, (v-3)*(t+2-v)^5) = (t-1)^7/42 := by
  have hd (v : ℝ) : HasDerivAt
      (fun w : ℝ => -(t-1)*(t+2-w)^6/6+(t+2-w)^7/7)
      ((v-3)*(t+2-v)^5) v := by
    convert (((((hasDerivAt_id v).const_sub (t+2)).pow 6).const_mul (-(t-1))).div_const 6).add
      ((((hasDerivAt_id v).const_sub (t+2)).pow 7).div_const 7) using 1 <;> first | rfl | (dsimp; ring)
  have hi : IntervalIntegrable (fun v : ℝ => (v-3)*(t+2-v)^5) volume 3 (t+2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v) hi]
  ring

theorem variationMass_lower {t b : ℝ} (ht : 1 ≤ t) (htb : t ≤ b) :
    (5/3:ℝ)*(Hf4Next.coupledCellFactor b*(t-1)^8/8) ≤ CorrectionSigmaVariable.variationMass t := by
  have hi : IntervalIntegrable (fun v : ℝ => (t+2-v)^7) volume 3 (t+2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hj : IntervalIntegrable (fun v : ℝ => (v-3)*(t+2-v)^5) volume 3 (t+2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have he : (fun v : ℝ => Hf4Next.coupledCellFactor b*
      ((t+2-v)^7+(7/2:ℝ)*(t-1)*(v-3)*(t+2-v)^5)) =
      (fun v : ℝ => Hf4Next.coupledCellFactor b*
      ((t+2-v)^7+((7/2:ℝ)*(t-1))*((v-3)*(t+2-v)^5))) := by funext v; ring
  have hm := intervalIntegral.integral_mono_on (by linarith : (3:ℝ) ≤ t+2)
    (by rw [he]; exact (hi.add (hj.const_mul _)).const_mul _)
    (CorrectionSigmaVariable.variation_integrable ht)
    (fun v hv => combined_density_lower ht htb hv)
  rw [he, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hi (hj.const_mul _), intervalIntegral.integral_const_mul,
    SigmaEndpointPayment.inner_moment, coefficient_moment] at hm
  calc
    _ = Hf4Next.coupledCellFactor b*((t-1)^8/8+7/2*(t-1)*((t-1)^7/42)) := by ring
    _ ≤ _ := hm

/-- Keep the actual outer divisor t instead of replacing it by b. -/
def outerDensity (b t : ℝ) : ℝ := (5/24:ℝ)*Hf4Next.coupledCellFactor b*(t-1)^8/t

theorem outerDensity_lower {t b : ℝ} (ht : 1 ≤ t) (htb : t ≤ b) :
    outerDensity b t ≤ CorrectionSigmaVariable.variationMass t/t := by
  calc
    _ = ((5/3:ℝ)*(Hf4Next.coupledCellFactor b*(t-1)^8/8))/t := by unfold outerDensity; ring
    _ ≤ _ := div_le_div_of_nonneg_right (variationMass_lower ht htb) (by linarith)

/-- Exact primitive of the new variable-divisor density, without log approximation. -/
def outerPrimitive (t : ℝ) : ℝ :=
  (t-1)^8/8-(t-1)^7/7+(t-1)^6/6-(t-1)^5/5+
  (t-1)^4/4-(t-1)^3/3+(t-1)^2/2-(t-1)+log t

theorem outerPrimitive_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt outerPrimitive ((t-1)^8/t) t := by
  have h := (hasDerivAt_id t).sub_const 1
  have h87 := ((h.pow 8).div_const 8).sub ((h.pow 7).div_const 7)
  have h65 := (h87.add ((h.pow 6).div_const 6)).sub ((h.pow 5).div_const 5)
  have h43 := (h65.add ((h.pow 4).div_const 4)).sub ((h.pow 3).div_const 3)
  have h21 := (h43.add ((h.pow 2).div_const 2)).sub h
  convert h21.add (hasDerivAt_log ht.ne') using 1 <;>
    first | rfl | (dsimp; field_simp; ring)

def cellPayment (a b : ℝ) : ℝ :=
  (5/24:ℝ)*Hf4Next.coupledCellFactor b*(outerPrimitive b-outerPrimitive a)

theorem outerDensity_integrable {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (outerDensity b) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  unfold outerDensity
  fun_prop

theorem outerDensity_integral {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, outerDensity b t) = cellPayment a b := by
  have hd (t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivAt (fun u => (5/24:ℝ)*Hf4Next.coupledCellFactor b*outerPrimitive u)
        (outerDensity b t) t := by
    rw [uIcc_of_le hab] at ht
    convert (outerPrimitive_hasDerivAt (show 0 < t by linarith [ht.1])).const_mul
      ((5/24:ℝ)*Hf4Next.coupledCellFactor b) using 1 <;> first | rfl | (dsimp [outerDensity]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (outerDensity_integrable ha hab)]
  unfold cellPayment
  ring

theorem amplified_old_cell_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (5/3:ℝ)*Hf4Next.cellPayment a b ≤ cellPayment a b := by
  have hb := ha.trans hab
  have hi : IntervalIntegrable (SigmaEndpointPayment.outerResidual b) volume a b := by
    apply Continuous.intervalIntegrable
    unfold SigmaEndpointPayment.outerResidual
    fun_prop
  have hm := intervalIntegral.integral_mono_on hab
    (hi.const_mul ((5/3:ℝ)*Hf4Next.amplification b)) (outerDensity_integrable ha hab)
    (fun t ht => show (5/3:ℝ)*Hf4Next.amplification b*SigmaEndpointPayment.outerResidual b t ≤
      outerDensity b t from by
        have ht1 : 1 ≤ t := ha.trans ht.1
        have hc := (Hf4Next.coupledCellFactor_pos hb).le
        have hn : 0 ≤ (5/24:ℝ)*Hf4Next.coupledCellFactor b*(t-1)^8 := by positivity
        calc
          _ = ((5/24:ℝ)*Hf4Next.coupledCellFactor b*(t-1)^8)/b := by
            rw [Hf4Next.factor_identity hb]
            unfold SigmaEndpointPayment.outerResidual
            ring
          _ ≤ _ := div_le_div_of_nonneg_left hn (by linarith) ht.2)
  rw [intervalIntegral.integral_const_mul, SigmaEndpointPayment.outerResidual_integral,
    outerDensity_integral ha hab] at hm
  rw [Hf4Next.cellPayment_eq_amplified hb]
  convert hm using 1
  ring

theorem cellPayment_nonneg {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ cellPayment a b :=
  (mul_nonneg (by norm_num) (Hf4Next.cellPayment_nonneg ha hab)).trans (amplified_old_cell_le ha hab)

theorem old_cell_add_payment_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    SigmaInnerProfile.cellIntegral a b + cellPayment a b ≤ SigmaVariableFull.cellMass a b := by
  have hi : IntervalIntegrable SigmaInnerProfile.weight volume a b :=
    (SigmaInnerProfile.weight_continuous (by linarith : 0<a) hab).intervalIntegrable
  have hj := outerDensity_integrable ha hab
  have hf : IntervalIntegrable SigmaVariableFull.weight volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro t ht
    have ht' : t ∈ Icc (1:ℝ) 3 := ⟨ha.trans ht.1,ht.2.trans hb⟩
    exact ((SigmaVariableFull.endpointMass_continuousAt ht').div continuousAt_id
      (show id t ≠ 0 by dsimp; linarith [ht'.1])).continuousWithinAt
  have hm := intervalIntegral.integral_mono_on hab (hi.add hj) hf
    (fun t ht => show SigmaInnerProfile.weight t + outerDensity b t ≤ SigmaVariableFull.weight t from by
      have ht' : t ∈ Icc (1:ℝ) 3 := ⟨ha.trans ht.1,ht.2.trans hb⟩
      rw [SigmaVariableFull.weight, SigmaVariableFull.endpointMass_eq ht',
        SigmaVariableFull.innerMass_balance ht', add_div]
      exact add_le_add le_rfl (outerDensity_lower ht'.1 ht.2))
  rw [intervalIntegral.integral_add hi hj, outerDensity_integral ha hab] at hm
  exact hm

end Hf4Refine
