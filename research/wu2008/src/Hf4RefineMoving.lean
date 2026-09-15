import Hf4RefineCells

noncomputable section
namespace Hf4Refine
open Real Set MeasureTheory
open scoped Interval

/-- No outer coordinate is frozen in this lower density. -/
def movingDensity (t : ℝ) : ℝ := (t-1)^8/(13440*t*(t+1)^7*(t+2))

theorem movingDensity_eq (t : ℝ) : movingDensity t = outerDensity t t := by
  unfold movingDensity outerDensity Hf4Next.coupledCellFactor
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem movingDensity_lower {t : ℝ} (ht : 1 ≤ t) :
    movingDensity t ≤ CorrectionSigmaVariable.variationMass t/t := by
  rw [movingDensity_eq]
  exact outerDensity_lower ht le_rfl

theorem outerDensity_le_moving {t b : ℝ} (ht : 1 ≤ t) (htb : t ≤ b) :
    outerDensity b t ≤ movingDensity t := by
  rw [movingDensity_eq]
  unfold outerDensity
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Hf4Next.coupledCellFactor_antitone ht htb) (by norm_num))
      (by positivity)) (by linarith)

/-- Partial fractions of this new density; no existing full-kernel FTC is replayed. -/
theorem moving_partial_fractions {t : ℝ} (ht : 0 < t) :
    (t-1)^8/(t*(t+1)^7*(t+2)) =
      1/(2*t)+6561/(2*(t+2))-3280/(t+1)+3264/(t+1)^2-
        3168/(t+1)^3+2816/(t+1)^4-2048/(t+1)^5+1024/(t+1)^6-256/(t+1)^7 := by
  have h1 : t+1 ≠ 0 := by positivity
  have h2 : t+2 ≠ 0 := by positivity
  field_simp
  ring

def movingPrimitive (t : ℝ) : ℝ :=
  log t/2+(6561/2:ℝ)*log (t+2)-3280*log (t+1)-3264*(t+1)⁻¹+
    1584*((t+1)⁻¹)^2-(2816/3:ℝ)*((t+1)⁻¹)^3+
    512*((t+1)⁻¹)^4-(1024/5:ℝ)*((t+1)⁻¹)^5+(128/3:ℝ)*((t+1)⁻¹)^6

theorem movingPrimitive_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt movingPrimitive ((t-1)^8/(t*(t+1)^7*(t+2))) t := by
  have h1 : 0 < t+1 := by positivity
  have h2 : 0 < t+2 := by positivity
  have hi := ((hasDerivAt_id t).add_const 1).inv h1.ne'
  have hl := ((hasDerivAt_log ht.ne').div_const 2).add
    ((((hasDerivAt_id t).add_const 2).log h2.ne').const_mul (6561/2:ℝ))
  have ha := (hl.sub ((((hasDerivAt_id t).add_const 1).log h1.ne').const_mul 3280)).sub
    (hi.const_mul 3264)
  have hb := (ha.add ((hi.pow 2).const_mul 1584)).sub ((hi.pow 3).const_mul (2816/3:ℝ))
  have hc := (hb.add ((hi.pow 4).const_mul 512)).sub ((hi.pow 5).const_mul (1024/5:ℝ))
  convert hc.add ((hi.pow 6).const_mul (128/3:ℝ)) using 1 <;>
    first | rfl | (dsimp; rw [moving_partial_fractions ht]; field_simp; ring)

def movingCellPayment (a b : ℝ) : ℝ := (movingPrimitive b-movingPrimitive a)/13440

theorem movingDensity_integrable {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable movingDensity volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  have h1 : 0 < t+1 := by positivity
  have h2 : 0 < t+2 := by positivity
  unfold movingDensity
  exact ((by fun_prop : ContinuousAt (fun t : ℝ => (t-1)^8) t).div
    (by fun_prop : ContinuousAt (fun t : ℝ => 13440*t*(t+1)^7*(t+2)) t)
    (by positivity)).continuousWithinAt

theorem movingDensity_integral {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, movingDensity t) = movingCellPayment a b := by
  have hd (t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivAt (fun u => movingPrimitive u/13440) (movingDensity t) t := by
    rw [uIcc_of_le hab] at ht
    convert (movingPrimitive_hasDerivAt (show 0 < t by linarith [ht.1])).div_const 13440 using 1 <;>
      first | rfl | (dsimp [movingDensity]; simp only [div_eq_mul_inv, mul_inv_rev]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (movingDensity_integrable ha hab)]
  unfold movingCellPayment
  ring

theorem cellPayment_le_moving {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    cellPayment a b ≤ movingCellPayment a b := by
  have hm := intervalIntegral.integral_mono_on hab (outerDensity_integrable ha hab)
    (movingDensity_integrable ha hab) (fun t ht => outerDensity_le_moving (ha.trans ht.1) ht.2)
  rw [outerDensity_integral ha hab, movingDensity_integral ha hab] at hm
  exact hm

theorem movingCellPayment_nonneg {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ movingCellPayment a b := (cellPayment_nonneg ha hab).trans (cellPayment_le_moving ha hab)

theorem old_cell_add_movingPayment_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    SigmaInnerProfile.cellIntegral a b + movingCellPayment a b ≤ SigmaVariableFull.cellMass a b := by
  have hi : IntervalIntegrable SigmaInnerProfile.weight volume a b :=
    (SigmaInnerProfile.weight_continuous (by linarith : 0<a) hab).intervalIntegrable
  have hj := movingDensity_integrable ha hab
  have hf : IntervalIntegrable SigmaVariableFull.weight volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro t ht
    have ht' : t ∈ Icc (1:ℝ) 3 := ⟨ha.trans ht.1,ht.2.trans hb⟩
    exact ((SigmaVariableFull.endpointMass_continuousAt ht').div continuousAt_id
      (show id t ≠ 0 by dsimp; linarith [ht'.1])).continuousWithinAt
  have hm := intervalIntegral.integral_mono_on hab (hi.add hj) hf
    (fun t ht => show SigmaInnerProfile.weight t + movingDensity t ≤ SigmaVariableFull.weight t from by
      have ht' : t ∈ Icc (1:ℝ) 3 := ⟨ha.trans ht.1,ht.2.trans hb⟩
      rw [SigmaVariableFull.weight, SigmaVariableFull.endpointMass_eq ht',
        SigmaVariableFull.innerMass_balance ht', add_div]
      exact add_le_add le_rfl (movingDensity_lower ht'.1))
  rw [intervalIntegral.integral_add hi hj, movingDensity_integral ha hab] at hm
  exact hm

end Hf4Refine
