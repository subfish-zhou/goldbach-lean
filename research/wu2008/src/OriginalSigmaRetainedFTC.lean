import OriginalSigmaRetainedKernel

namespace OriginalSigmaStrength
open Real Set MeasureTheory NodeExtension
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
open Wu04WholeCollection
open scoped Interval BigOperators
noncomputable section

/-- A complete principal part with the multiplicity forced by the actual rational denominator. -/
def poleDensity (r c1 c2 c3 t : ℝ) : ℝ := c1/(t+r)+c2/(t+r)^2+c3/(t+r)^3

def polePrimitive (r c1 c2 c3 t : ℝ) : ℝ :=
  c1*log (t+r)-c2/(t+r)-c3/(2*(t+r)^2)

theorem polePrimitive_deriv (r c1 c2 c3 : ℝ) {t : ℝ} (ht : t+r≠0) :
    HasDerivAt (polePrimitive r c1 c2 c3) (poleDensity r c1 c2 c3 t) t := by
  have h := (((hasDerivAt_id t).add_const r).log ht).const_mul c1
  have h2 := (((hasDerivAt_id t).add_const r).inv ht).const_mul c2
  have h3 := (((((hasDerivAt_id t).add_const r).pow 2).inv (pow_ne_zero 2 ht)).const_mul c3).div_const 2
  convert (h.sub h2).sub h3 using 1 <;> first | rfl | skip
  · funext x
    simp only [polePrimitive, Pi.sub_apply, Pi.inv_apply, Pi.pow_apply, id,
      div_eq_mul_inv, mul_inv_rev]
    ring
  · dsimp only [id, Pi.pow_apply]
    unfold poleDensity
    field_simp
    ring

def retainedOuterPrimitive (t : ℝ) : ℝ :=
  polePrimitive 0 (3973/28125) (1/1875) 0 t+
  polePrimitive 5 (2592/625) (-1872/125) (864/25) t+
  polePrimitive 3 (-16/45) 0 0 t+
  polePrimitive (5/3) (-347392/253125) (38912/151875) (-16384/91125) t

/-- Exact Laurent normalization. No truncation, sample, or new log approximation occurs here. -/
theorem retainedWeight_partial_fractions {t : ℝ} (ht : 0<t) :
    retainedWeight t =
      poleDensity 0 (3973/28125) (1/1875) 0 t+
      poleDensity 5 (2592/625) (-1872/125) (864/25) t+
      poleDensity 3 (-16/45) 0 0 t+
      poleDensity (5/3) (-347392/253125) (38912/151875) (-16384/91125) t := by
  have h3 : t+3≠0 := by positivity
  have h5 : t+5≠0 := by positivity
  have h1 : t+1≠0 := by positivity
  have h35 : 3*t+5≠0 := by positivity
  have h53 : t+5/3≠0 := by positivity
  unfold retainedWeight retainedPaid V lowerLog upperLog poleDensity
  field_simp
  ring

theorem retainedOuterPrimitive_deriv {t : ℝ} (ht : 0<t) :
    HasDerivAt retainedOuterPrimitive (retainedWeight t) t := by
  rw [retainedWeight_partial_fractions ht]
  exact (((polePrimitive_deriv 0 _ _ _ (by linarith)).add
    (polePrimitive_deriv 5 _ _ _ (by linarith))).add
    (polePrimitive_deriv 3 _ _ _ (by linarith))).add
    (polePrimitive_deriv (5/3) _ _ _ (by linarith))

theorem retainedWeight_continuous {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    ContinuousOn retainedWeight (uIcc a b) := by
  rw [uIcc_of_le hab]
  intro t ht
  have ht0 : 0<t := ha.trans_le ht.1
  apply ContinuousAt.continuousWithinAt
  have he : retainedWeight =ᶠ[nhds t] fun x =>
      poleDensity 0 (3973/28125) (1/1875) 0 x+
      poleDensity 5 (2592/625) (-1872/125) (864/25) x+
      poleDensity 3 (-16/45) 0 0 x+
      poleDensity (5/3) (-347392/253125) (38912/151875) (-16384/91125) x := by
    filter_upwards [eventually_gt_nhds ht0] with x hx
    exact retainedWeight_partial_fractions hx
  apply ContinuousAt.congr_of_eventuallyEq _ he
  unfold poleDensity
  fun_prop (disch := positivity)

theorem retainedWeight_integral {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ t in a..b, retainedWeight t)=retainedOuterPrimitive b-retainedOuterPrimitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact retainedOuterPrimitive_deriv (ha.trans_le ht.1)
  · exact (retainedWeight_continuous ha hab).intervalIntegrable

/-- Collect each pole's endpoint log ratio before the single inherited split. -/
def poleCellPaid (r c1 c2 c3 a b : ℝ) : ℝ :=
  signedLow c1 ((b+r)/(a+r))-c2*(1/(b+r)-1/(a+r))-
    c3/2*(1/(b+r)^2-1/(a+r)^2)

theorem poleCellPaid_le (r c1 c2 c3 : ℝ) {a b : ℝ}
    (ha : 0<a+r) (hb : 0<b+r) :
    poleCellPaid r c1 c2 c3 a b ≤ polePrimitive r c1 c2 c3 b-polePrimitive r c1 c2 c3 a := by
  have h := signed_bound c1 (div_pos hb ha)
  rw [log_div hb.ne' ha.ne'] at h
  unfold poleCellPaid polePrimitive
  simp only [div_eq_mul_inv, mul_inv_rev] at *
  linarith only [h]

def retainedCellPaid (a b : ℝ) : ℝ :=
  poleCellPaid 0 (3973/28125) (1/1875) 0 a b+
  poleCellPaid 5 (2592/625) (-1872/125) (864/25) a b+
  poleCellPaid 3 (-16/45) 0 0 a b+
  poleCellPaid (5/3) (-347392/253125) (38912/151875) (-16384/91125) a b

theorem retainedCellPaid_le {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    retainedCellPaid a b ≤ retainedOuterPrimitive b-retainedOuterPrimitive a := by
  have h0 := poleCellPaid_le 0 (3973/28125) (1/1875) 0 (by linarith : 0<a+0) (by linarith : 0<b+0)
  have h5 := poleCellPaid_le 5 (2592/625) (-1872/125) (864/25) (by linarith : 0<a+5) (by linarith : 0<b+5)
  have h3 := poleCellPaid_le 3 (-16/45) 0 0 (by linarith : 0<a+3) (by linarith : 0<b+3)
  have h53 := poleCellPaid_le (5/3) (-347392/253125) (38912/151875) (-16384/91125)
    (by linarith : 0<a+5/3) (by linarith : 0<b+5/3)
  unfold retainedCellPaid retainedOuterPrimitive
  linarith only [h0,h5,h3,h53]

end
end OriginalSigmaStrength
