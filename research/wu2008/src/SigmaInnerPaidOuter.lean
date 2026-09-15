import SigmaInnerLaurentA
import SigmaInnerLaurentB
import SigmaInnerLaurentC
import SigmaInnerLaurentR
import F1JointQuadratic

namespace SigmaInnerPaid
open Real Set MeasureTheory OriginalSigmaStrength
open scoped Interval
noncomputable section

/-- Translate the existing quadratic primitive by the forced variable u=t+1. -/
def quadraticPrimitive (f g t : ℝ) : ℝ := F1JointFTC.quadraticPrimitive f (g-f) (t+1)

theorem quadraticPrimitive_deriv (f g : ℝ) {t : ℝ} (ht : 1≤t) :
    HasDerivAt (quadraticPrimitive f g) ((f*t+g)/(t^2+18*t+21)) t := by
  have h := (F1JointFTC.quadraticPrimitive_deriv f (g-f) (by linarith : 2≤t+1)).comp t
    ((hasDerivAt_id t).add_const 1)
  convert h using 1 <;> first | rfl | skip
  simp only [mul_one]
  congr 1 <;> ring

def weight (t : ℝ) : ℝ := endpointPaid t/t

theorem weight_laurent {t : ℝ} (ht : 0<t) : weight t =
    22/189+
    poleDensity 0 (3117833702/21271359375) (740716/3038765625) (-2306/28940625) t+
    (4/275625)/t^4+
    poleDensity 3 (-4432/2835) (352/189) (-128/63) t+
    poleDensity 5 (4752318/1164625) (-23702004/2646875) (850824/48125) t+
    poleDensity (5/3) (-73544192/186046875) (22433792/79734375) (-557056/6834375) t+
    ((-438353120/201331053)*t-21945288920/1811979477)/(t^2+18*t+21) := by
  have h : weight t=aWeight t+bWeight t+cWeight t+rWeight t := by
    unfold weight endpointPaid aWeight bWeight cWeight rWeight
    ring
  rw [h,aWeight_laurent ht,bWeight_laurent ht,cWeight_laurent ht,rWeight_laurent ht]
  unfold poleDensity
  simp only [add_zero,div_eq_mul_inv]
  ring

/-- Elementary primitive of the new rational endpoint payment, not of the full log kernel. -/
def primitive (t : ℝ) : ℝ :=
  (22/189)*t+
  polePrimitive 0 (3117833702/21271359375) (740716/3038765625) (-2306/28940625) t-
  (4/275625)/(3*t^3)+
  polePrimitive 3 (-4432/2835) (352/189) (-128/63) t+
  polePrimitive 5 (4752318/1164625) (-23702004/2646875) (850824/48125) t+
  polePrimitive (5/3) (-73544192/186046875) (22433792/79734375) (-557056/6834375) t+
  quadraticPrimitive (-438353120/201331053) (-21945288920/1811979477) t

theorem primitive_deriv {t : ℝ} (ht : 1≤t) : HasDerivAt primitive (weight t) t := by
  have ht0 : 0<t := by linarith
  rw [weight_laurent ht0]
  have h := (((((((hasDerivAt_id t).const_mul (22/189)).add
    (polePrimitive_deriv 0 (3117833702/21271359375) (740716/3038765625) (-2306/28940625) (by linarith : t+0≠0))).add
    (SigmaExistingLogError.fourth_deriv ht0)).add
    (polePrimitive_deriv 3 (-4432/2835) (352/189) (-128/63) (by positivity : t+3≠0))).add
    (polePrimitive_deriv 5 (4752318/1164625) (-23702004/2646875) (850824/48125) (by positivity : t+5≠0))).add
    (polePrimitive_deriv (5/3) (-73544192/186046875) (22433792/79734375) (-557056/6834375) (by positivity : t+5/3≠0))).add
    (quadraticPrimitive_deriv (-438353120/201331053) (-21945288920/1811979477) ht)
  convert h using 1 <;> first | rfl | skip
  · funext x
    unfold primitive
    dsimp only [Pi.add_apply,id]
    ring
  · ring

theorem weight_continuous {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    ContinuousOn weight (uIcc a b) := by
  rw [uIcc_of_le hab]
  intro t ht
  have ht0 : 0<t := ha.trans_le ht.1
  have hq : 0<t^2+18*t+21 := by positivity
  have he : weight =ᶠ[nhds t] fun x =>
      22/189+
      poleDensity 0 (3117833702/21271359375) (740716/3038765625) (-2306/28940625) x+
      (4/275625)/x^4+
      poleDensity 3 (-4432/2835) (352/189) (-128/63) x+
      poleDensity 5 (4752318/1164625) (-23702004/2646875) (850824/48125) x+
      poleDensity (5/3) (-73544192/186046875) (22433792/79734375) (-557056/6834375) x+
      ((-438353120/201331053)*x-21945288920/1811979477)/(x^2+18*x+21) := by
    filter_upwards [eventually_gt_nhds ht0] with x hx
    exact weight_laurent hx
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.congr_of_eventuallyEq _ he
  unfold poleDensity
  fun_prop (disch := positivity)

theorem weight_integral {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    (∫ t in a..b, weight t)=primitive b-primitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact primitive_deriv (ha.trans ht.1)
  · exact (weight_continuous (by linarith) hab).intervalIntegrable

end
end SigmaInnerPaid
