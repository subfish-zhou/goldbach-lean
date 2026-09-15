import SigmaExistingLaurentA
import SigmaExistingLaurentB
import SigmaExistingLaurentC
import SigmaExistingLaurentR

namespace SigmaExistingLogError
open Real Set MeasureTheory NodeExtension OriginalSigmaStrength OriginalSigmaCubicRestoration
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
open scoped Interval
noncomputable section

def weight (t : ℝ) : ℝ := endpointPaid t/t

theorem weight_laurent {t : ℝ} (ht : 0<t) : weight t =
    80/1323+(2/1323)*t+
    poleDensity 0 (1818722/12403125) (1556/6890625) (-106/1378125) t+(4/275625)/t^4+
    poleDensity 1 (-227/2646) 0 0 t+
    poleDensity 3 (-20576/19845) (2752/1323) (-512/441) t+
    poleDensity 5 (1129701/306250) (-1270998/153125) (525528/30625) t+
    poleDensity (5/3) (-286208/212625) (2584576/11390625) (-1212416/6834375) t := by
  have he : weight t=aWeight t+bWeight t+cWeight t+rWeight t := by
    unfold weight endpointPaid aWeight bWeight cWeight rWeight
    ring
  rw [he,aWeight_laurent ht,bWeight_laurent ht,cWeight_laurent ht,rWeight_laurent ht]
  unfold poleDensity
  simp only [add_zero,pow_one]
  ring

def primitive (t : ℝ) : ℝ := (80/1323)*t+t^2/1323+
  polePrimitive 0 (1818722/12403125) (1556/6890625) (-106/1378125) t-(4/275625)/(3*t^3)+
  polePrimitive 1 (-227/2646) 0 0 t+
  polePrimitive 3 (-20576/19845) (2752/1323) (-512/441) t+
  polePrimitive 5 (1129701/306250) (-1270998/153125) (525528/30625) t+
  polePrimitive (5/3) (-286208/212625) (2584576/11390625) (-1212416/6834375) t

theorem fourth_deriv {t : ℝ} (ht : 0<t) :
    HasDerivAt (fun t : ℝ => -(4/275625)/(3*t^3)) ((4/275625)/t^4) t := by
  have h := (((((hasDerivAt_id t).pow 3).inv (pow_ne_zero 3 ht.ne')).const_mul (-(4/275625))).div_const 3)
  convert h using 1 <;> first | rfl | skip
  · funext x
    simp only [Pi.inv_apply,Pi.pow_apply,id,div_eq_mul_inv,mul_inv_rev]
    ring
  · dsimp only [id,Pi.pow_apply]
    field_simp
    ring

theorem primitive_deriv {t : ℝ} (ht : 0<t) : HasDerivAt primitive (weight t) t := by
  rw [weight_laurent ht]
  have hp : HasDerivAt (fun t : ℝ => (80/1323)*t+t^2/1323) (80/1323+(2/1323)*t) t := by
    convert ((hasDerivAt_id t).const_mul (80/1323)).add (((hasDerivAt_id t).pow 2).div_const 1323) using 1 <;>
      first | rfl | skip
    dsimp only [id]
    ring
  convert ((((((hp.add (polePrimitive_deriv 0 _ _ _ (by linarith))).add (fourth_deriv ht)).add
    (polePrimitive_deriv 1 _ _ _ (by linarith))).add
    (polePrimitive_deriv 3 _ _ _ (by linarith))).add
    (polePrimitive_deriv 5 _ _ _ (by linarith))).add
    (polePrimitive_deriv (5/3) _ _ _ (by linarith))) using 1 <;> first | rfl | skip
  funext x
  unfold primitive
  simp only [Pi.add_apply]
  ring

theorem weight_continuous {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    ContinuousOn weight (uIcc a b) := by
  rw [uIcc_of_le hab]
  intro t ht
  have ht0 : 0<t := ha.trans_le ht.1
  have he : weight =ᶠ[nhds t] fun x =>
      80/1323+(2/1323)*x+
      poleDensity 0 (1818722/12403125) (1556/6890625) (-106/1378125) x+(4/275625)/x^4+
      poleDensity 1 (-227/2646) 0 0 x+
      poleDensity 3 (-20576/19845) (2752/1323) (-512/441) x+
      poleDensity 5 (1129701/306250) (-1270998/153125) (525528/30625) x+
      poleDensity (5/3) (-286208/212625) (2584576/11390625) (-1212416/6834375) x := by
    filter_upwards [eventually_gt_nhds ht0] with x hx
    exact weight_laurent hx
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.congr_of_eventuallyEq _ he
  unfold poleDensity
  fun_prop (disch := positivity)

theorem weight_integral {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ t in a..b, weight t)=primitive b-primitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact primitive_deriv (ha.trans_le ht.1)
  · exact (weight_continuous ha hab).intervalIntegrable

def cellPaid (a b : ℝ) : ℝ := (80/1323)*(b-a)+(b^2-a^2)/1323+
  poleCellPaid 0 (1818722/12403125) (1556/6890625) (-106/1378125) a b-
  (4/275625)/3*(1/b^3-1/a^3)+
  poleCellPaid 1 (-227/2646) 0 0 a b+
  poleCellPaid 3 (-20576/19845) (2752/1323) (-512/441) a b+
  poleCellPaid 5 (1129701/306250) (-1270998/153125) (525528/30625) a b+
  poleCellPaid (5/3) (-286208/212625) (2584576/11390625) (-1212416/6834375) a b

theorem cellPaid_le {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    cellPaid a b ≤ primitive b-primitive a := by
  have h0 := poleCellPaid_le 0 (1818722/12403125) (1556/6890625) (-106/1378125)
    (by linarith : 0<a+0) (by linarith : 0<b+0)
  have h1 := poleCellPaid_le 1 (-227/2646) 0 0 (by linarith : 0<a+1) (by linarith : 0<b+1)
  have h3 := poleCellPaid_le 3 (-20576/19845) (2752/1323) (-512/441)
    (by linarith : 0<a+3) (by linarith : 0<b+3)
  have h5 := poleCellPaid_le 5 (1129701/306250) (-1270998/153125) (525528/30625)
    (by linarith : 0<a+5) (by linarith : 0<b+5)
  have h53 := poleCellPaid_le (5/3) (-286208/212625) (2584576/11390625) (-1212416/6834375)
    (by linarith : 0<a+5/3) (by linarith : 0<b+5/3)
  unfold cellPaid primitive
  simp only [div_eq_mul_inv,mul_inv_rev]
  linarith only [h0,h1,h3,h5,h53]

end
end SigmaExistingLogError
