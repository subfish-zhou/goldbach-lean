import F1ActualKernelPayment

noncomputable section
open Real Set MeasureTheory FirstIntegralRecovery
open scoped Interval
namespace F1RemainingRecovery

def momentWeight (u : ℝ) : ℝ := (u-2)^5*(927/200-u)
def momentDenom (u : ℝ) : ℝ := u*(1327/200+u)*(u+2)^3*(u^2+16*u+4)
def momentW : ℝ := (11289489565068814703/537600000000000000:ℝ)
def momentQ : ℝ := (100019929920101667003802169433380560014174461/5904138240000000000000000000000000000:ℝ)
def momentA : ℝ := momentW/momentQ
def momentPayment : ℝ := 2*momentW^2/momentQ

def momentPrimitive (u : ℝ) : ℝ :=
  (221056/5:ℝ)*((527/200:ℝ)*(u-2)^6/6-(u-2)^7/7)+
  (412448/5:ℝ)*((527/200:ℝ)*(u-2)^7/7-(u-2)^8/8)+
  (1564152/25:ℝ)*((527/200:ℝ)*(u-2)^8/8-(u-2)^9/9)+
  (124298/5:ℝ)*((527/200:ℝ)*(u-2)^9/9-(u-2)^10/10)+
  (138623/25:ℝ)*((527/200:ℝ)*(u-2)^10/10-(u-2)^11/11)+
  (68559/100:ℝ)*((527/200:ℝ)*(u-2)^11/11-(u-2)^12/12)+
  (8527/200:ℝ)*((527/200:ℝ)*(u-2)^12/12-(u-2)^13/13)+
  (1/1:ℝ)*((527/200:ℝ)*(u-2)^13/13-(u-2)^14/14)

theorem momentPrimitive_deriv (u : ℝ) :
    HasDerivAt momentPrimitive (momentWeight u*momentDenom u) u := by
  have hd := (hasDerivAt_id u).sub_const 2
  have h0 := (((hd.pow 6).const_mul (527/200)).div_const 6).sub ((hd.pow 7).div_const 7)
  have h1 := (((hd.pow 7).const_mul (527/200)).div_const 7).sub ((hd.pow 8).div_const 8)
  have h2 := (((hd.pow 8).const_mul (527/200)).div_const 8).sub ((hd.pow 9).div_const 9)
  have h3 := (((hd.pow 9).const_mul (527/200)).div_const 9).sub ((hd.pow 10).div_const 10)
  have h4 := (((hd.pow 10).const_mul (527/200)).div_const 10).sub ((hd.pow 11).div_const 11)
  have h5 := (((hd.pow 11).const_mul (527/200)).div_const 11).sub ((hd.pow 12).div_const 12)
  have h6 := (((hd.pow 12).const_mul (527/200)).div_const 12).sub ((hd.pow 13).div_const 13)
  have h7 := (((hd.pow 13).const_mul (527/200)).div_const 13).sub ((hd.pow 14).div_const 14)
  have h := ((((((((h0.const_mul (221056/5:ℝ)).add (h1.const_mul (412448/5:ℝ))).add (h2.const_mul (1564152/25:ℝ))).add (h3.const_mul (124298/5:ℝ))).add (h4.const_mul (138623/25:ℝ))).add (h5.const_mul (68559/100:ℝ))).add (h6.const_mul (8527/200:ℝ))).add (h7.const_mul (1/1:ℝ)))
  convert h using 1 <;> first | rfl | (dsimp [momentPrimitive,momentWeight,momentDenom]; ring)

theorem momentQ_integral :
    (∫ u in (2:ℝ)..(927/200), momentWeight u*momentDenom u) = momentQ := by
  have hc : Continuous (fun u => momentWeight u*momentDenom u) := by
    unfold momentWeight momentDenom
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => momentPrimitive_deriv u) (hc.intervalIntegrable 2 (927/200))]
  norm_num [momentPrimitive,momentQ]

theorem momentW_integral : (∫ u in (2:ℝ)..(927/200), momentWeight u) = momentW := by
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => (527/200)*(u-2)^6/6-(u-2)^7/7)
      (momentWeight u) u := by
    have h := (hasDerivAt_id u).sub_const 2
    convert (((h.pow 6).const_mul (527/200)).div_const 6).sub ((h.pow 7).div_const 7) using 1 <;>
      first | rfl | (dsimp [momentWeight]; ring)
  have hc : Continuous momentWeight := by unfold momentWeight; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hd u) (hc.intervalIntegrable 2 (927/200))]
  norm_num [momentW]

end F1RemainingRecovery
