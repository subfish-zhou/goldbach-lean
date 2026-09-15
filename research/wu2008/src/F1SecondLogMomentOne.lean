import F1SecondLogRational

noncomputable section
open Real Set MeasureTheory
open scoped Interval
namespace F1SecondLogRecovery

def massW : ℝ := (11289489565068814703/537600000000000000:ℝ)

theorem massW_integral : (∫ u in (2:ℝ)..(927/200), weight u) = massW := by
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => (927/200-u)^7/7-(527/200)*(927/200-u)^6/6)
      (weight u) u := by
    have ht := (hasDerivAt_id u).const_sub (927/200)
    convert ((ht.pow 7).div_const 7).sub (((ht.pow 6).const_mul (527/200)).div_const 6) using 1 <;>
      first | rfl | (dsimp [weight]; ring)
  have hc : Continuous weight := by unfold weight; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (hc.intervalIntegrable 2 (927/200))]
  norm_num [massW]

def massQOne : ℝ := (3038435121214519433905709006952403057278607147/1405747200000000000000000000000000000:ℝ)

def primitiveOne (u : ℝ) : ℝ :=
  (5744469110939805889909/5000000000000:ℝ)*((927/200-u)^7/7-(527/200)*(927/200-u)^6/6) +
  (-122724199917712118341/100000000000:ℝ)*((927/200-u)^8/8-(527/200)*(927/200-u)^7/7) +
  (5537019014092539267/10000000000:ℝ)*((927/200-u)^9/9-(527/200)*(927/200-u)^8/8) +
  (-27399872475495177/200000000:ℝ)*((927/200-u)^10/10-(527/200)*(927/200-u)^9/9) +
  (502484412717/25000:ℝ)*((927/200-u)^11/11-(527/200)*(927/200-u)^10/10) +
  (-69997480749/40000:ℝ)*((927/200-u)^12/12-(527/200)*(927/200-u)^11/11) +
  (8376291/100:ℝ)*((927/200-u)^13/13-(527/200)*(927/200-u)^12/12) +
  (-1701/1:ℝ)*((927/200-u)^14/14-(527/200)*(927/200-u)^13/13)

theorem primitiveOne_deriv (u : ℝ) :
    HasDerivAt primitiveOne (weight u*denomOne u) u := by
  have ht := (hasDerivAt_id u).const_sub (927/200)
  have h0 := ((ht.pow 7).div_const 7).sub (((ht.pow 6).const_mul (527/200)).div_const 6)
  have h1 := ((ht.pow 8).div_const 8).sub (((ht.pow 7).const_mul (527/200)).div_const 7)
  have h2 := ((ht.pow 9).div_const 9).sub (((ht.pow 8).const_mul (527/200)).div_const 8)
  have h3 := ((ht.pow 10).div_const 10).sub (((ht.pow 9).const_mul (527/200)).div_const 9)
  have h4 := ((ht.pow 11).div_const 11).sub (((ht.pow 10).const_mul (527/200)).div_const 10)
  have h5 := ((ht.pow 12).div_const 12).sub (((ht.pow 11).const_mul (527/200)).div_const 11)
  have h6 := ((ht.pow 13).div_const 13).sub (((ht.pow 12).const_mul (527/200)).div_const 12)
  have h7 := ((ht.pow 14).div_const 14).sub (((ht.pow 13).const_mul (527/200)).div_const 13)
  have hh := ((((((((h0.const_mul (5744469110939805889909/5000000000000:ℝ)).add (h1.const_mul (-122724199917712118341/100000000000:ℝ))).add (h2.const_mul (5537019014092539267/10000000000:ℝ))).add (h3.const_mul (-27399872475495177/200000000:ℝ))).add (h4.const_mul (502484412717/25000:ℝ))).add (h5.const_mul (-69997480749/40000:ℝ))).add (h6.const_mul (8376291/100:ℝ))).add (h7.const_mul (-1701/1:ℝ)))
  convert hh using 1 <;> first | rfl | (dsimp [primitiveOne,weight,denomOne,errorDenomOne]; ring)

theorem massQOne_integral :
    (∫ u in (2:ℝ)..(927/200), weight u*denomOne u) = massQOne := by
  have hc : Continuous (fun u => weight u*denomOne u) := by
    unfold weight denomOne errorDenomOne
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => primitiveOne_deriv u)
    (hc.intervalIntegrable 2 (927/200))]
  norm_num [primitiveOne,massQOne]

end F1SecondLogRecovery
