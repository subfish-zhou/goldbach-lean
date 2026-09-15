import F1SecondLogMomentOne

noncomputable section
open Real Set MeasureTheory
open scoped Interval
namespace F1SecondLogRecovery

def massQTwo : ℝ := (165156213554962872098454780967226370865856048513/29520691200000000000000000000000000000:ℝ)

def primitiveTwo (u : ℝ) : ℝ :=
  (5744469110939805889909/5000000000000:ℝ)*((927/200-u)^7/7-(527/200)*(927/200-u)^6/6) +
  (-71752867966161045671/100000000000:ℝ)*((927/200-u)^8/8-(527/200)*(927/200-u)^7/7) +
  (1675250267347802467/10000000000:ℝ)*((927/200-u)^9/9-(527/200)*(927/200-u)^8/8) +
  (-3812486496564291/200000000:ℝ)*((927/200-u)^10/10-(527/200)*(927/200-u)^9/9) +
  (576437981413/500000:ℝ)*((927/200-u)^11/11-(527/200)*(927/200-u)^10/10) +
  (-1482405691/40000:ℝ)*((927/200-u)^12/12-(527/200)*(927/200-u)^11/11) +
  (57277/100:ℝ)*((927/200-u)^13/13-(527/200)*(927/200-u)^12/12) +
  (-3/1:ℝ)*((927/200-u)^14/14-(527/200)*(927/200-u)^13/13)

theorem primitiveTwo_deriv (u : ℝ) :
    HasDerivAt primitiveTwo (weight u*denomTwo u) u := by
  have ht := (hasDerivAt_id u).const_sub (927/200)
  have h0 := ((ht.pow 7).div_const 7).sub (((ht.pow 6).const_mul (527/200)).div_const 6)
  have h1 := ((ht.pow 8).div_const 8).sub (((ht.pow 7).const_mul (527/200)).div_const 7)
  have h2 := ((ht.pow 9).div_const 9).sub (((ht.pow 8).const_mul (527/200)).div_const 8)
  have h3 := ((ht.pow 10).div_const 10).sub (((ht.pow 9).const_mul (527/200)).div_const 9)
  have h4 := ((ht.pow 11).div_const 11).sub (((ht.pow 10).const_mul (527/200)).div_const 10)
  have h5 := ((ht.pow 12).div_const 12).sub (((ht.pow 11).const_mul (527/200)).div_const 11)
  have h6 := ((ht.pow 13).div_const 13).sub (((ht.pow 12).const_mul (527/200)).div_const 12)
  have h7 := ((ht.pow 14).div_const 14).sub (((ht.pow 13).const_mul (527/200)).div_const 13)
  have hh := ((((((((h0.const_mul (5744469110939805889909/5000000000000:ℝ)).add (h1.const_mul (-71752867966161045671/100000000000:ℝ))).add (h2.const_mul (1675250267347802467/10000000000:ℝ))).add (h3.const_mul (-3812486496564291/200000000:ℝ))).add (h4.const_mul (576437981413/500000:ℝ))).add (h5.const_mul (-1482405691/40000:ℝ))).add (h6.const_mul (57277/100:ℝ))).add (h7.const_mul (-3/1:ℝ)))
  convert hh using 1 <;> first | rfl | (dsimp [primitiveTwo,weight,denomTwo,errorDenomTwo]; ring)

theorem massQTwo_integral :
    (∫ u in (2:ℝ)..(927/200), weight u*denomTwo u) = massQTwo := by
  have hc : Continuous (fun u => weight u*denomTwo u) := by
    unfold weight denomTwo errorDenomTwo
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => primitiveTwo_deriv u)
    (hc.intervalIntegrable 2 (927/200))]
  norm_num [primitiveTwo,massQTwo]

end F1SecondLogRecovery
