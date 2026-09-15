import F1FixedSquareIdentity

noncomputable section
open Real Set MeasureTheory FirstIntegralRecovery FirstCRationalPayment
open F1RemainingRecovery
open scoped Interval
namespace F1FixedSquareRecovery

/-- This polynomial is forced solely by the previously checked fixed square. -/
def forcedSquarePrimitive (u : ℝ) : ℝ :=
  (48865755136/25:ℝ)*((527/200:ℝ)*(u-2)^6/6-(u-2)^7/7) +
  (182348210176/25:ℝ)*((527/200:ℝ)*(u-2)^7/7-(u-2)^8/8) +
  (1542097132544/125:ℝ)*((527/200:ℝ)*(u-2)^8/8-(u-2)^9/9) +
  (1565030915072/125:ℝ)*((527/200:ℝ)*(u-2)^9/9-(u-2)^10/10) +
  (5316329013184/625:ℝ)*((527/200:ℝ)*(u-2)^10/10-(u-2)^11/11) +
  (510769177952/125:ℝ)*((527/200:ℝ)*(u-2)^11/11-(u-2)^12/12) +
  (892953442212/625:ℝ)*((527/200:ℝ)*(u-2)^12/12-(u-2)^13/13) +
  (230375409144/625:ℝ)*((527/200:ℝ)*(u-2)^13/13-(u-2)^14/14) +
  (8791639122/125:ℝ)*((527/200:ℝ)*(u-2)^14/14-(u-2)^15/15) +
  (6154996036/625:ℝ)*((527/200:ℝ)*(u-2)^15/15-(u-2)^16/16) +
  (1985136353/2000:ℝ)*((527/200:ℝ)*(u-2)^16/16-(u-2)^17/17) +
  (695500993/10000:ℝ)*((527/200:ℝ)*(u-2)^17/17-(u-2)^18/18) +
  (127556929/40000:ℝ)*((527/200:ℝ)*(u-2)^18/18-(u-2)^19/19) +
  (8527/100:ℝ)*((527/200:ℝ)*(u-2)^19/19-(u-2)^20/20) +
  (1/1:ℝ)*((527/200:ℝ)*(u-2)^20/20-(u-2)^21/21)

def forcedSquareMass : ℝ := (5347949792151715944746249375205041414289829915936750698261151314473/341877719040000000000000000000000000000000000000000000:ℝ)

theorem forcedSquarePrimitive_deriv (u : ℝ) :
    HasDerivAt forcedSquarePrimitive (momentWeight u*(momentDenom u)^2) u := by
  have hd := (hasDerivAt_id u).sub_const 2
  have h0 := (((hd.pow 6).const_mul (527/200)).div_const 6).sub ((hd.pow 7).div_const 7)
  have h1 := (((hd.pow 7).const_mul (527/200)).div_const 7).sub ((hd.pow 8).div_const 8)
  have h2 := (((hd.pow 8).const_mul (527/200)).div_const 8).sub ((hd.pow 9).div_const 9)
  have h3 := (((hd.pow 9).const_mul (527/200)).div_const 9).sub ((hd.pow 10).div_const 10)
  have h4 := (((hd.pow 10).const_mul (527/200)).div_const 10).sub ((hd.pow 11).div_const 11)
  have h5 := (((hd.pow 11).const_mul (527/200)).div_const 11).sub ((hd.pow 12).div_const 12)
  have h6 := (((hd.pow 12).const_mul (527/200)).div_const 12).sub ((hd.pow 13).div_const 13)
  have h7 := (((hd.pow 13).const_mul (527/200)).div_const 13).sub ((hd.pow 14).div_const 14)
  have h8 := (((hd.pow 14).const_mul (527/200)).div_const 14).sub ((hd.pow 15).div_const 15)
  have h9 := (((hd.pow 15).const_mul (527/200)).div_const 15).sub ((hd.pow 16).div_const 16)
  have h10 := (((hd.pow 16).const_mul (527/200)).div_const 16).sub ((hd.pow 17).div_const 17)
  have h11 := (((hd.pow 17).const_mul (527/200)).div_const 17).sub ((hd.pow 18).div_const 18)
  have h12 := (((hd.pow 18).const_mul (527/200)).div_const 18).sub ((hd.pow 19).div_const 19)
  have h13 := (((hd.pow 19).const_mul (527/200)).div_const 19).sub ((hd.pow 20).div_const 20)
  have h14 := (((hd.pow 20).const_mul (527/200)).div_const 20).sub ((hd.pow 21).div_const 21)
  have h := (((((((((((((((h0.const_mul (48865755136/25:ℝ)).add (h1.const_mul (182348210176/25:ℝ))).add (h2.const_mul (1542097132544/125:ℝ))).add (h3.const_mul (1565030915072/125:ℝ))).add (h4.const_mul (5316329013184/625:ℝ))).add (h5.const_mul (510769177952/125:ℝ))).add (h6.const_mul (892953442212/625:ℝ))).add (h7.const_mul (230375409144/625:ℝ))).add (h8.const_mul (8791639122/125:ℝ))).add (h9.const_mul (6154996036/625:ℝ))).add (h10.const_mul (1985136353/2000:ℝ))).add (h11.const_mul (695500993/10000:ℝ))).add (h12.const_mul (127556929/40000:ℝ))).add (h13.const_mul (8527/100:ℝ))).add (h14.const_mul (1/1:ℝ)))
  convert h using 1 <;> first | rfl | (dsimp [forcedSquarePrimitive,momentWeight,momentDenom]; ring)

theorem forcedSquareMass_integral :
    (∫ u in (2:ℝ)..(927/200), momentWeight u*(momentDenom u)^2) = forcedSquareMass := by
  have hc : Continuous (fun u => momentWeight u*(momentDenom u)^2) := by
    unfold momentWeight momentDenom
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => forcedSquarePrimitive_deriv u) (hc.intervalIntegrable 2 (927/200))]
  norm_num [forcedSquarePrimitive,forcedSquareMass]

/-- No new fit: this is the exact integral of the original fixed-square lower bound. -/
def squarePayment : ℝ := 2/qEnd*(momentW-2*momentA*momentQ+momentA^2*forcedSquareMass)

theorem squarePayment_exact : squarePayment = (12176748552399127052917374315861301491116647374355516452663061368749849/3047344543765335765525957145085174651086098894988016510488370929964326401930:ℝ) := by
  norm_num [squarePayment,qEnd,momentDenom,momentA,momentW,momentQ,forcedSquareMass]

theorem squarePayment_pos : 0 < squarePayment := by
  rw [squarePayment_exact]
  norm_num

end F1FixedSquareRecovery
