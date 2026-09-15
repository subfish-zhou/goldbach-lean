import PositiveTwoP2

namespace QtwoWeightedMoment
open Real Set MeasureTheory Wu2008DoubleSieve
open FixedCoefficientUpperEnclosure (a b)
noncomputable section

def meanXY : ℝ := a*b+7*(b-a)^2/30
def P (x y : ℝ) : ℝ := (2*b-x-y)*(x+y-2*a)
def rate : ℝ := GlobalLowerSlack.scalarRate/a^3
def density (x y : ℝ) : ℝ := rate*P x y*(2/meanXY-x*y/meanXY^2)
def gain : ℝ := (5/3)*rate*(b-a)^4/meanXY

theorem params : 0 < a ∧ a < b ∧ 0 < meanXY ∧ meanXY < b^2 := by
  norm_num [a,b,meanXY,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem reciprocal_tangent {z m : ℝ} (hz : 0 < z) (hm : 0 < m) :
    2/m-z/m^2 ≤ 1/z := by
  apply (le_div_iff₀ hz).mpr
  have h := sq_nonneg (z-m)
  field_simp [hm.ne']
  nlinarith only [h]

def innerMoment (y : ℝ) : ℝ := y*(-(y^4-a^4)/4+
  (2*a+2*b-2*y)*(y^3-a^3)/3+(2*b-y)*(y-2*a)*(y^2-a^2)/2)
def outerMoment (y : ℝ) : ℝ := -17*y^6/72+(a+b)*y^5/3+
  (-2*a*b+a^2/2)*y^4/4+(2*a^3/3-(a+b)*a^2)*y^3/3+
  (-5*a^4/12+4*a^3*b/3)*y^2/2

theorem inner_moment (y : ℝ) : (∫ x in a..y, x*y*P x y) = innerMoment y := by
  let F : ℝ → ℝ := fun x => y*(-x^4/4+(2*a+2*b-2*y)*x^3/3+
    (2*b-y)*(y-2*a)*x^2/2)
  have hd (x : ℝ) : HasDerivAt F (x*y*P x y) x := by
    convert! (((((hasDerivAt_id x).pow 4).neg.div_const 4).add
      ((((hasDerivAt_id x).pow 3).const_mul (2*a+2*b-2*y)).div_const 3)).add
      ((((hasDerivAt_id x).pow 2).const_mul ((2*b-y)*(y-2*a))).div_const 2)).const_mul y using 1 ;
      first | rfl | (dsimp [F,P]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by unfold P; fun_prop : Continuous (fun x => x*y*P x y)).intervalIntegrable _ _)]
  dsimp [F,innerMoment]; ring

theorem outer_moment : (∫ y in a..b, innerMoment y) =
    (5/12)*(b-a)^4*meanXY := by
  have hd (y : ℝ) : HasDerivAt outerMoment (innerMoment y) y := by
    convert! ((((((hasDerivAt_id y).pow 6).const_mul (-17/72)).add
      (((hasDerivAt_id y).pow 5).const_mul ((a+b)/3))).add
      (((hasDerivAt_id y).pow 4).const_mul ((-2*a*b+a^2/2)/4))).add
      (((hasDerivAt_id y).pow 3).const_mul ((2*a^3/3-(a+b)*a^2)/3))).add
      (((hasDerivAt_id y).pow 2).const_mul ((-5*a^4/12+4*a^3*b/3)/2)) using 1 <;>
      first | (funext x; dsimp [outerMoment]; ring) | (dsimp [innerMoment]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
    ((by unfold innerMoment; fun_prop : Continuous innerMoment).intervalIntegrable _ _)]
  unfold outerMoment meanXY; ring

def innerDensity (y : ℝ) : ℝ :=
  (2*b^2/meanXY)*GlobalLowerSlack.innerPoly y-rate/meanXY^2*innerMoment y

theorem density_split (x y : ℝ) : density x y =
    (2*b^2/meanXY)*GlobalLowerSlack.gainDensity x y-rate/meanXY^2*(x*y*P x y) := by
  unfold density GlobalLowerSlack.gainDensity GlobalLowerSlack.densityRate rate P
  field_simp [params.1.ne', (params.1.trans params.2.1).ne', params.2.2.1.ne']

theorem inner_density (y : ℝ) : (∫ x in a..y, density x y) = innerDensity y := by
  simp_rw [density_split]
  rw [intervalIntegral.integral_sub
    (((by unfold GlobalLowerSlack.gainDensity; fun_prop :
      Continuous (fun x => GlobalLowerSlack.gainDensity x y)).intervalIntegrable _ _).const_mul _)
    (((by unfold P; fun_prop : Continuous (fun x => x*y*P x y)).intervalIntegrable _ _).const_mul _)]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    GlobalLowerSlack.innerPoly_ftc,inner_moment]
  rfl

theorem gain_ftc : 4*(∫ y in a..b, innerDensity y) = gain := by
  unfold innerDensity
  rw [intervalIntegral.integral_sub
    (((by unfold GlobalLowerSlack.innerPoly; fun_prop : Continuous GlobalLowerSlack.innerPoly).intervalIntegrable _ _).const_mul _)
    (((by unfold innerMoment; fun_prop : Continuous innerMoment).intervalIntegrable _ _).const_mul _)]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,outer_moment]
  have h := GlobalLowerSlack.fifthGain_ftc
  unfold GlobalLowerSlack.fifthGain GlobalLowerSlack.densityRate at h
  unfold gain rate
  field_simp [params.2.2.1.ne',params.1.ne',(params.1.trans params.2.1).ne'] at h ⊢
  nlinarith only [h]

end
end QtwoWeightedMoment
