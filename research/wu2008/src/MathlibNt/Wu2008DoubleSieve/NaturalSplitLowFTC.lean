import MathlibNt.Wu2008DoubleSieve.NaturalSplitDensity

namespace Wu2008DoubleSieve.NaturalSplitLowFTC
open Real Set MeasureTheory FixedCoefficientUpperEnclosure NaturalSplitDensity
open RefinedRetainedDensity
open RetainedSixthDensity (lam m zmax error)
open scoped Interval

noncomputable def c0 (x : ℝ) : ℝ :=
  (5197640254392384358547/154007680000000000 : ℝ)+(-83052670716238372616962613/121281048000000000000 : ℝ)*x^1+(4396309169202288475644954959/758006550000000000000 : ℝ)*x^2+(-28477865906893713100694815381/1137009825000000000000 : ℝ)*x^3+(62390038466581535062417154287/1137009825000000000000 : ℝ)*x^4+(-9169838704791446316363473893/189501637500000000000 : ℝ)*x^5

noncomputable def c1 (x : ℝ) : ℝ :=
  (-251970510126116144953150811/503836125120000000000 : ℝ)+(569960186695984231642146689/62979515640000000000 : ℝ)*x^1+(-18329033168780808009119656737547/275535380925000000000000 : ℝ)*x^2+(6106546858114777473064302809771/25831441961718750000000 : ℝ)*x^3+(-160446044181691299902396423653223/413303071387500000000000 : ℝ)*x^4+(3679655146706099558510272262309/17220961307812500000000 : ℝ)*x^5

noncomputable def c2 (x : ℝ) : ℝ :=
  (192340452760768926775739833/62979515640000000000 : ℝ)+(-1014296937633420841273979003/20993171880000000000 : ℝ)*x^1+(83618815653584039865495155627753/275535380925000000000000 : ℝ)*x^2+(-23665825528503197877884613567127/27553538092500000000000 : ℝ)*x^3+(9729827053580498615334231736117/9840549318750000000000 : ℝ)*x^4+(-10507007857332533765574247876087/34441922615625000000000 : ℝ)*x^5

noncomputable def c3 (x : ℝ) : ℝ :=
  (-179850930914132371167652321/18893854692000000000 : ℝ)+(430333264935723125885454348553/3306424571100000000000 : ℝ)*x^1+(-18913272230055529980760931123321/27553538092500000000000 : ℝ)*x^2+(1645762989864225571858408065343/1148064087187500000000 : ℝ)*x^3+(-10507007857332533765574247876087/11480640871875000000000 : ℝ)*x^4

noncomputable def c4 (x : ℝ) : ℝ :=
  (2873147421337951087164953269/188938546920000000000 : ℝ)+(-586571801788712299427973405109/3306424571100000000000 : ℝ)*x^1+(52039673005814190637154457579647/68883845231250000000000 : ℝ)*x^2+(-10507007857332533765574247876087/11480640871875000000000 : ℝ)*x^3

noncomputable def c5 (x : ℝ) : ℝ :=
  (-12687691379086934549163353/1259590312800000000 : ℝ)+(133681248043994967978970135253/1377676904625000000000 : ℝ)*x^1+(-10507007857332533765574247876087/34441922615625000000000 : ℝ)*x^2

theorem polynomial_eq (x y : ℝ) : low x y = c0 x*y^0+c1 x*y^1+c2 x*y^2+c3 x*y^3+c4 x*y^4+c5 x*y^5 := by
  norm_num [low,lowPrincipal,lowCorrection,reciprocalUpper,reciprocalLower,
    RetainedSixthDensity.chord,c0,c1,c2,c3,c4,c5,error,zmax,m,lam,a,b,s,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma]
  ring

noncomputable def inner (x y : ℝ) : ℝ := c0 x*y^1/1+c1 x*y^2/2+c2 x*y^3/3+c3 x*y^4/4+c4 x*y^5/5+c5 x*y^6/6

theorem inner_derivative (x y : ℝ) : HasDerivAt (inner x) (low x y) y := by
  rw [polynomial_eq]
  have h := (((((((((hasDerivAt_id y).pow 1).const_mul (c0 x)).div_const 1).add (((((hasDerivAt_id y).pow 2).const_mul (c1 x)).div_const 2))).add (((((hasDerivAt_id y).pow 3).const_mul (c2 x)).div_const 3))).add (((((hasDerivAt_id y).pow 4).const_mul (c3 x)).div_const 4))).add (((((hasDerivAt_id y).pow 5).const_mul (c4 x)).div_const 5))).add (((((hasDerivAt_id y).pow 6).const_mul (c5 x)).div_const 6)))
  convert! h using 1
  dsimp
  ring

noncomputable def moving (x : ℝ) : ℝ := inner x (lam-x)-inner x (cut x)
noncomputable def outer (x : ℝ) : ℝ :=
  (12952597244003/839726875200 : ℝ)*x^1+(-24678068972804987/440856609480000 : ℝ)*x^2+(560637509681552809/3306424571100000 : ℝ)*x^3+(-1127204258587018243/1653212285550000 : ℝ)*x^4+(3388405402976362807/1377676904625000 : ℝ)*x^5

theorem outer_derivative (x : ℝ) : HasDerivAt outer (moving x) x := by
  have h := (((((((hasDerivAt_id x).pow 1).const_mul (12952597244003/839726875200 : ℝ)).add ((((hasDerivAt_id x).pow 2).const_mul (-24678068972804987/440856609480000 : ℝ)))).add ((((hasDerivAt_id x).pow 3).const_mul (560637509681552809/3306424571100000 : ℝ)))).add ((((hasDerivAt_id x).pow 4).const_mul (-1127204258587018243/1653212285550000 : ℝ)))).add ((((hasDerivAt_id x).pow 5).const_mul (3388405402976362807/1377676904625000 : ℝ))))
  convert! h using 1
  norm_num [moving,inner,c0,c1,c2,c3,c4,c5,cut,lam,a,b,s,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma]
  ring

theorem polynomial_continuous : Continuous (fun p : ℝ × ℝ => low p.1 p.2) := by
  unfold low lowPrincipal lowCorrection reciprocalUpper reciprocalLower RetainedSixthDensity.chord
  fun_prop

theorem moving_continuous : Continuous moving := by
  unfold moving inner c0 c1 c2 c3 c4 c5 cut
  fun_prop

theorem inner_ftc (x : ℝ) : (∫ y in (cut x)..(lam-x), low x y) = moving x := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => inner_derivative x y)
  exact (polynomial_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)).intervalIntegrable _ _

noncomputable def rationalPart : ℝ := (10914500473995131197/7447730868905514768 : ℝ)

theorem polynomial_integral : 4*(∫ x in a..b, moving x) = rationalPart := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => outer_derivative x)
    (moving_continuous.intervalIntegrable a b)]
  norm_num [outer,rationalPart,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

end Wu2008DoubleSieve.NaturalSplitLowFTC
