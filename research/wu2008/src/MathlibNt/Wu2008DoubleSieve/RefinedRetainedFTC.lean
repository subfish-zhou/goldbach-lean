import MathlibNt.Wu2008DoubleSieve.RefinedRetainedDensity

namespace Wu2008DoubleSieve.RefinedRetainedFTC
open Real Set MeasureTheory
open FixedCoefficientUpperEnclosure RefinedRetainedDensity
open RetainedSixthDensity (lam m zmax error correction moving_geometry tail_zero)
open scoped Interval

noncomputable def c0 (x : ℝ) : ℝ :=
  (1614196250345012438624169600754474558258337/158978726599481145318558173880000000000 : ℝ)+(-51539957412544167136872285160049140927096097/241169184768630378213832181250000000000 : ℝ)*x^1+(113961681631740321600484911918174013230850321/58536209895298635488794218750000000000 : ℝ)*x^2+(-2113473195733679149047234424350736907/227325086972033535878812500000 : ℝ)*x^3+(661574615565323974763306196699173332879/28415635871504191984851562500000 : ℝ)*x^4+(-65408403260256179548677190977/2756095079464843750000 : ℝ)*x^5

noncomputable def c1 (x : ℝ) : ℝ :=
  (-9309025172913149890525326896245424982295552673/57788767118911396323295896205380000000000 : ℝ)+(276443640858403730093514574564462384166735154713/87664998663397142480727997884375000000000 : ℝ)*x^1+(-534843414911899547352858949632007553326911934009/21277912296941054000176698515625000000000 : ℝ)*x^2+(1016001014885693883552500485557990505231583/10329083639291773786493542968750000 : ℝ)*x^3+(-187569384944879243852594007362969349779459/1032908363929177378649354296875000 : ℝ)*x^4+(112428389292739626717320338822233/1001840561385470703125000 : ℝ)*x^5

noncomputable def c2 (x : ℝ) : ℝ :=
  (944723671616157977976913475384981552447347949/841583987168612567814988779690000000000 : ℝ)+(-24281925438897709589727501101692497569373047969/1276674737816463240010601910937500000000 : ℝ)*x^1+(39564457836948190209245611423969880153023747717/309872509178753213594806289062500000000 : ℝ)*x^2+(-1357041305979388949403810949766990163241527/3443027879763924595497847656250000 : ℝ)*x^3+(62854977869570685989642447032066/125230070173183837890625 : ℝ)*x^4+(-84000637798372909358686658415529/500920280692735351562500 : ℝ)*x^5

noncomputable def c3 (x : ℝ) : ℝ :=
  (-10643022111715883702635780165376084567/2644245411658694089342347000000 : ℝ)+(47553978316660001867599554468078824775637/826326691143341902919483437500000 : ℝ)*x^1+(-548225191533016390521143663799933556233079/1721513939881962297748923828125000 : ℝ)*x^2+(721831718445565547652510078958907/1001840561385470703125000 : ℝ)*x^3+(-252001913395118728076059975246587/500920280692735351562500 : ℝ)*x^4

noncomputable def c4 (x : ℝ) : ℝ :=
  (1215407215877098243631616249130204949/165265338228668380583896687500 : ℝ)+(-36239228628200760483240374561928514279937/413163345571670951459741718750000 : ℝ)*x^1+(192428762596196569211441392218581/500920280692735351562500 : ℝ)*x^2+(-252001913395118728076059975246587/500920280692735351562500 : ℝ)*x^3

noncomputable def c5 (x : ℝ) : ℝ :=
  (-710042219205073866182756657/128235591857340250000 : ℝ)+(1068744808213069039403838858251/20036811227709414062500 : ℝ)*x^1+(-84000637798372909358686658415529/500920280692735351562500 : ℝ)*x^2

 theorem polynomial_eq (x y : ℝ) : polynomial x y = c0 x*y^0+c1 x*y^1+c2 x*y^2+c3 x*y^3+c4 x*y^4+c5 x*y^5 := by
  norm_num [polynomial,principal,correction,reciprocalUpper,reciprocalLower,RetainedSixthDensity.chord,c0,c1,c2,c3,c4,c5,error,zmax,m,lam,a,b,s,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma]
  ring

noncomputable def inner (x y : ℝ) : ℝ := c0 x*y^1/1+c1 x*y^2/2+c2 x*y^3/3+c3 x*y^4/4+c4 x*y^5/5+c5 x*y^6/6

 theorem inner_derivative (x y : ℝ) : HasDerivAt (inner x) (polynomial x y) y := by
  rw [polynomial_eq]
  have h := (((((((((hasDerivAt_id y).pow 1).const_mul (c0 x)).div_const 1).add ((((hasDerivAt_id y).pow 2).const_mul (c1 x)).div_const 2)).add ((((hasDerivAt_id y).pow 3).const_mul (c2 x)).div_const 3)).add ((((hasDerivAt_id y).pow 4).const_mul (c3 x)).div_const 4)).add ((((hasDerivAt_id y).pow 5).const_mul (c4 x)).div_const 5)).add ((((hasDerivAt_id y).pow 6).const_mul (c5 x)).div_const 6))
  convert! h using 1
  dsimp
  ring

noncomputable def moving (x : ℝ) : ℝ := inner x (lam-x)-inner x b
noncomputable def outer (x : ℝ) : ℝ :=
  (721380414397306068589092640545442813393/5685394929829865289172704420000000000 : ℝ)*x^1+(-138443547722431792405658242244093622808889/137995022568686050708075350000000000000 : ℝ)*x^2+(8547474002471132966611570052184850277730562381/1565154953185294855961894919375000000000000 : ℝ)*x^3+(-169109819293187640462487647407701820365678967963/6311879903764594258612415847675000000000000 : ℝ)*x^4+(8454057583161104211607259362099739898507831449/76600484268987794400636114656250000000000 : ℝ)*x^5+(-1478544872346109492924150862610628692749028967/5577705165217557844706513203125000000000 : ℝ)*x^6+(13653332795961309420431043943120120840919/72303585475042416505454800781250000 : ℝ)*x^7+(19871032710726372197265279933197/160294489821675312500000000 : ℝ)*x^8+(84000637798372909358686658415529/270496951574077089843750000 : ℝ)*x^9

 theorem outer_derivative (x : ℝ) : HasDerivAt outer (moving x) x := by
  have h := (((((((((((hasDerivAt_id x).pow 1).const_mul (721380414397306068589092640545442813393/5685394929829865289172704420000000000 : ℝ)).add (((hasDerivAt_id x).pow 2).const_mul (-138443547722431792405658242244093622808889/137995022568686050708075350000000000000 : ℝ))).add (((hasDerivAt_id x).pow 3).const_mul (8547474002471132966611570052184850277730562381/1565154953185294855961894919375000000000000 : ℝ))).add (((hasDerivAt_id x).pow 4).const_mul (-169109819293187640462487647407701820365678967963/6311879903764594258612415847675000000000000 : ℝ))).add (((hasDerivAt_id x).pow 5).const_mul (8454057583161104211607259362099739898507831449/76600484268987794400636114656250000000000 : ℝ))).add (((hasDerivAt_id x).pow 6).const_mul (-1478544872346109492924150862610628692749028967/5577705165217557844706513203125000000000 : ℝ))).add (((hasDerivAt_id x).pow 7).const_mul (13653332795961309420431043943120120840919/72303585475042416505454800781250000 : ℝ))).add (((hasDerivAt_id x).pow 8).const_mul (19871032710726372197265279933197/160294489821675312500000000 : ℝ))).add (((hasDerivAt_id x).pow 9).const_mul (84000637798372909358686658415529/270496951574077089843750000 : ℝ)))
  convert! h using 1
  norm_num [moving,inner,c0,c1,c2,c3,c4,c5,lam,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  ring

 theorem polynomial_continuous : Continuous (fun p : ℝ × ℝ => polynomial p.1 p.2) := by
  unfold polynomial principal correction reciprocalUpper reciprocalLower RetainedSixthDensity.chord
  fun_prop
 theorem moving_continuous : Continuous moving := by
  unfold moving inner c0 c1 c2 c3 c4 c5
  fun_prop
 theorem inner_ftc (x : ℝ) : (∫ y in b..lam-x, polynomial x y) = moving x := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => inner_derivative x y)
  exact (polynomial_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)).intervalIntegrable b (lam-x)

noncomputable def rationalSixth : ℝ := (193587106291061386200618482775001436915301129556878573727/42032841380095105717241393734501540651301004120000000000 : ℝ)
 theorem polynomial_integral : 4*(∫ x in a..b, moving x) = rationalSixth := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => outer_derivative x)
    (moving_continuous.intervalIntegrable a b)]
  norm_num [outer,rationalSixth,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

 theorem actual_sixth_upper : truncatedSixthLowerF6lin ≤ rationalSixth := by
  have hp := truncatedSixthLower_parameters
  have hc : Continuous (fun v : ℝ × ℝ => truncatedSixthZeroDeltaRegular 0 (v.1,v.2)) :=
    truncatedSixthZeroDelta_regular_continuous.comp (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)
  have hi : Continuous (fun x : ℝ => ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) := by
    apply gamma5Gain_moving_integral
      (f := fun x y : ℝ => truncatedSixthZeroDeltaRegular 0 (x,y)) hc <;> fun_prop
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) :
      (∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) ≤ moving x := by
    have hc1 := hc.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
    have hzero : (∫ y in (lam-x)..s, truncatedSixthZeroDeltaRegular 0 (x,y)) = 0 := by
      calc
        _ = ∫ _y in (lam-x)..s, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro y hy
          exact tail_zero hx (uIcc_of_le (moving_geometry hx).2 ▸ hy)
        _ = 0 := by simp
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc1.intervalIntegrable b (lam-x)) (hc1.intervalIntegrable (lam-x) s)
    have hmono := intervalIntegral.integral_mono_on (μ := volume) (moving_geometry hx).1
      (hc1.intervalIntegrable b (lam-x))
      ((polynomial_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)).intervalIntegrable b (lam-x))
      (fun y hy => retained_density_upper hx hy)
    simp only [Function.comp_apply] at hsplit hmono
    rw [inner_ftc] at hmono
    rw [hzero] at hsplit
    linarith
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hp.2.1.le
    (hi.intervalIntegrable a b) (moving_continuous.intervalIntegrable a b) hpoint
  have he := truncatedSixthZeroDelta_extension_eq (by norm_num : (0 : ℝ) ≤ 0)
  change (4*∫ x in a..b, ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) =
    truncatedSixthLowerF6lin at he
  have hf := polynomial_integral
  linarith

end Wu2008DoubleSieve.RefinedRetainedFTC
