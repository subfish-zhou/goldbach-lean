import GlobalSignedActualComparison

namespace Wu2008DoubleSieve.SixthReciprocalTightPayment
open Real Set MeasureTheory SharpLogRecurrence JointLogTotalComparison TotalEndpointComparison
open ClassicalLossBottleneck ClassicalAnalyticLeaves SharpMassBalance
open PositiveSixthFTC DynamicSixthEnvelope
open scoped Interval
noncomputable section

/-- The secant of the original reciprocal, with no fixed-density replacement. -/
def chord (l u t : ℝ) : ℝ := (l+u-t)/(l*u)

theorem reciprocal_chord {l u t : ℝ} (hl : 0 < l) (ht : l ≤ t) (hu : t ≤ u) :
    1/t ≤ chord l u t := by
  have ht0 : 0 < t := hl.trans_le ht
  have hu0 : 0 < u := ht0.trans_le hu
  unfold chord
  apply (div_le_div_iff₀ ht0 (mul_pos hl hu0)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hu)]

def X (x : ℝ) : ℝ := chord a b x
def Y (y : ℝ) : ℝ := chord b (lam-a) y
def Z (z : ℝ) : ℝ := chord (2*a) (1/2-a-b) z
def C (c : ℝ) : ℝ := chord (1/2-b) (1/2-a) c

def first (x y : ℝ) : ℝ :=
  (lam-x-y)^3/(464*a^3)*X x*Y y*Z (1/2-x-y)
def second (x : ℝ) : ℝ :=
  ((1/(2*a)^3+1/b^3)/464)*(lam-b-x)^3*
  ((2/3)*(1/2-x-2*a)*((1/2-x-2*a)^2+3*(1/2-x)^2))*C (1/2-x)^4*X x

theorem first_pointwise {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b (lam-x)) :
    sixthLogRegular x y ≤ Phase25.exactKernel x y+first x y := by
  have hg := Phase25.mask_geometry hx hy
  have hx0 := hg.1
  have hy0 := hg.2.1
  have hz0 := hg.2.2.2.1
  have ha := geometry.1
  have hb := geometry.2.2.1
  have hs2 : 2 ≤ truncatedSixthLowerS 0 x y := by
    apply (le_div_iff₀ ha).2
    dsimp [truncatedSixthLowerC]
    simpa only [sub_zero] using hg.2.2.2.2
  have hgap := SixthFullRationalEnclosure.gap_cubic (t := truncatedSixthLowerS 0 x y-1) (by linarith)
  have hdshape : truncatedSixthLowerS 0 x y-1-1 = (lam-x-y)/a := by
    unfold truncatedSixthLowerS truncatedSixthLowerC lam
    field_simp
    ring
  rw [hdshape] at hgap
  have he : Phase25.exactKernel x y = lowerLog (truncatedSixthLowerS 0 x y-1)/(x*y*(1/2-x-y)) := by
    have hz' : 1-x*2-y*2 ≠ 0 := by linarith [hg.2.2.2.1]
    simp only [Phase25.exactKernel,lowerLog,truncatedSixthLowerS,truncatedSixthLowerC,lam,sub_zero]
    field_simp [ha.ne',hg.1.ne',hg.2.1.ne',hg.2.2.2.1.ne',hz']
    ring
  have hX : 1/x ≤ X x := reciprocal_chord ha hx.1 hx.2
  have hY : 1/y ≤ Y y := reciprocal_chord hb hy.1 (by linarith [hy.2,hx.1])
  have hZ : 1/(1/2-x-y) ≤ Z (1/2-x-y) := reciprocal_chord
    (by positivity) hg.2.2.2.2 (by linarith [hx.1,hy.1])
  have hX0 : 0 ≤ X x := (by positivity : 0 ≤ 1/x).trans hX
  have hY0 : 0 ≤ Y y := (by positivity : 0 ≤ 1/y).trans hY
  have hm := mul_le_mul (mul_le_mul hX hY (by positivity) hX0) hZ (by positivity)
    (mul_nonneg hX0 hY0)
  have hn : 0 ≤ lam-x-y := by linarith [hy.2]
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ (lam-x-y)^3/(464*a^3) by positivity)
  have hi := div_le_div_of_nonneg_right hgap (mul_pos (mul_pos hg.1 hg.2.1) hg.2.2.2.1).le
  have hid : (((lam-x-y)/a)^3/464)/(x*y*(1/2-x-y)) =
      (lam-x-y)^3/(464*a^3)*((1/x)*(1/y)*(1/(1/2-x-y))) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hid,sub_div] at hi
  rw [sixth_log_retained hx hy,he]
  unfold first
  nlinarith only [hi,hm']

/-- Keep the endpoint cancellation abstract, without expanding its polynomial factors. -/
private theorem endpoint_payment_algebra {s0 r0 t l1 l2 q1 q2 k n c w : ℝ}
    (h : s0/t*((l1-q1)+(l2-q2)) ≤ n*c*w*k) :
    (s0*(l1+l2)+r0)/t ≤ (s0*(q1+q2)+r0)/t+k*n*c*w := by
  have he : (s0*(l1+l2)+r0)/t =
      (s0*(q1+q2)+r0)/t+s0/t*((l1-q1)+(l2-q2)) := by ring
  rw [he]
  calc
    _ ≤ (s0*(q1+q2)+r0)/t+n*c*w*k := _root_.add_le_add le_rfl h
    _ = _ := by ring

theorem second_pointwise {x : ℝ} (hx : x ∈ Icc a b) :
    Phase25.movingExact x ≤ Phase25.rationalInner (1/2-x)+second x := by
  have hg := Phase25.outer_geometry hx
  have hx0 := hg.1
  have hcpos := hg.2.1
  have hcapos := hg.2.2.2.1
  have ha := geometry.1
  have hb := geometry.2.2.1
  have h1 : 1 ≤ (1/2-x-b)/(2*a) := (le_div_iff₀ (by positivity)).2 (by linarith [hg.2.2.2.2])
  have h2 : 1 ≤ (1/2-x-2*a)/b := (le_div_iff₀ hb).2 (by linarith [hg.2.2.2.2])
  have he1 := SixthFullRationalEnclosure.gap_cubic h1
  have he2 := SixthFullRationalEnclosure.gap_cubic h2
  have he : ((1/2-x-b)/(2*a)-1)^3/464+((1/2-x-2*a)/b-1)^3/464 =
      ((1/(2*a)^3+1/b^3)/464)*(lam-b-x)^3 := by
    unfold lam
    field_simp
    ring
  have herr : (log ((1/2-x-b)/(2*a))-lowerLog ((1/2-x-b)/(2*a)))+
      (log ((1/2-x-2*a)/b)-lowerLog ((1/2-x-2*a)/b)) ≤
      ((1/(2*a)^3+1/b^3)/464)*(lam-b-x)^3 := by linarith only [he1,he2,he]
  have hs := Phase25.S_pos (h := 2*a) hg.2.1 (by linarith [hg.2.2.2.1])
  have hX : 1/x ≤ X x := reciprocal_chord ha hx.1 hx.2
  have hc0 : 0 < 1/2-b := by norm_num [b,truncatedSixthLowerBeta]
  have hC : 1/(1/2-x) ≤ C (1/2-x) := reciprocal_chord hc0
    (by linarith [hx.2]) (by linarith [hx.1])
  have hC0 : 0 ≤ C (1/2-x) := (by positivity : 0 ≤ 1/(1/2-x)).trans hC
  have hC4 := pow_le_pow_left₀ (by positivity : 0 ≤ 1/(1/2-x)) hC 4
  have hX0 : 0 ≤ X x := (by positivity : 0 ≤ 1/x).trans hX
  have hN : 0 ≤ (2/3:ℝ)*(1/2-x-2*a)*((1/2-x-2*a)^2+3*(1/2-x)^2) := by positivity
  have hp := mul_le_mul (mul_le_mul_of_nonneg_left hC4 hN) hX (by positivity)
    (mul_nonneg hN (pow_nonneg hC0 4))
  have hcoef : Phase25.S (1/2-x) (2*a)/x ≤
      ((2/3)*(1/2-x-2*a)*((1/2-x-2*a)^2+3*(1/2-x)^2))*C (1/2-x)^4*X x := by
    rw [Phase25.S_factor hg.2.1.ne']
    convert hp using 1 <;> first | rfl | field_simp
  have hcoef0 := (div_nonneg hs.le hg.1.le).trans hcoef
  have herr0 : 0 ≤ (log ((1/2-x-b)/(2*a))-lowerLog ((1/2-x-b)/(2*a)))+
      (log ((1/2-x-2*a)/b)-lowerLog ((1/2-x-2*a)/b)) :=
    add_nonneg (sub_nonneg.mpr (log_lower h1)) (sub_nonneg.mpr (log_lower h2))
  have hp' := mul_le_mul hcoef herr herr0 hcoef0
  rw [Phase25.movingExact_endpoint,Phase25.endpoint_difference hg.2.2.1 hg.2.2.2.1]
  unfold Phase25.rationalInner second
  rw [show (1/2:ℝ)-(1/2-x)=x by ring]
  exact endpoint_payment_algebra hp'

macro "fixed_num" : tactic => `(tactic| norm_num [first,second,X,Y,Z,C,chord,lam,a,b,
  truncatedSixthLowerAlpha,truncatedSixthLowerBeta])

def innerPrimitive (x y : ℝ) : ℝ :=
    (-15448183538111468607411/279665151680000000000)*y^1+
    (50758627239128725498332801/55933030336000000000000)*y^2+
    (-37078930757994021196602759/6991628792000000000000)*y^3+
    (52744960559021590990636857/3495814396000000000000)*y^4+
    (-185556263404294739132630127/8739535990000000000000)*y^5+
    (41535471254796276580977117/3495814396000000000000)*y^6+
    (6837938746626801572160363/3495814396000000000000)*x^1*y^1+
    (-12867493866244792056719983881/699162879200000000000000)*x^1*y^2+
    (6770401639130790845352641529/87395359900000000000000)*x^1*y^3+
    (-28554389874170405324204989493/174790719800000000000000)*x^1*y^4+
    (18021122937574350478028491487/109244199875000000000000)*x^1*y^5+
    (-7917865755337252272474941881/131093039850000000000000)*x^1*y^6+
    (-441082579031655641538877341/21848839975000000000000)*x^2*y^1+
    (22916090404629119139279949071/174790719800000000000000)*x^2*y^2+
    (-3418037283667393921145863423/8739535990000000000000)*x^2*y^3+
    (11961926073743567569710663691/21848839975000000000000)*x^2*y^4+
    (-7917865755337252272474941881/27311049968750000000000)*x^2*y^5+
    (984922692892363212785713773/10924419987500000000000)*x^3*y^1+
    (-35433575227940075575023946911/87395359900000000000000)*x^3*y^2+
    (3399478465335020779081562283/4369767995000000000000)*x^3*y^3+
    (-23753597266011756817424825643/43697679950000000000000)*x^3*y^4+
    (-2019624815498050900931307971/10924419987500000000000)*x^4*y^1+
    (45475663930301825178199321417/87395359900000000000000)*x^4*y^2+
    (-7917865755337252272474941881/16386629981250000000000)*x^4*y^3+
    (782454128645095268869257907/5462209993750000000000)*x^5*y^1+
    (-7917865755337252272474941881/43697679950000000000000)*x^5*y^2

def innerMass (x : ℝ) : ℝ :=
    (9928183090951791631293642060297/7869139801645657520000000000000)+
    (-12907381887731950296471658741933/716244520780854750000000000000)*x^1+
    (243488340337092602112281275631/9271773731791000000000000000)*x^2+
    (7600772292528747626684385921/9001722069700000000000000)*x^3+
    (-1215846452483675209098554501/209748863760000000000000)*x^4+
    (1196065045479006316481726623/87395359900000000000000)*x^5+
    (-1409946771088544735989403139/218488399750000000000000)*x^6+
    (-7917865755337252272474941881/655465199250000000000000)*x^7

def outerPrimitive (x : ℝ) : ℝ :=
    (53587965199753646917828847608658921124561209160577358092474149563/21756071591248487786527293101162588076012878841720080000000000000)*x^1+
    (-178371813389156660193735940792715704602763529676366855114517/10932285293582293178348428524416576905918215500000000000000)*x^2+
    (3466941546482495858095441393073281913937610667953303528149083/364349095247905424344866314936584423693397889000000000000000)*x^3+
    (13029482275198663317133917206748829861268433770091148415717/36608801331113330755575615668081831066907600000000000000)*x^4+
    (-1175510121144905745223308345256539715207226716979575151/803523562114266008199580387941597538800000000000000)*x^5+
    (651332936380478092343781390758932553786527720723/678325862168338637073168451139400000000000000)*x^6+
    (232505738855053616617934601599446841458748251/62724776687362479843230190750000000000000)*x^7+
    (622668902284487155388851575568427122899456929/215056377213814216605360654000000000000000)*x^8+
    (-186840760723608454403984041119557/6422505098329083090600000000)*x^9+
    (6251287353713922706560938509/718208210136997125000000)*x^10+
    (763974865440727416292201325383/11150182462376880365625000)*x^11+
    (-142846578089335244851209807598733/2140835032776361030200000000)*x^12

def payment : ℝ := 4*(outerPrimitive b-outerPrimitive a)

theorem inner_ftc (x : ℝ) : (∫ y in b..(lam-x), first x y) = innerMass x := by
  have hc : Continuous (first x) := by unfold first X Y Z chord; fun_prop
  have hd (y : ℝ) : HasDerivAt (innerPrimitive x) (first x y) y := by
    unfold innerPrimitive
    convert ((((((((((((((((((((((((((((hasDerivAt_id y).pow 1).const_mul ((-15448183538111468607411/279665151680000000000))).add (((hasDerivAt_id y).pow 2).const_mul ((50758627239128725498332801/55933030336000000000000)))).add (((hasDerivAt_id y).pow 3).const_mul ((-37078930757994021196602759/6991628792000000000000)))).add (((hasDerivAt_id y).pow 4).const_mul ((52744960559021590990636857/3495814396000000000000)))).add (((hasDerivAt_id y).pow 5).const_mul ((-185556263404294739132630127/8739535990000000000000)))).add (((hasDerivAt_id y).pow 6).const_mul ((41535471254796276580977117/3495814396000000000000)))).add (((hasDerivAt_id y).pow 1).const_mul ((6837938746626801572160363/3495814396000000000000)*x^1))).add (((hasDerivAt_id y).pow 2).const_mul ((-12867493866244792056719983881/699162879200000000000000)*x^1))).add (((hasDerivAt_id y).pow 3).const_mul ((6770401639130790845352641529/87395359900000000000000)*x^1))).add (((hasDerivAt_id y).pow 4).const_mul ((-28554389874170405324204989493/174790719800000000000000)*x^1))).add (((hasDerivAt_id y).pow 5).const_mul ((18021122937574350478028491487/109244199875000000000000)*x^1))).add (((hasDerivAt_id y).pow 6).const_mul ((-7917865755337252272474941881/131093039850000000000000)*x^1))).add (((hasDerivAt_id y).pow 1).const_mul ((-441082579031655641538877341/21848839975000000000000)*x^2))).add (((hasDerivAt_id y).pow 2).const_mul ((22916090404629119139279949071/174790719800000000000000)*x^2))).add (((hasDerivAt_id y).pow 3).const_mul ((-3418037283667393921145863423/8739535990000000000000)*x^2))).add (((hasDerivAt_id y).pow 4).const_mul ((11961926073743567569710663691/21848839975000000000000)*x^2))).add (((hasDerivAt_id y).pow 5).const_mul ((-7917865755337252272474941881/27311049968750000000000)*x^2))).add (((hasDerivAt_id y).pow 1).const_mul ((984922692892363212785713773/10924419987500000000000)*x^3))).add (((hasDerivAt_id y).pow 2).const_mul ((-35433575227940075575023946911/87395359900000000000000)*x^3))).add (((hasDerivAt_id y).pow 3).const_mul ((3399478465335020779081562283/4369767995000000000000)*x^3))).add (((hasDerivAt_id y).pow 4).const_mul ((-23753597266011756817424825643/43697679950000000000000)*x^3))).add (((hasDerivAt_id y).pow 1).const_mul ((-2019624815498050900931307971/10924419987500000000000)*x^4))).add (((hasDerivAt_id y).pow 2).const_mul ((45475663930301825178199321417/87395359900000000000000)*x^4))).add (((hasDerivAt_id y).pow 3).const_mul ((-7917865755337252272474941881/16386629981250000000000)*x^4))).add (((hasDerivAt_id y).pow 1).const_mul ((782454128645095268869257907/5462209993750000000000)*x^5))).add (((hasDerivAt_id y).pow 2).const_mul ((-7917865755337252272474941881/43697679950000000000000)*x^5))) using 1 <;> first | rfl | (fixed_num; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) (hc.intervalIntegrable b (lam-x))]
  unfold innerPrimitive innerMass
  fixed_num
  ring

theorem error_ftc : (∫ x in a..b, second x+innerMass x) = payment/4 := by
  have hc : Continuous (fun x : ℝ => second x+innerMass x) := by
    unfold second C X chord innerMass; fun_prop
  have hd (x : ℝ) : HasDerivAt outerPrimitive (second x+innerMass x) x := by
    unfold outerPrimitive innerMass
    convert ((((((((((((((hasDerivAt_id x).pow 1).const_mul ((53587965199753646917828847608658921124561209160577358092474149563/21756071591248487786527293101162588076012878841720080000000000000))).add (((hasDerivAt_id x).pow 2).const_mul ((-178371813389156660193735940792715704602763529676366855114517/10932285293582293178348428524416576905918215500000000000000)))).add (((hasDerivAt_id x).pow 3).const_mul ((3466941546482495858095441393073281913937610667953303528149083/364349095247905424344866314936584423693397889000000000000000)))).add (((hasDerivAt_id x).pow 4).const_mul ((13029482275198663317133917206748829861268433770091148415717/36608801331113330755575615668081831066907600000000000000)))).add (((hasDerivAt_id x).pow 5).const_mul ((-1175510121144905745223308345256539715207226716979575151/803523562114266008199580387941597538800000000000000)))).add (((hasDerivAt_id x).pow 6).const_mul ((651332936380478092343781390758932553786527720723/678325862168338637073168451139400000000000000)))).add (((hasDerivAt_id x).pow 7).const_mul ((232505738855053616617934601599446841458748251/62724776687362479843230190750000000000000)))).add (((hasDerivAt_id x).pow 8).const_mul ((622668902284487155388851575568427122899456929/215056377213814216605360654000000000000000)))).add (((hasDerivAt_id x).pow 9).const_mul ((-186840760723608454403984041119557/6422505098329083090600000000)))).add (((hasDerivAt_id x).pow 10).const_mul ((6251287353713922706560938509/718208210136997125000000)))).add (((hasDerivAt_id x).pow 11).const_mul ((763974865440727416292201325383/11150182462376880365625000)))).add (((hasDerivAt_id x).pow 12).const_mul ((-142846578089335244851209807598733/2140835032776361030200000000)))) using 1 <;> first | rfl | (fixed_num; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable a b)]
  unfold payment
  ring
theorem inner_cap {x : ℝ} (hx : x ∈ Icc a b) :
    (∫ y in b..s, sixthLogRegular x y) ≤ Phase25.rationalInner (1/2-x)+
      second x+innerMass x := by
  have hc := sixth_log_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
  have hp : Continuous (first x) := by unfold first X Y Z chord; fun_prop
  have he := inner_ftc x
  have hi := intervalIntegral.integral_mono_on (μ := volume) (moving_geometry hx).1
    (hc.intervalIntegrable b (lam-x)) ((Phase25.inner_integrable hx).add (hp.intervalIntegrable b (lam-x)))
    (fun y hy => first_pointwise hx hy)
  rw [intervalIntegral.integral_add (Phase25.inner_integrable hx) (hp.intervalIntegrable b (lam-x)),
    Phase25.inner_ftc hx,he] at hi
  have hcomp : (∫ y in (lam-x)..s, sixthLogRegular x y) = 0 := by
    calc
      _ = ∫ _y in (lam-x)..s, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        have hy' : y ∈ Icc (lam-x) s := uIcc_of_le (moving_geometry hx).2 ▸ hy
        have hh := sixth_log_pointwise hx ⟨(moving_geometry hx).1.trans hy'.1,hy'.2⟩
        rw [sixth_complement_zero hx hy'] at hh
        have hn := sixth_log_nonnegative x y
        linarith only [hh.1,hn]
      _ = 0 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable b (lam-x)) (hc.intervalIntegrable (lam-x) s)
  simp only [Function.comp_apply] at hi hadd
  rw [hcomp,add_zero] at hadd
  rw [← hadd]
  linarith only [hi,second_pointwise hx]

/-- An upper bound on the actual entire log recovery, not on a lower certificate. -/
theorem sixth_log_loss_enclosure : 0 ≤ sixthLogIntegral-AnalyticTotalThreshold.sixthEndpoint ∧
    sixthLogIntegral-AnalyticTotalThreshold.sixthEndpoint ≤ payment := by
  have hc : Continuous (fun x : ℝ => ∫ y in b..s, sixthLogRegular x y) := by
    apply gamma5Gain_moving_integral (f := sixthLogRegular) sixth_log_continuous <;> fun_prop
  have hp : Continuous (fun x : ℝ => second x+innerMass x) := by unfold second C X chord innerMass; fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) geometry.2.1
    (hc.intervalIntegrable a b) (Phase25.rationalInner_integrable.add (hp.intervalIntegrable a b))
    (fun x hx => show (∫ y in b..s, sixthLogRegular x y) ≤
      Phase25.rationalInner (1/2-x)+(second x+innerMass x) by
      linarith only [inner_cap hx])
  rw [intervalIntegral.integral_add Phase25.rationalInner_integrable (hp.intervalIntegrable a b),
    Phase25.outer_ftc,error_ftc] at hi
  refine ⟨sub_nonneg.mpr sixth_endpoint_le_logIntegral,?_⟩
  unfold sixthLogIntegral AnalyticTotalThreshold.sixthEndpoint
  linarith only [hi]


theorem payment_rational : payment = (2928924908403303183348338037815541770827056963258188853285849551823941510137/53755391426465427771763631972728312678571978758655629987351184793600000000000) := by
  norm_num [payment,outerPrimitive,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem payment_bounds : (54486/1000000:ℝ) < payment ∧ payment < 54487/1000000 := by
  rw [payment_rational]
  norm_num

theorem full_log_loss_lt : sixthLogIntegral-AnalyticTotalThreshold.sixthEndpoint < 54487/1000000 :=
  sixth_log_loss_enclosure.2.trans_lt payment_bounds.2

theorem full_actual_sixth_loss_lt : AnalyticTotalThreshold.sixthLoss < 54497/1000000 := by
  have h := sixth_loss_localization.2
  have h6 := full_log_loss_lt
  linarith only [h,h6]

open GlobalSignedActualComparison

def upperReal : ℝ :=
  (rationalPart+packet log+FifthActualIntegralRecovery.recurrenceCap+
    payment+1/100000+
    Phase24.newFour-FourTrueLowerTight.actualLower)/4+retainedExtra

theorem actual_upper_real : JointHMotherPayment.unroundedCoefficient < upperReal := by
  have hw := ExactWeightTripleEnclosure.window_payments
  have hb := BaseGSharedActualRecovery.base_exact
  have hbeta := HighSharedKernelMagnitude.beta_bound
  have hg := BaseGSharedActualRecovery.g_exact
  have he := ExactWeightTripleEnclosure.upper_joint_identity
  have ht : JointSharedTightEnclosure.triple ≤ base log+
      ExactWeightTripleEnclosure.upperEnvelope log log := by
    unfold JointSharedTightEnclosure.triple
    rw [BaseGSharedActualRecovery.shared_exact]
    unfold base BaseGSharedActualRecovery.baseLogRemainder at *
    linarith only [hw.2.1,hw.2.2.2.1,hw.2.2.2.2,hb,hbeta,hg,he]
  have hj := JFourRemainingMagnitude.j_remaining_real_interval.2
  unfold JFourRemainingMagnitude.jRemaining JFourRemainingMagnitude.jCapReal at hj
  rw [j_lower_identity] at hj
  have h5 := FifthLogTotalMagnitude.integral_bounds.2
  have e5 := FifthActualIntegralRecovery.integral_distance.2
  have h6 := sixth_log_loss_enclosure.2
  have e6 := ClassicalLossBottleneck.sixth_recurrence_integral_cap.2
  have h4 := FourTrueLowerTight.actual_four_lower
  rw [cancelled_actual_identity]
  unfold upperReal packet mainLogs logTotal D AnalyticTotalThreshold.fourLoss
    AnalyticTotalThreshold.fifthEndpoint FifthLogTotalMagnitude.endpoint at *
  rw [← log_div (by norm_num [b,truncatedSixthLowerBeta])
    (by norm_num [a,truncatedSixthLowerAlpha])] at h5
  rw [← log_div (by norm_num [b,truncatedSixthLowerBeta])
    (by norm_num [a,truncatedSixthLowerAlpha])]
  rw [log_two]
  unfold SignedTotalCorrelation.d2 SignedTotalCorrelation.e2 at hj
  rw [log_two] at hj
  linarith only [ht,hj,h5,e5,h6,e6,h4]

def upperRational : ℝ := rationalTotal+
  (packet (fun _ => 0)+collected lowerLog V-logPayment-JointJLossStrength.fixedRecovery+
    FifthActualIntegralRecovery.recurrenceCap+payment+1/100000+
    Phase24.newFour-FourTrueLowerTight.actualLower)/4+
  (328543353599/72210108813375-Phase20.fixedPsi)+354/1000000

theorem actual_upper : JointHMotherPayment.unroundedCoefficient < upperRational := by
  have hr := fixedCertificate_exact
  unfold fixedCertificate classicalPayment at hr
  have hp := PsiG18Strength.psi_loss_upper
  have hg := PsiG18Strength.g18_bounds.2
  have hc := collected_payment
  have hu := actual_upper_real
  unfold upperReal at hu
  rw [collection] at hu
  unfold upperRational retainedExtra Phase20.psiPaymentLoss at *
  linarith only [hr,hp,hg,hc,hu]

/-- Literal substitution into the parent's global endpoint, with the original quarter weight. -/
theorem upper_shift : upperRational = GlobalSignedActualComparison.upperRational-
    (SixthFullRationalEnclosure.payment-payment)/4 := by
  unfold upperRational GlobalSignedActualComparison.upperRational
  ring

def upperRemainder : ℝ := upperRational-8*lowerLog (5000/4469)

theorem remainder_shift : upperRemainder = GlobalSignedActualComparison.upperRemainder-
    (SixthFullRationalEnclosure.payment-payment)/4 := by
  rw [upperRemainder,upper_shift]
  unfold GlobalSignedActualComparison.upperRemainder
  ring

theorem quarter_decrease_bounds : (3506/1000000:ℝ) <
    (SixthFullRationalEnclosure.payment-payment)/4 ∧
    (SixthFullRationalEnclosure.payment-payment)/4 < 3507/1000000 := by
  rw [SixthFullRationalEnclosure.payment_rational,payment_rational]
  norm_num

theorem upper_exact : upperRational = 1025918560989639910578747088982418804657101332724281869279370612659721793624292438848630867066392769294744852894330691766011369952390633140953472365972408668253901333364998234176636954026915524766218828689419118591031507865884583949497553548314491428132505576588426828102255928696300377888712375911359713017602115368385593758346555432732697634215032111/1122920570776473089584766627526823146118260997196453327408953652215330051779511860935653443455292483981630832535806830073849125985759463318381310840113111833123949557247238380440535424825088837261174382956609049416128957219931997661982031965197966686191052751229614798994023693115573988388030385287156746236226389539170045283622312016872243200000000000 := by
  unfold upperRational
  rw [payment_rational]
  all_num

theorem remainder_exact : upperRemainder = 2994617387736573595131922936955368618141608738379235963177613013875361896302019039673166728577385890867089308128874639726196964377913637566652080587807781444515889843598854838983783363473893515619821536031625807581756053604386536186974925047832690439659120473487040621172612939319599890775415811996587971821512409923101253878949663895459496301160580054940923/194050436178696309760815433612928130322844706358395763745042357136907740811639768866288028664458498089589060179014654005534960940791429468430917201906678828044983829985823942383365690984223355575993244763813085541573658216629362064846170733390082109298216974234043876307614949218335438878132707725759987003214951628372847830213586045273886295370137600000000000 := by
  rw [remainder_shift,GlobalSignedActualComparison.upperRemainder_exact,
    SixthFullRationalEnclosure.payment_rational,payment_rational]
  norm_num

theorem remainder_bounds : (15432/1000000:ℝ) < upperRemainder ∧
    upperRemainder < 15433/1000000 := by
  rw [remainder_exact]
  norm_num

theorem actual_Q_bounds : (822040/1000000:ℝ) < JointHMotherPayment.unroundedCoefficient ∧
    JointHMotherPayment.unroundedCoefficient < 913617/1000000 := by
  have hu : upperRational < (913617/1000000:ℝ) := by rw [upper_exact]; norm_num
  exact ⟨GlobalSignedActualComparison.actual_Q_rational_bounds.1,actual_upper.trans hu⟩

/-- This improved upper route still straddles the target; no claim about actual Q's sign. -/
theorem actual_target_lower : (-15433/1000000:ℝ) <
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient := by
  have ht := log_lower (by norm_num : (1:ℝ) ≤ 5000/4469)
  have hu := actual_upper
  have hr := remainder_bounds.2
  unfold upperRemainder AnalyticTotalThreshold.target at *
  linarith only [ht,hu,hr]

/-- Even zero nonnegative sixth payment cannot close this fixed upper ledger alone. -/
theorem fixed_other_payments_floor : (1800/1000000:ℝ) <
    GlobalSignedActualComparison.upperRemainder-SixthFullRationalEnclosure.payment/4 := by
  rw [GlobalSignedActualComparison.upperRemainder_exact,SixthFullRationalEnclosure.payment_rational]
  norm_num

end
end Wu2008DoubleSieve.SixthReciprocalTightPayment
