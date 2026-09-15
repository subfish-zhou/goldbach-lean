import TailRationalBasis

noncomputable section
open Real Set MeasureTheory TailRationalBasis
open scoped Interval
namespace TailFiniteFTC.AB21

def c1_1 : ℝ := -20815910318716375235479058848041567927902746337120982020138687118093755/1664675086095214024514996366567953622074532635204676021497978256958192
def c1_2 : ℝ := 56786631502648788069442810658137397587189249258141471075/85772299802181128923306060810452382768159921396116833328
def c1_3 : ℝ := -1150024013416629247527572663531105629075885/39774720768789145626768181752215853208797168
def c1_4 : ℝ := 4731461088278512765771254623/6148171441066714252728725198736
def c3_1 : ℝ := -18255459552045643861707572473252222529709304089068277428112745993728906293440/22565005408157267520708920438042850578292952936901952182156836422421368017829
def c3_2 : ℝ := -225013711374690115389658821118155289237775266657936816879264640/1635324943524786334638800572791428264436627940068788973860424561
def c3_3 : ℝ := -2323218186550720763773397292437015568114786667520/118514825170287283899877601172693020054187068087949
def c3_4 : ℝ := -20020777672350534887924581106514944/8588974222376539651892446700321203641
def c4_1 : ℝ := 871679979859398357225124738377880091964324319/465873770899936451230739930010375741183065507954700
def c4_2 : ℝ := 388833196388008567575799780537561/320114816352739838666333785684410180000
def c4_3 : ℝ := 0
def c4_4 : ℝ := 0
def c5_1 : ℝ := -14485332744589542138714324114729556097476189489332509713582315645224710272/6348844721700858382427933784188391428758472768916401961926218906739674263569025
def c5_2 : ℝ := -4110175748462360958572554491560553462687729150071510782788284/3244941738209200120200917538605676975095805982076047186487088193125
def c5_3 : ℝ := 185205044931041700800987703312663729849416411417476/81267178510551309488066091269604705648736547213252015625
def c5_4 : ℝ := -6251404789748121099371838147231665400767/8141106788204568280106268087802387798045312500
def g1 : ℝ := -1185522824576021344728562472537342287697947831421960000/20938944405986616145618203276629939784492413356887987
def f1 : ℝ := 1951396844631284739884782227414249046085686901056082500/6979648135328872048539401092209979928164137785629329
def g2 : ℝ := -967941566889270883678244346800974024750791850944545366433038439287/969109014307666004342255234152529755350427396295603441064692497732968
def f2 : ℝ := -1089922361841217641439903216404665399004159958118188339396301825/4486615806979935205288218676632082200696423130998164079003206008023

def kernel (u : ℝ) : ℝ := ((36020403044979695187527821/17146080000000000000000)*u+(-168911804590077320435708501/38578680000000000000000)*u^2+(16464564430971311257139741/10287648000000000000000)*u^3+(166674037133775995342793889/66134880000000000000000)*u^4+(-357071369486233961518799671/176359680000000000000000)*u^5+(-81806631076655738540317727/264539520000000000000000)*u^6+(712676315527108717079288543/1058158080000000000000000)*u^7+(-19046055973629192296306999/296284262400000000000000)*u^8+(-12499748470719186757834301729/118513704960000000000000000)*u^9+(18926408459065473795151327/925888320000000000000000)*u^10+(23857573539370765302571/2645395200000000000000)*u^11+(-6859355296772558831/3306744000000000000)*u^12+(-12209498883530569/26453952000000000)*u^13+(1571303220371/16533720000000)*u^14+(164737204301/11573604000000)*u^15+(-23155759/14467005000)*u^16+(-247609/1157360400)*u^17)/((u-(1))^4*(u-(2/3))^4*(u-(-1327/200))^2*(u-(-1727/600))^4*((21*u^2-24*u+4))*(F1BFullFTC.quadOne u))
def partialValue (u : ℝ) : ℝ := (FirstCRationalPayment.poleKernel (1) c1_1 c1_2 c1_3 u+c1_4/(u-(1))^4)+(FirstCRationalPayment.poleKernel (2/3) c3_1 c3_2 c3_3 u+c3_4/(u-(2/3))^4)+(FirstCRationalPayment.poleKernel (-1327/200) c4_1 c4_2 c4_3 u+c4_4/(u-(-1327/200))^4)+(FirstCRationalPayment.poleKernel (-1727/600) c5_1 c5_2 c5_3 u+c5_4/(u-(-1727/600))^4)+(f1*u+g1)/((21*u^2-24*u+4))+(f2*u+g2)/(F1BFullFTC.quadOne u)
def primitive (u : ℝ) : ℝ := F1FreshFTC.pole4 (1) c1_1 c1_2 c1_3 c1_4 u+F1FreshFTC.pole4 (2/3) c3_1 c3_2 c3_3 c3_4 u+F1FreshFTC.pole4 (-1327/200) c4_1 c4_2 c4_3 c4_4 u+F1FreshFTC.pole4 (-1727/600) c5_1 c5_2 c5_3 c5_4 u+F1ActualSecondFTC.affinePrimitive f1 g1 u+F1BFullFTC.quadPrimitiveOne f2 g2 u

theorem source_exact {u : ℝ} (hu : 2 ≤ u) :
    ActualTailVariation.floor (2*(u-1)/u)*F1JointFTC.low (((1127/200)+u+1)/(2*(u+1)))/u=kernel u := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hfour : 0 < 16-u*96+u^2*216-u^3*216+u^4*81 := by
    have he : 16-u*96+u^2*216-u^3*216+u^4*81=(3*u-2)^4 := by ring
    rw [he]
    exact pow_pos ht 4
  have hsix : 0 < 64-u*768+u^2*3504-u^3*8064+u^4*10044-u^5*6480+u^6*1701 := by
    have he : 64-u*768+u^2*3504-u^3*8064+u^4*10044-u^5*6480+u^6*1701=
        (3*u-2)^4*(21*u^2-24*u+4) := by ring
    rw [he]
    exact mul_pos (pow_pos ht 4) hq
  rw [low_rational (show 0 < (((1127/200)+u+1)/(2*(u+1))) by positivity)]
  unfold ActualTailVariation.floor ActualTailVariation.denominator lowNumerator kernel
    F1BFullFTC.quadOne
  simp only [neg_div, sub_neg_eq_add]
  field_simp (disch := first | positivity | nlinarith only [hq,hfour,hsix])
  ring

theorem partial_exact {u : ℝ} (hu : 2 ≤ u) : kernel u=partialValue u := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hfour : 0 < 16-u*96+u^2*216-u^3*216+u^4*81 := by
    have he : 16-u*96+u^2*216-u^3*216+u^4*81=(3*u-2)^4 := by ring
    rw [he]
    exact pow_pos ht 4
  have hsix : 0 < 64-u*768+u^2*3504-u^3*8064+u^4*10044-u^5*6480+u^6*1701 := by
    have he : 64-u*768+u^2*3504-u^3*8064+u^4*10044-u^5*6480+u^6*1701=
        (3*u-2)^4*(21*u^2-24*u+4) := by ring
    rw [he]
    exact mul_pos (pow_pos ht 4) hq
  unfold kernel partialValue FirstCRationalPayment.poleKernel
    F1BFullFTC.quadOne
  simp only [neg_div, sub_neg_eq_add]
  field_simp (disch := first | positivity | nlinarith only [hq,hfour,hsix])
  unfold c1_1 c1_2 c1_3 c1_4 c3_1 c3_2 c3_3 c3_4 c4_1 c4_2 c4_3 c4_4 c5_1 c5_2 c5_3 c5_4 g1 f1 g2 f2
  ring

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := F1FreshFTC.pole4_deriv (1) c1_1 c1_2 c1_3 c1_4 u (by linarith)
  have h1 := F1FreshFTC.pole4_deriv (2/3) c3_1 c3_2 c3_3 c3_4 u (by linarith)
  have h2 := F1FreshFTC.pole4_deriv (-1327/200) c4_1 c4_2 c4_3 c4_4 u (by linarith)
  have h3 := F1FreshFTC.pole4_deriv (-1727/600) c5_1 c5_2 c5_3 c5_4 u (by linarith)
  have h4 := F1ActualSecondFTC.affinePrimitive_deriv f1 g1 hu
  have h5 := F1BFullFTC.quadPrimitiveOne_deriv f2 g2 hu
  rw [partial_exact hu]
  exact (((((h0.add h1).add h2).add h3).add h4).add h5)

theorem kernel_continuousOn : ContinuousOn kernel (Icc 2 (927/200)) := by
  intro u hu
  have hu := hu.1
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hfour : 0 < 16-u*96+u^2*216-u^3*216+u^4*81 := by
    have he : 16-u*96+u^2*216-u^3*216+u^4*81=(3*u-2)^4 := by ring
    rw [he]
    exact pow_pos ht 4
  have hsix : 0 < 64-u*768+u^2*3504-u^3*8064+u^4*10044-u^5*6480+u^6*1701 := by
    have he : 64-u*768+u^2*3504-u^3*8064+u^4*10044-u^5*6480+u^6*1701=
        (3*u-2)^4*(21*u^2-24*u+4) := by ring
    rw [he]
    exact mul_pos (pow_pos ht 4) hq
  apply ContinuousAt.continuousWithinAt
  unfold kernel F1BFullFTC.quadOne
  simp only [neg_div, sub_neg_eq_add]
  fun_prop (disch := positivity)

def mass : ℝ := primitive (927/200)-primitive 2

theorem integral_exact : (∫ u in (2:ℝ)..(927/200),kernel u)=mass := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    apply primitive_deriv
    rw [uIcc_of_le (by norm_num : (2:ℝ)≤927/200)] at hu
    exact hu.1
  · exact kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num)
end TailFiniteFTC.AB21
