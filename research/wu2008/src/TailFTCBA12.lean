import TailRationalBasis

noncomputable section
open Real Set MeasureTheory TailRationalBasis
open scoped Interval
namespace TailFiniteFTC.BA12

def c0_1 : ℝ := -684045470639655664252105951734098754247111540471216869/388495768507953889169937369691107880997143649433086315419280
def c0_2 : ℝ := 224770021557603764347067663242516280274504/1101807645521395456378205537083676539392536175725
def c0_3 : ℝ := -106693315103171395599636806361/5713960056250061349861237185290144300
def c0_4 : ℝ := 0
def c2_1 : ℝ := 796915105974073814364848525608014157027847092330257151566341584/402845629223139349870293688751614834625158511894969237905947823286805
def c2_2 : ℝ := 1454481295850194503210090287237809072297584132137830016/642834243475891087760619333919154536381880239603386022190175
def c2_3 : ℝ := -1264962312009277345934619373072885281296224/991103479720523502767156818329406380252709217175
def c2_4 : ℝ := -19585878724348024106701510603968/4584165128802615912761911361986372525
def c6_1 : ℝ := 201515768417608503059637827560913647058874106287792974139309602670703687936/337726730304411954000927423801570057389223812336773582103404494296252229
def c6_2 : ℝ := 841383746131940973201642441497104143680777326664464906447206944/486238815675077452075626063011010189031436776334379536833725
def c6_3 : ℝ := 32291199126308303018144532210226765096956659801392/700057663946220735093959917827093776272980043125
def c6_4 : ℝ := 6090692411354907743363588747336105090396/335967098917177343211914830960359375
def g0 : ℝ := -1335233353544330620653134419079507392165558819253835567425/8376811770873104252590726156799616069533966130468125997
def f0 : ℝ := -10512272261151364216221215053925519986518299835530581790875/16753623541746208505181452313599232139067932260936251994
def g3 : ℝ := 539692827896704161696559377011366558853844339974409955192032687749658100/50209786291255238973135002641949628320129022305351417048351064784899
def f3 : ℝ := 66905420903223036160124511109808080914549809562532949802253419083510000/50209786291255238973135002641949628320129022305351417048351064784899
def p0 : ℝ := -9270599966592950/711433405398681
def p1 : ℝ := 85834214635000/711433405398681
def p2 : ℝ := -657490000000/711433405398681
def p3 : ℝ := 3100000000/711433405398681

def kernel (u : ℝ) : ℝ := ((-106693315103171395599636806361/1129259373648700000000000000)+(1705597323543979387888793990571/3952407807770450000000000000)*u+(-54942995007847400246718640355601/15809631231081800000000000000)*u^2+(-7434166832370711030668482268163/3161926246216360000000000000)*u^3+(3320656359138806520648744819603/1580963123108180000000000000)*u^4+(20003213701321570181394904257/8016038144800000000000000)*u^5+(-53383989539540647664424331241121/36136299956758400000000000000)*u^6+(-15630118253557888468281569984611/36136299956758400000000000000)*u^7+(10446409657273586519280957054167/29140312285129973760000000000)*u^8+(793501836891696141016444079/607089839273541120000000000)*u^9+(-14543443614446873775670209/404726559515694080000000)*u^10+(55730364579828986148383/11382934486378896000000)*u^11+(13934344783785753323/10840889987027520000)*u^12+(-3691370799445657/11615239271815200)*u^13+(-7540031526623/813066749027064)*u^14+(5179598141500/711433405398681)*u^15+(-9586547500/30931887191247)*u^16+(-40435000000/711433405398681)*u^17+(3100000000/711433405398681)*u^18)/((u-(0))^3*(u-(-2))^4*(u-(-3581/200))^4*((u^2+16*u+4))*(F1BFullFTC.quadTwo u))
def partialValue (u : ℝ) : ℝ := (FirstCRationalPayment.poleKernel (0) c0_1 c0_2 c0_3 u+c0_4/(u-(0))^4)+(FirstCRationalPayment.poleKernel (-2) c2_1 c2_2 c2_3 u+c2_4/(u-(-2))^4)+(FirstCRationalPayment.poleKernel (-3581/200) c6_1 c6_2 c6_3 u+c6_4/(u-(-3581/200))^4)+(f0*u+g0)/((u^2+16*u+4))+(f3*u+g3)/(F1BFullFTC.quadTwo u)+p0+p1*u^1+p2*u^2+p3*u^3
def primitive (u : ℝ) : ℝ := F1FreshFTC.pole4 (0) c0_1 c0_2 c0_3 c0_4 u+F1FreshFTC.pole4 (-2) c2_1 c2_2 c2_3 c2_4 u+F1FreshFTC.pole4 (-3581/200) c6_1 c6_2 c6_3 c6_4 u+F1JointFTC.quadraticPrimitive f0 g0 u+F1BFullFTC.quadPrimitiveTwo f3 g3 u+(p0/1)*u^1+(p1/2)*u^2+(p2/3)*u^3+(p3/4)*u^4

theorem source_exact {u : ℝ} (hu : 2 ≤ u) :
    ActualTailVariation.floor ((2*(1127/200))/((1127/200)+u+1))*F1JointFTC.low (u/2)/u=kernel u := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  rw [low_rational (show 0 < (u/2) by positivity)]
  unfold ActualTailVariation.floor ActualTailVariation.denominator lowNumerator kernel
    F1BFullFTC.quadTwo
  simp only [neg_div, sub_neg_eq_add, sub_zero]
  field_simp (disch := positivity)
  ring

theorem partial_exact {u : ℝ} (hu : 2 ≤ u) : kernel u=partialValue u := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  unfold kernel partialValue FirstCRationalPayment.poleKernel
    F1BFullFTC.quadTwo
  simp only [neg_div, sub_neg_eq_add, sub_zero]
  field_simp (disch := positivity)
  unfold c0_1 c0_2 c0_3 c0_4 c2_1 c2_2 c2_3 c2_4 c6_1 c6_2 c6_3 c6_4 g0 f0 g3 f3 p0 p1 p2 p3
  ring

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := F1FreshFTC.pole4_deriv (0) c0_1 c0_2 c0_3 c0_4 u (by linarith)
  have h1 := F1FreshFTC.pole4_deriv (-2) c2_1 c2_2 c2_3 c2_4 u (by linarith)
  have h2 := F1FreshFTC.pole4_deriv (-3581/200) c6_1 c6_2 c6_3 c6_4 u (by linarith)
  have h3 := F1JointFTC.quadraticPrimitive_deriv f0 g0 hu
  have h4 := F1BFullFTC.quadPrimitiveTwo_deriv f3 g3 hu
  have h5 := ((hasDerivAt_id u).pow 1).const_mul (p0/1)
  have h6 := ((hasDerivAt_id u).pow 2).const_mul (p1/2)
  have h7 := ((hasDerivAt_id u).pow 3).const_mul (p2/3)
  have h8 := ((hasDerivAt_id u).pow 4).const_mul (p3/4)
  rw [partial_exact hu]
  convert ((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8) using 1 <;> first
    | rfl
    | (dsimp [partialValue]; ring)

theorem kernel_continuousOn : ContinuousOn kernel (Icc 2 (927/200)) := by
  intro u hu
  have hu := hu.1
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  apply ContinuousAt.continuousWithinAt
  unfold kernel F1BFullFTC.quadTwo
  simp only [neg_div, sub_neg_eq_add, sub_zero]
  fun_prop (disch := positivity)

def mass : ℝ := primitive (927/200)-primitive 2

theorem integral_exact : (∫ u in (2:ℝ)..(927/200),kernel u)=mass := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    apply primitive_deriv
    rw [uIcc_of_le (by norm_num : (2:ℝ)≤927/200)] at hu
    exact hu.1
  · exact kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num)
end TailFiniteFTC.BA12
