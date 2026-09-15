import TailRationalBasis

noncomputable section
open Real Set MeasureTheory TailRationalBasis
open scoped Interval
namespace TailFiniteFTC.BA22

def c0_1 : ℝ := 3307492768198313263588740997191/6399635263000068711844585647524961616
def c0_2 : ℝ := 0
def c0_3 : ℝ := 0
def c0_4 : ℝ := 0
def c1_1 : ℝ := 2122895373533105874622093444500520376844043/358087266193877374433972930905903408528188299659200
def c1_2 : ℝ := -20216727232009474787276594761/129048110735986052789355637703373188800
def c1_3 : ℝ := 0
def c1_4 : ℝ := 0
def c3_1 : ℝ := -43933419939731771173187161118885272018414086312623078580931849051359943216/2697592373793467436302530945902068234653322154869896005586805324863670200457868675
def c3_2 : ℝ := 141122134318037262147566025836386192051579606320314911639232/6147518619068412509772339268115098390665534682315909756832559197446725
def c3_3 : ℝ := 16245763420330942752598846785558200768252732657504/49337888959536204541087064384886029982204930105016003101525
def c3_4 : ℝ := 1268824756049886867191291582850931264/43996564356028187816115892914759129713106822525
def c6_1 : ℝ := -121734825997653159830673839026983864546313134743794983076204151093282143270436178711390206144/34996833039452659108402689502723664784872954153274659669458359845923446826910047225479306675
def c6_2 : ℝ := 719079004216127204560853340705416922568787760514851487268803917469400436472/20230816206896575072126825031520208114453532334094968875254465934839130625
def c6_3 : ℝ := -120393916124111671341977587209771596431244412173286113502116/573052146542968506819316202992429841270153279664279796875
def c6_4 : ℝ := 2961406034421745418633852314628479000686593/5410702156866973258482267373110619921875
def g1 : ℝ := 20568140005887978720321925511369905446041962134975223075/4662684128971512005422718001409673771528677966259577549952143
def f1 : ℝ := -45795104670113818208479833494468685334282010858189294525/9325368257943024010845436002819347543057355932519155099904286
def g3 : ℝ := 16273158974295120995027102386611102492533688061586806833224756571818488581635/9245444338683567219330394750461885858704851721734514201210500943447131383
def f3 : ℝ := 6052203447412136711567273999521927727126384933615846943346261254749310774700/27736333016050701657991184251385657576114555165203542603631502830341394149
def p0 : ℝ := -48716224931283576522281/22414365378685222488882
def p1 : ℝ := 10984263437869197650/533675366159171964021
def p2 : ℝ := -4165874988620000/25413112674246284001
def p3 : ℝ := 990377000000/1210148222583156381

def kernel (u : ℝ) : ℝ := ((40833244051831027945540012311/1264770498486544000000000000)+(-6184286147793865118010544249983/15809631231081800000000000000)*u+(18917623945880883261452282075091/9034074989189600000000000000)*u^2+(-414031864444044848440274019896883/63238524924327200000000000000)*u^3+(84167118615299237278985942007741/6323852492432720000000000000)*u^4+(-2732240074605924667430873224867/147495101864320000000000000)*u^5+(3362355592696098457712178970307171/185843828349043200000000000000)*u^6+(-1023057362574119952867920949120256541/81957128301928051200000000000000)*u^7+(35493748746548067833874776766968304073/5900913237738819686400000000000000)*u^8+(-4088168419968041990195556390596771/2107469013478149888000000000000)*u^9+(53758661479050068007445746671381/147522830943470492160000000000)*u^10+(-1191251020749924410762944631/92201769339669057600000000)*u^11+(-3213192601359695719478153/263433626684768736000000)*u^12+(2084537336547571904039/658584066711921840000)*u^13+(-4352383744325129333/15366961556611509600)*u^14+(-11067833722111/711433405398681)*u^15+(49286072693675/8232300833899023)*u^16+(-3418124930000/6402900648588129)*u^17+(990377000000/57626105837293161)*u^18)/((u-(0))^1*(u-(1))^2*(u-(2/3))^4*(u-(-3581/200))^4*((21*u^2-24*u+4))*(F1BFullFTC.quadTwo u))
def partialValue (u : ℝ) : ℝ := (FirstCRationalPayment.poleKernel (0) c0_1 c0_2 c0_3 u+c0_4/(u-(0))^4)+(FirstCRationalPayment.poleKernel (1) c1_1 c1_2 c1_3 u+c1_4/(u-(1))^4)+(FirstCRationalPayment.poleKernel (2/3) c3_1 c3_2 c3_3 u+c3_4/(u-(2/3))^4)+(FirstCRationalPayment.poleKernel (-3581/200) c6_1 c6_2 c6_3 u+c6_4/(u-(-3581/200))^4)+(f1*u+g1)/((21*u^2-24*u+4))+(f3*u+g3)/(F1BFullFTC.quadTwo u)+p0+p1*u^1+p2*u^2+p3*u^3
def primitive (u : ℝ) : ℝ := F1FreshFTC.pole4 (0) c0_1 c0_2 c0_3 c0_4 u+F1FreshFTC.pole4 (1) c1_1 c1_2 c1_3 c1_4 u+F1FreshFTC.pole4 (2/3) c3_1 c3_2 c3_3 c3_4 u+F1FreshFTC.pole4 (-3581/200) c6_1 c6_2 c6_3 c6_4 u+F1ActualSecondFTC.affinePrimitive f1 g1 u+F1BFullFTC.quadPrimitiveTwo f3 g3 u+(p0/1)*u^1+(p1/2)*u^2+(p2/3)*u^3+(p3/4)*u^4

theorem source_exact {u : ℝ} (hu : 2 ≤ u) :
    ActualTailVariation.floor ((2*(1127/200))/((1127/200)+u+1))*F1JointFTC.low (2*(u-1)/u)/u=kernel u := by
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
  rw [low_rational (show 0 < (2*(u-1)/u) by positivity)]
  unfold ActualTailVariation.floor ActualTailVariation.denominator lowNumerator kernel
    F1BFullFTC.quadTwo
  simp only [neg_div, sub_neg_eq_add, sub_zero]
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
    F1BFullFTC.quadTwo
  simp only [neg_div, sub_neg_eq_add, sub_zero]
  field_simp (disch := first | positivity | nlinarith only [hq,hfour,hsix])
  unfold c0_1 c0_2 c0_3 c0_4 c1_1 c1_2 c1_3 c1_4 c3_1 c3_2 c3_3 c3_4 c6_1 c6_2 c6_3 c6_4 g1 f1 g3 f3 p0 p1 p2 p3
  ring

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := F1FreshFTC.pole4_deriv (0) c0_1 c0_2 c0_3 c0_4 u (by linarith)
  have h1 := F1FreshFTC.pole4_deriv (1) c1_1 c1_2 c1_3 c1_4 u (by linarith)
  have h2 := F1FreshFTC.pole4_deriv (2/3) c3_1 c3_2 c3_3 c3_4 u (by linarith)
  have h3 := F1FreshFTC.pole4_deriv (-3581/200) c6_1 c6_2 c6_3 c6_4 u (by linarith)
  have h4 := F1ActualSecondFTC.affinePrimitive_deriv f1 g1 hu
  have h5 := F1BFullFTC.quadPrimitiveTwo_deriv f3 g3 hu
  have h6 := ((hasDerivAt_id u).pow 1).const_mul (p0/1)
  have h7 := ((hasDerivAt_id u).pow 2).const_mul (p1/2)
  have h8 := ((hasDerivAt_id u).pow 3).const_mul (p2/3)
  have h9 := ((hasDerivAt_id u).pow 4).const_mul (p3/4)
  rw [partial_exact hu]
  convert (((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9) using 1 <;> first
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
end TailFiniteFTC.BA22
