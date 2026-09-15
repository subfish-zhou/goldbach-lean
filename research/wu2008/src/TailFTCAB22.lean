import TailRationalBasis

noncomputable section
open Real Set MeasureTheory TailRationalBasis
open scoped Interval
namespace TailFiniteFTC.AB22

def c1_1 : ℝ := -15692254616696993239731945313458593276316296123960974781106371811637/2109600034781630256350917440792934074398575698755720249853994987200
def c1_2 : ℝ := 2100616559363319618536030890373202434591221827382649603/5321829263954325212356192478167824143947860269219265600
def c1_3 : ℝ := -232365498311184355387337912905369338589227/13425230492856101509373229802263557425988800
def c1_4 : ℝ := 423900916626256011425094885391/914421288407614088887192355524800
def c3_1 : ℝ := -363203276468126380589329875608256816221851572087464382292991796489839407984/775382115570510054989892624651756337623678814201782155292094283484846060075
def c3_2 : ℝ := -7813873312885602382153216736311315155860878115402681818972448/98777024738792199972301371543396634750719514450667958937234725
def c3_3 : ℝ := -6909347979671153549331204403170967850030725938944/616583901789355861092413027674167254404804177746075
def c3_4 : ℝ := -709466785730479356940254335139213056/549832469285718070058249337862646169075
def c6_1 : ℝ := -143079251455626755238982495777850066051455788868828993979447944904330371729536/338051063733470274490327913991458387192069358957852094921638400274646256787060377075
def c6_2 : ℝ := -7686678203492274629642713155492225503447596336260590577311641884/699795727879924560406199319322755245969221319259682575328926122888125
def c6_3 : ℝ := 6302948458407947668317501805861480123093956735892896/70983326341815165223495672316222895462451253682383171875
def c6_4 : ℝ := -5621878839797877719509577940906147439143/28800590902796660854995965208065483045312500
def g1 : ℝ := -119969070097269560319977398334840025747282376162583600/3567572343649169112329513608842559783063225033635123
def f1 : ℝ := 592378493142956480535844983008990719959237803773674025/3567572343649169112329513608842559783063225033635123
def g3 : ℝ := -135616747278402956115494955034462301656982397404972825314836627674942281757049/978572073807327937355263477685022738736751834059323658125473153318314963056451592
def f3 : ℝ := -1000626396914530057842277566184230564733295065288285798837417819013932911025/122321509225915992169407934710627842342093979257415457265684144164789370382056449
def p0 : ℝ := 422101/11433310058268
def p1 : ℝ := -25/136110834027

def kernel (u : ℝ) : ℝ := ((15132391265909575729959106333/96021752400000000000000)*u+(-133693123444211854924371225797/216048942900000000000000)*u^2+(909237145996682096458030079779/864195771600000000000000)*u^3+(-371819689937947570302424376591/370369616400000000000000)*u^4+(342703499435147864830837415951/592591386240000000000000)*u^5+(-292296220272828757269466894991/1481478465600000000000000)*u^6+(65595742289604003898649057797/1975304620800000000000000)*u^7+(1488502291208034338574092201/4609044115200000000000000)*u^8+(-645689601104385311825457639409/663702352588800000000000000)*u^9+(7004109974740985401908271/103703492592000000000000)*u^10+(7558364732982614096927/592591386240000000000)*u^11+(-224956971578259167/370369616400000000)*u^12+(-233131938895427/1975304620800000)*u^13+(-14197958309/3086413470000)*u^14+(-47807573/864195771600)*u^15+(844/6481468287)*u^16+(-25/6481468287)*u^17)/((u-(1))^4*(u-(2/3))^4*(u-(-3581/200))^4*((21*u^2-24*u+4))*(F1BFullFTC.quadTwo u))
def partialValue (u : ℝ) : ℝ := (FirstCRationalPayment.poleKernel (1) c1_1 c1_2 c1_3 u+c1_4/(u-(1))^4)+(FirstCRationalPayment.poleKernel (2/3) c3_1 c3_2 c3_3 u+c3_4/(u-(2/3))^4)+(FirstCRationalPayment.poleKernel (-3581/200) c6_1 c6_2 c6_3 u+c6_4/(u-(-3581/200))^4)+(f1*u+g1)/((21*u^2-24*u+4))+(f3*u+g3)/(F1BFullFTC.quadTwo u)+p0+p1*u^1
def primitive (u : ℝ) : ℝ := F1FreshFTC.pole4 (1) c1_1 c1_2 c1_3 c1_4 u+F1FreshFTC.pole4 (2/3) c3_1 c3_2 c3_3 c3_4 u+F1FreshFTC.pole4 (-3581/200) c6_1 c6_2 c6_3 c6_4 u+F1ActualSecondFTC.affinePrimitive f1 g1 u+F1BFullFTC.quadPrimitiveTwo f3 g3 u+(p0/1)*u^1+(p1/2)*u^2

theorem source_exact {u : ℝ} (hu : 2 ≤ u) :
    ActualTailVariation.floor (2*(u-1)/u)*F1JointFTC.low ((2*(1127/200))/((1127/200)+u+1))/u=kernel u := by
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
  rw [low_rational (show 0 < ((2*(1127/200))/((1127/200)+u+1)) by positivity)]
  unfold ActualTailVariation.floor ActualTailVariation.denominator lowNumerator kernel
    F1BFullFTC.quadTwo
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
    F1BFullFTC.quadTwo
  simp only [neg_div, sub_neg_eq_add]
  field_simp (disch := first | positivity | nlinarith only [hq,hfour,hsix])
  unfold c1_1 c1_2 c1_3 c1_4 c3_1 c3_2 c3_3 c3_4 c6_1 c6_2 c6_3 c6_4 g1 f1 g3 f3 p0 p1
  ring

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := F1FreshFTC.pole4_deriv (1) c1_1 c1_2 c1_3 c1_4 u (by linarith)
  have h1 := F1FreshFTC.pole4_deriv (2/3) c3_1 c3_2 c3_3 c3_4 u (by linarith)
  have h2 := F1FreshFTC.pole4_deriv (-3581/200) c6_1 c6_2 c6_3 c6_4 u (by linarith)
  have h3 := F1ActualSecondFTC.affinePrimitive_deriv f1 g1 hu
  have h4 := F1BFullFTC.quadPrimitiveTwo_deriv f3 g3 hu
  have h5 := ((hasDerivAt_id u).pow 1).const_mul (p0/1)
  have h6 := ((hasDerivAt_id u).pow 2).const_mul (p1/2)
  rw [partial_exact hu]
  convert ((((((h0.add h1).add h2).add h3).add h4).add h5).add h6) using 1 <;> first
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
end TailFiniteFTC.AB22
