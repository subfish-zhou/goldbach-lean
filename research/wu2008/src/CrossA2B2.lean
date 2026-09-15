import CrossRational

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1FactorCross
open scoped Interval
namespace F1CrossFTC.A2B2

def c0_1 : ℝ := 1793335811814319707869207517/3598979351703684491802793061360
def c0_2 : ℝ := 0
def c0_3 : ℝ := 0
def c0_4 : ℝ := 0
def c1_1 : ℝ := 4041471056927119699230004241691532359791/120827074435704913584359068220372016833899200
def c1_2 : ℝ := -117369567236753010812094671/130631612629659155555313193646400
def c1_3 : ℝ := 0
def c1_4 : ℝ := 0
def c3_1 : ℝ := 307874842865655680299481838350858873601729244794452669117011240258337692/775382115570510054989892624651756337623678814201782155292094283484846060075
def c3_2 : ℝ := -58442252987063241957086147836758723973074305937707690030722/691439173171545399806109600803776443255036601154675712560643075
def c3_3 : ℝ := 68056228826485438609432131171655208461462744/3829713675710284851505670979342653754067106694075
def c3_4 : ℝ := 75115888157862597678092855528384/549832469285718070058249337862646169075
def c6_1 : ℝ := 26611463581630282648535978056865003693765497685536240383552444760570920628755359042002318/3888537004383628789822521055858184976096994905919406629939817760658160758545560802831034075
def c6_2 : ℝ := -405380978275873568360107420645540844545774032573706462084764910299049221/4495736934865905571583738895893379580989673852021104194500992429964251250
def c6_3 : ℝ := 330052513334669820742290250716009577608000654644676473463/254689842907986003030807201329968818342290346517457687500
def c6_4 : ℝ := -3354421302777865695711935081778773692011/7214269542489297677976356497480826562500
def g1 : ℝ := 59886034695565881682923504762109387056749427687775/3567572343649169112329513608842559783063225033635123
def f1 : ℝ := -136038573409698539572800302360025542001408504495425/7135144687298338224659027217685119566126450067270246
def g3 : ℝ := -24225080060916692448010397224356709950575389239167276979203999726648936071/73963554709468537754643158003695086869638813773876113609684007547577051064
def f3 : ℝ := -187434941619971417992832441676927501687480271163611182646195781959040975/9245444338683567219330394750461885858704851721734514201210500943447131383
def p0 : ℝ := 1063835237/11433310058268
def p1 : ℝ := -63425/136110834027

def kernel (u : ℝ) : ℝ := ((22139948294003947010730957/711272240000000000000)+(-55399080221496840779454051/254025800000000000000)*u+(4802842814963215403244539283/7112722400000000000000)*u^2+(-3734083442628608822890534273/3048309600000000000000)*u^3+(249261468398187555910689931/171467415000000000000)*u^4+(-235421221909774943951425131803/197530462080000000000000)*u^5+(913799993997076533868337999227/1316869747200000000000000)*u^6+(-8014782607904046244857075409097/27654264691200000000000000)*u^7+(8189653388219395389883692089761/94814621798400000000000000)*u^8+(-1859468454887752611406750033/103703492592000000000000)*u^9+(1449549721765495977661639/592591386240000000000)*u^10+(-69543174819159509899/370369616400000000)*u^11+(3674542771459811/1185182772480000)*u^12+(6013913314721/9259240410000)*u^13+(-103494993863/2592587314800)*u^14+(275804/925924041)*u^15+(-63425/6481468287)*u^16)/((u-(0))^1*(u-(1))^2*(u-(2/3))^4*(u-(-3581/200))^4*((21*u^2-24*u+4))^1*(F1BFullFTC.quadTwo u)^1)
def partialValue (u : ℝ) : ℝ := (poleKernel (0) c0_1 c0_2 c0_3 u+c0_4/(u-(0))^4)+(poleKernel (1) c1_1 c1_2 c1_3 u+c1_4/(u-(1))^4)+(poleKernel (2/3) c3_1 c3_2 c3_3 u+c3_4/(u-(2/3))^4)+(poleKernel (-3581/200) c6_1 c6_2 c6_3 u+c6_4/(u-(-3581/200))^4)+(f1*u+g1)/((21*u^2-24*u+4))+(f3*u+g3)/(F1BFullFTC.quadTwo u)+p0+p1*u
def primitive (u : ℝ) : ℝ := F1FreshFTC.pole4 (0) c0_1 c0_2 c0_3 c0_4 u+F1FreshFTC.pole4 (1) c1_1 c1_2 c1_3 c1_4 u+F1FreshFTC.pole4 (2/3) c3_1 c3_2 c3_3 c3_4 u+F1FreshFTC.pole4 (-3581/200) c6_1 c6_2 c6_3 c6_4 u+F1ActualSecondFTC.affinePrimitive f1 g1 u+F1BFullFTC.quadPrimitiveTwo f3 g3 u+p0*u+(p1/2)*u^2

theorem source_exact {u : ℝ} (hu : 2 ≤ u) : kA2 u*kB2 u/u=kernel u := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  dsimp only [kA2,kB2,kernel,F1BFullFTC.quadTwo]
  have hv : 0 ≤ u-2 := by linarith
  generalize he : u-2=v at hv
  have heq : u=v+2 := by linarith
  rw [heq]
  ring_nf
  field_simp (disch := positivity)
  ring

theorem partial_exact {u : ℝ} (hu : 2 ≤ u) : kernel u=partialValue u := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  dsimp only [kernel,partialValue,poleKernel,F1BFullFTC.quadTwo]
  have hv : 0 ≤ u-2 := by linarith
  generalize he : u-2=v at hv
  have heq : u=v+2 := by linarith
  rw [heq]
  field_simp (disch := positivity)
  unfold c0_1 c0_2 c0_3 c0_4 c1_1 c1_2 c1_3 c1_4 c3_1 c3_2 c3_3 c3_4 c6_1 c6_2 c6_3 c6_4 g1 f1 g3 f3 p0 p1
  ring_nf
  all_goals (field_simp; ring)

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := F1FreshFTC.pole4_deriv (0) c0_1 c0_2 c0_3 c0_4 u (by linarith)
  have h1 := F1FreshFTC.pole4_deriv (1) c1_1 c1_2 c1_3 c1_4 u (by linarith)
  have h2 := F1FreshFTC.pole4_deriv (2/3) c3_1 c3_2 c3_3 c3_4 u (by linarith)
  have h3 := F1FreshFTC.pole4_deriv (-3581/200) c6_1 c6_2 c6_3 c6_4 u (by linarith)
  have h4 := F1ActualSecondFTC.affinePrimitive_deriv f1 g1 hu
  have h5 := F1BFullFTC.quadPrimitiveTwo_deriv f3 g3 hu
  have h6 := ((hasDerivAt_id u).const_mul p0).add (((hasDerivAt_id u).pow 2).const_mul (p1/2))
  rw [partial_exact hu]
  convert ((((((h0.add h1).add h2).add h3).add h4).add h5).add h6) using 1 <;> first | rfl | (funext x; dsimp [primitive]; ring) | (dsimp [partialValue]; ring)

theorem kernel_continuousOn : ContinuousOn kernel (Icc 2 (927/200)) := by
  intro u hu
  have hu := hu.1
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hp0 : 0 < u-(0) := by linarith
  have hp1 : 0 < u-(1) := by linarith
  have hp3 : 0 < u-(2/3) := by linarith
  have hp6 : 0 < u-(-3581/200) := by linarith
  apply ContinuousAt.continuousWithinAt
  unfold kernel F1BFullFTC.quadTwo
  fun_prop (disch := positivity)

def mass : ℝ := primitive (927/200)-primitive 2

theorem integral_exact : (∫ u in (2:ℝ)..(927/200), kernel u)=mass := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    apply primitive_deriv
    rw [uIcc_of_le (by norm_num : (2:ℝ)≤927/200)] at hu
    exact hu.1
  · exact kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num)

end F1CrossFTC.A2B2
