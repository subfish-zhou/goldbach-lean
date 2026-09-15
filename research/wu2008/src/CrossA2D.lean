import CrossRational

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1FactorCross
open scoped Interval
namespace F1CrossFTC.A2D

def c0_1 : ℝ := 694636650211067249297355/2197146110989861299073267
def c0_2 : ℝ := 0
def c0_3 : ℝ := 0
def c0_4 : ℝ := 0
def c1_1 : ℝ := 29695661779240152866027485223257331/1173733777393507922627420230389194196
def c1_2 : ℝ := -8556137129530242054671/12480427594438380641553372
def c1_3 : ℝ := 0
def c1_4 : ℝ := 0
def c3_1 : ℝ := 7135219317885074631897153736479273836101432073521770157360899136/26991145879941585233836531515526043102780246637507444779043498783
def c3_2 : ℝ := -14520641846248139697173120552021900024726649583966816/259943192749498771117585300984098483789456297095877363
def c3_3 : ℝ := 92959540547214322357314665510615715231616/7510292125872794676247831996801002127160229
def c3_4 : ℝ := 61831992162799218995667426304/650963241845335787728892553942921
def c4_1 : ℝ := 3057817978526567770953712352431/212542318675726636140790413124230
def c4_2 : ℝ := 0
def c4_3 : ℝ := 0
def c4_4 : ℝ := 0
def c5_1 : ℝ := -148208493501831902732025655652770950742003070349133581067234311454/6401996208124907517824893523938075547475582065018749415147185161315
def c5_2 : ℝ := -323597913753365334289203518782515922367242374957391/26525483504984210111206179818054080638922840271256750
def c5_3 : ℝ := -26294285286058475953705228717811208457/769323936799843785496289431195358512500
def c5_4 : ℝ := 0
def c6_1 : ℝ := -981805842385278971909057069472536670256067244771283375854234228265806/125880634176245356004344689085014628267710867856590917446027788038999035
def c6_2 : ℝ := 12925722703797788118325053708445785922029502568944671/203751874326388802424645761063975054673832277213966150
def c6_3 : ℝ := -62504744772258367000843510840598267553/57714156339914381423810851979846612500
def c6_4 : ℝ := 0
def g1 : ℝ := 2175583863823568493636315733256148203453658710000/200916422249080497269318206920050414940493231761
def f1 : ℝ := -832114646110697264696585218764971393513344295000/66972140749693499089772735640016804980164410587
def p0 : ℝ := 0
def p1 : ℝ := 0

def kernel (u : ℝ) : ℝ := ((1715152222743375924191/7560000000000000)+(-76804334166357936576073/56700000000000000)*u+(989887171122504416131949/291600000000000000)*u^2+(-36409110985442411021203417/7873200000000000000)*u^3+(143776365680261159364253/39366000000000000)*u^4+(-9925124146918685452750027/6298560000000000000)*u^5+(9275114645128843267488203/41990400000000000000)*u^6+(89175829346270773674116207/881798400000000000000)*u^7+(-299719998813450748326109219/7054387200000000000000)*u^8+(-47103085684578479549279/25194240000000000000)*u^9+(506029220544859173283/125971200000000000)*u^10+(-496601662760641067/629856000000000)*u^11+(281877424247/12960000000)*u^12+(106898511299/15746400000)*u^13+(-67377721/551124000)*u^14+(-27907/551124)*u^15)/((u-(0))^1*(u-(1))^2*(u-(2/3))^4*(u-(-1327/200))^1*(u-(-1727/600))^3*(u-(-3581/200))^3*((21*u^2-24*u+4))^1)
def partialValue (u : ℝ) : ℝ := (poleKernel (0) c0_1 c0_2 c0_3 u+c0_4/(u-(0))^4)+(poleKernel (1) c1_1 c1_2 c1_3 u+c1_4/(u-(1))^4)+(poleKernel (2/3) c3_1 c3_2 c3_3 u+c3_4/(u-(2/3))^4)+(poleKernel (-1327/200) c4_1 c4_2 c4_3 u+c4_4/(u-(-1327/200))^4)+(poleKernel (-1727/600) c5_1 c5_2 c5_3 u+c5_4/(u-(-1727/600))^4)+(poleKernel (-3581/200) c6_1 c6_2 c6_3 u+c6_4/(u-(-3581/200))^4)+(f1*u+g1)/((21*u^2-24*u+4))+p0+p1*u
def primitive (u : ℝ) : ℝ := F1FreshFTC.pole4 (0) c0_1 c0_2 c0_3 c0_4 u+F1FreshFTC.pole4 (1) c1_1 c1_2 c1_3 c1_4 u+F1FreshFTC.pole4 (2/3) c3_1 c3_2 c3_3 c3_4 u+F1FreshFTC.pole4 (-1327/200) c4_1 c4_2 c4_3 c4_4 u+F1FreshFTC.pole4 (-1727/600) c5_1 c5_2 c5_3 c5_4 u+F1FreshFTC.pole4 (-3581/200) c6_1 c6_2 c6_3 c6_4 u+F1ActualSecondFTC.affinePrimitive f1 g1 u+p0*u+(p1/2)*u^2

theorem source_exact {u : ℝ} (hu : 2 ≤ u) : kA2 u*bDiff u/u=kernel u := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  dsimp only [kA2,bDiff,kernel]
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
  dsimp only [kernel,partialValue,poleKernel]
  have hv : 0 ≤ u-2 := by linarith
  generalize he : u-2=v at hv
  have heq : u=v+2 := by linarith
  rw [heq]
  field_simp (disch := positivity)
  unfold c0_1 c0_2 c0_3 c0_4 c1_1 c1_2 c1_3 c1_4 c3_1 c3_2 c3_3 c3_4 c4_1 c4_2 c4_3 c4_4 c5_1 c5_2 c5_3 c5_4 c6_1 c6_2 c6_3 c6_4 g1 f1 p0 p1
  ring_nf
  all_goals (field_simp; ring)

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := F1FreshFTC.pole4_deriv (0) c0_1 c0_2 c0_3 c0_4 u (by linarith)
  have h1 := F1FreshFTC.pole4_deriv (1) c1_1 c1_2 c1_3 c1_4 u (by linarith)
  have h2 := F1FreshFTC.pole4_deriv (2/3) c3_1 c3_2 c3_3 c3_4 u (by linarith)
  have h3 := F1FreshFTC.pole4_deriv (-1327/200) c4_1 c4_2 c4_3 c4_4 u (by linarith)
  have h4 := F1FreshFTC.pole4_deriv (-1727/600) c5_1 c5_2 c5_3 c5_4 u (by linarith)
  have h5 := F1FreshFTC.pole4_deriv (-3581/200) c6_1 c6_2 c6_3 c6_4 u (by linarith)
  have h6 := F1ActualSecondFTC.affinePrimitive_deriv f1 g1 hu
  have h7 := ((hasDerivAt_id u).const_mul p0).add (((hasDerivAt_id u).pow 2).const_mul (p1/2))
  rw [partial_exact hu]
  convert (((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7) using 1 <;> first | rfl | (funext x; dsimp [primitive]; ring) | (dsimp [partialValue]; ring)

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
  have hp4 : 0 < u-(-1327/200) := by linarith
  have hp5 : 0 < u-(-1727/600) := by linarith
  have hp6 : 0 < u-(-3581/200) := by linarith
  apply ContinuousAt.continuousWithinAt
  unfold kernel 
  fun_prop (disch := positivity)

def mass : ℝ := primitive (927/200)-primitive 2

theorem integral_exact : (∫ u in (2:ℝ)..(927/200), kernel u)=mass := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    apply primitive_deriv
    rw [uIcc_of_le (by norm_num : (2:ℝ)≤927/200)] at hu
    exact hu.1
  · exact kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num)

end F1CrossFTC.A2D
