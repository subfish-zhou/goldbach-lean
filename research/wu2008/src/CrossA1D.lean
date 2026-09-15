import CrossRational

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1FactorCross
open scoped Interval
namespace F1CrossFTC.A1D

def c0_1 : ℝ := -426049960279735627257341443206125804441301285/147976960156537422839660954949423393884793067
def c0_2 : ℝ := 7789867551921810755734825996899648/18031278449517600849173751088050583
def c0_3 : ℝ := -12923472562066367428788/313878015855694471296181
def c0_4 : ℝ := 0
def c2_1 : ℝ := -2556033210664224212569894091322172024497397340255271520/1032535974835402370538983448395962210018173225201447
def c2_2 : ℝ := 662473955347395808474036318471078362855618784/664432968368999595986052892093581142930803
def c2_3 : ℝ := -106699699308881471942124322879613824/427560085280336497843653520374447
def c2_4 : ℝ := -6126386182212427380153344/275133286919327800507803
def c4_1 : ℝ := -350463472856288212167059094166/12038264683564313069307948339
def c4_2 : ℝ := 0
def c4_3 : ℝ := 0
def c4_4 : ℝ := 0
def c5_1 : ℝ := 357896767715126756610513726847161684571537353546365185703768/143673159674688387675960625728738787031710994133986821779
def c5_2 : ℝ := 1107705210746432238361934136262413216347101280518/973911042726523997356435917814447789920268575
def c5_3 : ℝ := 2917916510593024690324334565417847067/6601808725389699035269321763206875
def c5_4 : ℝ := 0
def c6_1 : ℝ := -3576664226750464077940915173705711605964667407602327674317528/2161061403000344231447226946715600840139719005930575719261
def c6_2 : ℝ := -2113312974958489810630134924640547225581348290258/622273479063307320083519926957416690020426705
def c6_3 : ℝ := -40011406775525402041708332964413373923/4479561318895697909492197746138125
def c6_4 : ℝ := 0
def g0 : ℝ := 1383166772540009576357991343336741715696600667010000/2796921062598965381944392431852827554755810649429
def f0 : ℝ := 4671119826173029161541869156993339392016518330075000/2796921062598965381944392431852827554755810649429
def p0 : ℝ := 0
def p1 : ℝ := 0

def kernel (u : ℝ) : ℝ := ((-119661782982095994711/50000000000000)+(1311780328905807029441/175000000000000)*u+(-24420264184930299662137/900000000000000)*u^2+(197478822698672716248907/4860000000000000)*u^3+(-24307298490206547180203/1215000000000000)*u^4+(-556012754254311525373973/97200000000000000)*u^5+(368728236384229334645123/43200000000000000)*u^6+(-693512896521145449100003/388800000000000000)*u^7+(-2852246832880807791592889/4354560000000000000)*u^8+(4016012466760733439059/15552000000000000)*u^9+(1507657018830379577/77760000000000)*u^10+(-6670825900606033/388800000000)*u^11+(907150635013/648000000)*u^12+(1528980121/9720000)*u^13+(-474317/48600)*u^14+(-2365/1701)*u^15)/((u-(0))^3*(u-(-2))^4*(u-(-1327/200))^1*(u-(-1727/600))^3*(u-(-3581/200))^3*((u^2+16*u+4))^1)
def partialValue (u : ℝ) : ℝ := (poleKernel (0) c0_1 c0_2 c0_3 u+c0_4/(u-(0))^4)+(poleKernel (-2) c2_1 c2_2 c2_3 u+c2_4/(u-(-2))^4)+(poleKernel (-1327/200) c4_1 c4_2 c4_3 u+c4_4/(u-(-1327/200))^4)+(poleKernel (-1727/600) c5_1 c5_2 c5_3 u+c5_4/(u-(-1727/600))^4)+(poleKernel (-3581/200) c6_1 c6_2 c6_3 u+c6_4/(u-(-3581/200))^4)+(f0*u+g0)/((u^2+16*u+4))+p0+p1*u
def primitive (u : ℝ) : ℝ := F1FreshFTC.pole4 (0) c0_1 c0_2 c0_3 c0_4 u+F1FreshFTC.pole4 (-2) c2_1 c2_2 c2_3 c2_4 u+F1FreshFTC.pole4 (-1327/200) c4_1 c4_2 c4_3 c4_4 u+F1FreshFTC.pole4 (-1727/600) c5_1 c5_2 c5_3 c5_4 u+F1FreshFTC.pole4 (-3581/200) c6_1 c6_2 c6_3 c6_4 u+F1JointFTC.quadraticPrimitive f0 g0 u+p0*u+(p1/2)*u^2

theorem source_exact {u : ℝ} (hu : 2 ≤ u) : kA1 u*bDiff u/u=kernel u := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  dsimp only [kA1,bDiff,kernel]
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
  unfold c0_1 c0_2 c0_3 c0_4 c2_1 c2_2 c2_3 c2_4 c4_1 c4_2 c4_3 c4_4 c5_1 c5_2 c5_3 c5_4 c6_1 c6_2 c6_3 c6_4 g0 f0 p0 p1
  ring_nf
  all_goals (field_simp; ring)

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := F1FreshFTC.pole4_deriv (0) c0_1 c0_2 c0_3 c0_4 u (by linarith)
  have h1 := F1FreshFTC.pole4_deriv (-2) c2_1 c2_2 c2_3 c2_4 u (by linarith)
  have h2 := F1FreshFTC.pole4_deriv (-1327/200) c4_1 c4_2 c4_3 c4_4 u (by linarith)
  have h3 := F1FreshFTC.pole4_deriv (-1727/600) c5_1 c5_2 c5_3 c5_4 u (by linarith)
  have h4 := F1FreshFTC.pole4_deriv (-3581/200) c6_1 c6_2 c6_3 c6_4 u (by linarith)
  have h5 := F1JointFTC.quadraticPrimitive_deriv f0 g0 hu
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
  have hp2 : 0 < u-(-2) := by linarith
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

end F1CrossFTC.A1D
