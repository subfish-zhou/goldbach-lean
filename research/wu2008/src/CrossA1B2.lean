import CrossRational

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1FactorCross
open scoped Interval
namespace F1CrossFTC.A1B2

def c0_1 : ℝ := -198777100715402583180694296272469382169475948281403/43695873018517229258933245553472789096579239412811760
def c0_2 : ℝ := 84645960699861902466864193695064994916/123925280201729279509427280567977913986075
def c0_3 : ℝ := -41705483995681853671376919/642674884232800802107641618100
def c0_4 : ℝ := 0
def c2_1 : ℝ := -82359502188821006829441935569303917451679534825581479907990282/625276159607108864893706848986237361697364988027715011973708403
def c2_2 : ℝ := 36960988433484461416153148383515151981595803299610922/216907408665652213648249002576843275553185173520637675
def c2_3 : ℝ := -125409777653293729511744965067049617339224/1003264945921096150177817862253660558694025
def c2_4 : ℝ := -128857825138032890931892958144/13921247198138437641775150035225
def c6_1 : ℝ := 290094641518579051948213795996493706611364962210004464461080784371632593976/187625961280228863333848568778650031882902117964874212279669163497917905
def c6_2 : ℝ := 854857166658133570695102608804958356188620313297366049594688882/270132675375043028930903368339450105017464875741321964907625
def c6_3 : ℝ := 3502281549360801127871921753713524050388828706505199/388920924414567075052199954348385431262766690625
def c6_4 : ℝ := -2147278830286529909571680535756851067201/559945164861962238686524718267265625
def g0 : ℝ := -369731731786333314817595376535945955444398896546575/942177838502242601520984556551749138364681982299
def f0 : ℝ := -8735131842369175620214818299325046409688843170237375/5653067031013455609125907339310494830188091893794
def g3 : ℝ := 9101162956518867484453499556076432726593716881487116584998302685482405/33473190860836825982090001761299752213419348203567611365567376523266
def f3 : ℝ := -167333956398246987179735506800056002907478873857561838261153557375500/16736595430418412991045000880649876106709674101783805682783688261633
def p0 : ℝ := 4835015/80018127
def p1 : ℝ := -21500/80018127

def kernel (u : ℝ) : ℝ := ((-41705483995681853671376919/127012900000000000000)+(608353653880672193542288509/444545150000000000000)*u+(-8833051355187388929255485559/1778180600000000000000)*u^2+(511164028740931808888403873/50805160000000000000)*u^3+(-137052159307096266256852119/12701290000000000000)*u^4+(18153598726189187095643405243/3048309600000000000000)*u^5+(-3815161627211313532523117799/4064412800000000000000)*u^6+(-10817864708597799780014930267/12193238400000000000000)*u^7+(279257817712378755888089074373/409692810240000000000000)*u^8+(-14840790166558604894178707/64014501600000000000)*u^9+(16286581180547476652261/365797152000000000)*u^10+(-150445992649909823/32660460000000)*u^11+(572945568989021/3657971520000)*u^12+(73513960579/5715580500)*u^13+(-242585011/228623220)*u^14+(555440/80018127)*u^15+(-21500/80018127)*u^16)/((u-(0))^3*(u-(-2))^4*(u-(-3581/200))^4*((u^2+16*u+4))^1*(F1BFullFTC.quadTwo u)^1)
def partialValue (u : ℝ) : ℝ := (poleKernel (0) c0_1 c0_2 c0_3 u+c0_4/(u-(0))^4)+(poleKernel (-2) c2_1 c2_2 c2_3 u+c2_4/(u-(-2))^4)+(poleKernel (-3581/200) c6_1 c6_2 c6_3 u+c6_4/(u-(-3581/200))^4)+(f0*u+g0)/((u^2+16*u+4))+(f3*u+g3)/(F1BFullFTC.quadTwo u)+p0+p1*u
def primitive (u : ℝ) : ℝ := F1FreshFTC.pole4 (0) c0_1 c0_2 c0_3 c0_4 u+F1FreshFTC.pole4 (-2) c2_1 c2_2 c2_3 c2_4 u+F1FreshFTC.pole4 (-3581/200) c6_1 c6_2 c6_3 c6_4 u+F1JointFTC.quadraticPrimitive f0 g0 u+F1BFullFTC.quadPrimitiveTwo f3 g3 u+p0*u+(p1/2)*u^2

theorem source_exact {u : ℝ} (hu : 2 ≤ u) : kA1 u*kB2 u/u=kernel u := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  dsimp only [kA1,kB2,kernel,F1BFullFTC.quadTwo]
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
  ring_nf
  field_simp (disch := positivity)
  unfold c0_1 c0_2 c0_3 c0_4 c2_1 c2_2 c2_3 c2_4 c6_1 c6_2 c6_3 c6_4 g0 f0 g3 f3 p0 p1
  ring_nf

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := F1FreshFTC.pole4_deriv (0) c0_1 c0_2 c0_3 c0_4 u (by linarith)
  have h1 := F1FreshFTC.pole4_deriv (-2) c2_1 c2_2 c2_3 c2_4 u (by linarith)
  have h2 := F1FreshFTC.pole4_deriv (-3581/200) c6_1 c6_2 c6_3 c6_4 u (by linarith)
  have h3 := F1JointFTC.quadraticPrimitive_deriv f0 g0 hu
  have h4 := F1BFullFTC.quadPrimitiveTwo_deriv f3 g3 hu
  have h5 := ((hasDerivAt_id u).const_mul p0).add (((hasDerivAt_id u).pow 2).const_mul (p1/2))
  rw [partial_exact hu]
  convert (((((h0.add h1).add h2).add h3).add h4).add h5) using 1 <;> first | rfl | (funext x; dsimp [primitive]; ring) | (dsimp [partialValue]; ring)

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

end F1CrossFTC.A1B2
