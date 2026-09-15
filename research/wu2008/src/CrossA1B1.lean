import CrossRational

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1FactorCross
open scoped Interval
namespace F1CrossFTC.A1B1

def c0_1 : ℝ := -20131157976617711609348015421262399692453046047081495/77194979897921039810778208585914241087670907401255044
def c0_2 : ℝ := 1696806058630634094207263653642595373504/47789967402365303729327184960518537589235
def c0_3 : ℝ := -9838264427910095482945107/3381242795601821536000372835
def c0_4 : ℝ := 0
def c2_1 : ℝ := 1087014454842384760260563640054075782844206738582673425577050552/428416170488283573418649574387134435532544647263544419691261
def c2_2 : ℝ := -4882869007481482690713510644616463577967994891545224/5254610226841765748123941544366236692519187504755
def c2_3 : ℝ := 32890119828658081599503490268023018789344/116007926330626984488536942315664633345
def c2_4 : ℝ := 20716908459873891625520589568/853716285354298337175550185
def c4_1 : ℝ := -1444607176662677260771533809825211580472609/172185064323351577743626287003268452871505
def c4_2 : ℝ := -197486166954518407556137799562541/36114794050692939207923845017000
def c4_3 : ℝ := 0
def c4_4 : ℝ := 0
def c5_1 : ℝ := -176395804598966320296693351159008783026436047137179288601182949666390428936/71532890254309124598613035688246121685883402342621304487045929736950745
def c5_2 : ℝ := -186384849836665392787212908484141500182222199787807535479966262/161632304634024436135455703944831135410674868400735174501375
def c5_3 : ℝ := -501683876028077397246146152739466586487636153631979/1095649923067339497025990407541253763660302146875
def c5_4 : ℝ := 469784558205476975142217865032273377787/22281104448190234244033960950823203125
def g0 : ℝ := 104911369778647905664942036886684363201336669036541128016500/13197097795958112543833322944995913697137096974155339911229
def f0 : ℝ := 646457083444932870602925894964995380215963330001261768750/1466344199550901393759258104999545966348566330461704434581
def g2 : ℝ := -4565431646006545598714380985761008567891549074090596496605/513876575753775365205962212195682351377791476636534442
def f2 : ℝ := -340676552819562406098441846802764644346399692080965486500/256938287876887682602981106097841175688895738318267221
def p0 : ℝ := 0
def p1 : ℝ := 0

def kernel (u : ℝ) : ℝ := ((-121460054665556734357347/1400000000000000000)+(1522423871179212646618497/4900000000000000000)*u+(-21726072053668304336241987/19600000000000000000)*u^2+(3228728505722020993290911/1680000000000000000)*u^3+(-5338935789497361709976849/3780000000000000000)*u^4+(390810284714059432899055879/2721600000000000000000)*u^5+(1520611712481138530590402973/3628800000000000000000)*u^6+(-882536755119972592487197837/3628800000000000000000)*u^7+(9101962150084422526117792633/365783040000000000000000)*u^8+(12361032515981037756009551/571536000000000000000)*u^9+(-13277737876855609655887/1632960000000000000)*u^10+(171314260333202831/291600000000000)*u^11+(3274754977127549/16329600000000)*u^12+(-383960765861/10206000000)*u^13+(-743799391/1020600000)*u^14+(5502053/8930250)*u^15+(-27907/714420)*u^16)/((u-(0))^3*(u-(-2))^4*(u-(-1327/200))^2*(u-(-1727/600))^4*((u^2+16*u+4))^1*(F1BFullFTC.quadOne u)^1)
def partialValue (u : ℝ) : ℝ := (poleKernel (0) c0_1 c0_2 c0_3 u+c0_4/(u-(0))^4)+(poleKernel (-2) c2_1 c2_2 c2_3 u+c2_4/(u-(-2))^4)+(poleKernel (-1327/200) c4_1 c4_2 c4_3 u+c4_4/(u-(-1327/200))^4)+(poleKernel (-1727/600) c5_1 c5_2 c5_3 u+c5_4/(u-(-1727/600))^4)+(f0*u+g0)/((u^2+16*u+4))+(f2*u+g2)/(F1BFullFTC.quadOne u)+p0+p1*u
def primitive (u : ℝ) : ℝ := F1FreshFTC.pole4 (0) c0_1 c0_2 c0_3 c0_4 u+F1FreshFTC.pole4 (-2) c2_1 c2_2 c2_3 c2_4 u+F1FreshFTC.pole4 (-1327/200) c4_1 c4_2 c4_3 c4_4 u+F1FreshFTC.pole4 (-1727/600) c5_1 c5_2 c5_3 c5_4 u+F1JointFTC.quadraticPrimitive f0 g0 u+F1BFullFTC.quadPrimitiveOne f2 g2 u+p0*u+(p1/2)*u^2

theorem source_exact {u : ℝ} (hu : 2 ≤ u) : kA1 u*kB1 u/u=kernel u := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  dsimp only [kA1,kB1,kernel,F1BFullFTC.quadOne]
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
  dsimp only [kernel,partialValue,poleKernel,F1BFullFTC.quadOne]
  have hv : 0 ≤ u-2 := by linarith
  generalize he : u-2=v at hv
  have heq : u=v+2 := by linarith
  rw [heq]
  field_simp (disch := positivity)
  unfold c0_1 c0_2 c0_3 c0_4 c2_1 c2_2 c2_3 c2_4 c4_1 c4_2 c4_3 c4_4 c5_1 c5_2 c5_3 c5_4 g0 f0 g2 f2 p0 p1
  ring_nf
  all_goals (field_simp; ring)

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := F1FreshFTC.pole4_deriv (0) c0_1 c0_2 c0_3 c0_4 u (by linarith)
  have h1 := F1FreshFTC.pole4_deriv (-2) c2_1 c2_2 c2_3 c2_4 u (by linarith)
  have h2 := F1FreshFTC.pole4_deriv (-1327/200) c4_1 c4_2 c4_3 c4_4 u (by linarith)
  have h3 := F1FreshFTC.pole4_deriv (-1727/600) c5_1 c5_2 c5_3 c5_4 u (by linarith)
  have h4 := F1JointFTC.quadraticPrimitive_deriv f0 g0 hu
  have h5 := F1BFullFTC.quadPrimitiveOne_deriv f2 g2 hu
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
  apply ContinuousAt.continuousWithinAt
  unfold kernel F1BFullFTC.quadOne
  fun_prop (disch := positivity)

def mass : ℝ := primitive (927/200)-primitive 2

theorem integral_exact : (∫ u in (2:ℝ)..(927/200), kernel u)=mass := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    apply primitive_deriv
    rw [uIcc_of_le (by norm_num : (2:ℝ)≤927/200)] at hu
    exact hu.1
  · exact kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num)

end F1CrossFTC.A1B1
