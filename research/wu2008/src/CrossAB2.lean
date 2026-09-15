import CrossRational

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1FactorCross
open scoped Interval
namespace F1CrossFTC.AB2

def c2_1 : ℝ := 52040846031037638056275505482168645041642299179237/459063298763285108250262439316070424451185552424630
def c2_2 : ℝ := -1590713720380707678951276122933707865918/9554904246867582382645884402415814844705
def c2_3 : ℝ := 16107228142254111366486619768/132583306648937501350239524145
def c2_4 : ℝ := 0
def c3_1 : ℝ := -111532607327965826624005827039540551145219624187738692889/487787776487862715912599365646403134571454392348977574998690
def c3_2 : ℝ := 11157180218497273253283194584365872778331466/130493947468646743088341381518342276064508820687
def c3_3 : ℝ := -9389486019732824709761606941048/581833300831447693183332632658884835
def c3_4 : ℝ := 0
def c6_1 : ℝ := 962196401816034056790099848751685529160332980352/267749436964031659732848256269046185835347418815
def c6_2 : ℝ := -245422271234908982626318625412911396139296/6994215529545881297539946350752293705375
def c6_3 : ℝ := 3342883091853593029864281003525261616/4933023906856743629111980614753125
def c6_4 : ℝ := -851648047400148674448196386928/3479264366793136193780234375
def g3 : ℝ := -1814009226518654228597356108036096017455419066178440/8640283756256110607184030347747620188821298533403
def f3 : ℝ := -78688831026578652221367587895048921830818306792000/8640283756256110607184030347747620188821298533403
def p0 : ℝ := 11453360/308641347
def p1 : ℝ := -8000/44091621

def kernel (u : ℝ) : ℝ := ((-4633942666186872630152991/12701290000000000000)+(6533540506544609813100831/5080516000000000000)*u+(-53779641286331464088594949/25402580000000000000)*u^2+(106535411339133634571659737/50805160000000000000)*u^3+(-823914013298786974813017157/609661920000000000000)*u^4+(6363647461749644618998544033/10973914560000000000000)*u^5+(-13433039966149633503617/81651150000000000)*u^6+(6099020085864350060501/205760898000000000)*u^7+(-194287895961581833/64300280625000)*u^8+(42955225350313/411521796000)*u^9+(326235253868/38580168375)*u^10+(-122767108/171467415)*u^11+(475520/102880449)*u^12+(-8000/44091621)*u^13)/((u-(-2))^3*(u-(2/3))^3*(u-(-3581/200))^4*(F1BFullFTC.quadTwo u)^1)
def partialValue (u : ℝ) : ℝ := (poleKernel (-2) c2_1 c2_2 c2_3 u+c2_4/(u-(-2))^4)+(poleKernel (2/3) c3_1 c3_2 c3_3 u+c3_4/(u-(2/3))^4)+(poleKernel (-3581/200) c6_1 c6_2 c6_3 u+c6_4/(u-(-3581/200))^4)+(f3*u+g3)/(F1BFullFTC.quadTwo u)+p0+p1*u
def primitive (u : ℝ) : ℝ := F1FreshFTC.pole4 (-2) c2_1 c2_2 c2_3 c2_4 u+F1FreshFTC.pole4 (2/3) c3_1 c3_2 c3_3 c3_4 u+F1FreshFTC.pole4 (-3581/200) c6_1 c6_2 c6_3 c6_4 u+F1BFullFTC.quadPrimitiveTwo f3 g3 u+p0*u+(p1/2)*u^2

theorem source_exact {u : ℝ} (hu : 2 ≤ u) : aDiff u*kB2 u/u=kernel u := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  simp only [aDiff,kB2,kernel,F1BFullFTC.quadTwo]
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
  simp only [kernel,partialValue,poleKernel,F1BFullFTC.quadTwo]
  have hv : 0 ≤ u-2 := by linarith
  generalize he : u-2=v at hv
  have heq : u=v+2 := by linarith
  rw [heq]
  ring_nf
  field_simp (disch := positivity)
  unfold c2_1 c2_2 c2_3 c2_4 c3_1 c3_2 c3_3 c3_4 c6_1 c6_2 c6_3 c6_4 g3 f3 p0 p1
  ring_nf

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := F1FreshFTC.pole4_deriv (-2) c2_1 c2_2 c2_3 c2_4 u (by linarith)
  have h1 := F1FreshFTC.pole4_deriv (2/3) c3_1 c3_2 c3_3 c3_4 u (by linarith)
  have h2 := F1FreshFTC.pole4_deriv (-3581/200) c6_1 c6_2 c6_3 c6_4 u (by linarith)
  have h3 := F1BFullFTC.quadPrimitiveTwo_deriv f3 g3 hu
  have h4 := ((hasDerivAt_id u).const_mul p0).add (((hasDerivAt_id u).pow 2).const_mul (p1/2))
  rw [partial_exact hu]
  convert ((((h0.add h1).add h2).add h3).add h4) using 1 <;> first | rfl | (funext x; dsimp [primitive]; ring) | (dsimp [partialValue]; ring)

theorem kernel_continuousOn : ContinuousOn kernel (Icc 2 (927/200)) := by
  intro u hu
  have hu := hu.1
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hp2 : 0 < u-(-2) := by linarith
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

end F1CrossFTC.AB2
