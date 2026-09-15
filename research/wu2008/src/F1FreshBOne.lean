import F1FreshPole

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment
open scoped Interval
namespace F1FreshFTC.BOne

def c0_1 : ℝ := -5318541103512170165097602/2710210429696185197382699
def c0_2 : ℝ := 0
def c0_3 : ℝ := 0
def c0_4 : ℝ := 0
def c1_1 : ℝ := -6230611756473202030290694082/187013613394659778602835950537183
def c1_2 : ℝ := 0
def c1_3 : ℝ := 0
def c1_4 : ℝ := 0
def c2_1 : ℝ := 1072188004130768/247398597734535
def c2_2 : ℝ := 4387025566/1522945125
def c2_3 : ℝ := 0
def c2_4 : ℝ := 0
def c3_1 : ℝ := 66955970685915207739603656448/17263593760800674958862791735
def c3_2 : ℝ := -2204638194393765352769792/1155086122368188013616125
def c3_3 : ℝ := 405059882688666747136/77285411634112509375
def c3_4 : ℝ := -10792954078921616/5171073165703125
def f : ℝ := -1459611451635200/11120854285557
def g : ℝ := -16092749625292472/100087688570013
def p0 : ℝ := 0
def p1 : ℝ := 0

def kernel (u : ℝ) : ℝ := 8*(u-2)*(927/200-u)^7*(5*(1127/200)+19*(u+1))/((51030)*(u-(-2))^1*(u-(2/3))^1*(u-(-1327/200))^2*(u-(-1727/600))^4*(F1BFullFTC.quadOne u))
def partialValue (u : ℝ) : ℝ := (poleKernel (-2) c0_1 c0_2 c0_3 u+c0_4/(u-(-2))^4)+
  (poleKernel (2/3) c1_1 c1_2 c1_3 u+c1_4/(u-(2/3))^4)+
  (poleKernel (-1327/200) c2_1 c2_2 c2_3 u+c2_4/(u-(-1327/200))^4)+
  (poleKernel (-1727/600) c3_1 c3_2 c3_3 u+c3_4/(u-(-1727/600))^4)+(f*u+g)/(F1BFullFTC.quadOne u)+p0+p1*u
def primitive (u : ℝ) : ℝ := pole4 (-2) c0_1 c0_2 c0_3 c0_4 u+
  pole4 (2/3) c1_1 c1_2 c1_3 c1_4 u+
  pole4 (-1327/200) c2_1 c2_2 c2_3 c2_4 u+
  pole4 (-1727/600) c3_1 c3_2 c3_3 c3_4 u+F1BFullFTC.quadPrimitiveOne f g u+p0*u+(p1/2)*u^2

theorem partial_exact {u : ℝ} (hu : 2 ≤ u) : kernel u = partialValue u := by
  have hu0 : 0 < u := by linarith
  have h0 : 0 < u-(-2) := by linarith
  have h1 : 0 < u-(2/3) := by linarith
  have h2 : 0 < u-(-1327/200) := by linarith
  have h3 : 0 < u-(-1727/600) := by linarith
  have hq : 0 < (F1BFullFTC.quadOne u) := by unfold F1BFullFTC.quadOne; positivity
  unfold kernel partialValue poleKernel
  generalize hr1 : (2/3:ℝ) = r1 at *
  generalize hr2 : (-1327/200:ℝ) = r2 at *
  generalize hr3 : (-1727/600:ℝ) = r3 at *
  field_simp [h0.ne',h1.ne',h2.ne',h3.ne',hq.ne']
  rw [← hr1, ← hr2, ← hr3]
  unfold c0_1 c0_2 c0_3 c0_4 c1_1 c1_2 c1_3 c1_4 c2_1 c2_2 c2_3 c2_4 c3_1 c3_2 c3_3 c3_4 f g p0 p1 F1BFullFTC.quadOne
  ring

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := pole4_deriv (-2) c0_1 c0_2 c0_3 c0_4 u (by linarith)
  have h1 := pole4_deriv (2/3) c1_1 c1_2 c1_3 c1_4 u (by linarith)
  have h2 := pole4_deriv (-1327/200) c2_1 c2_2 c2_3 c2_4 u (by linarith)
  have h3 := pole4_deriv (-1727/600) c3_1 c3_2 c3_3 c3_4 u (by linarith)
  have hq := F1BFullFTC.quadPrimitiveOne_deriv f g hu
  have hp := (((hasDerivAt_id u).const_mul p0).add (((hasDerivAt_id u).pow 2).const_mul (p1/2)))
  rw [partial_exact hu]
  convert (((((h0.add h1).add h2).add h3).add hq).add hp) using 1 <;> first | rfl | (funext x; dsimp [primitive]; ring) | (dsimp [partialValue]; ring)

theorem kernel_continuousOn : ContinuousOn kernel (Icc 2 (927/200)) := by
  intro u hu
  have hu := hu.1
  have hu0 : 0 < u := by linarith
  have h0 : 0 < u-(-2) := by linarith
  have h1 : 0 < u-(2/3) := by linarith
  have h2 : 0 < u-(-1327/200) := by linarith
  have h3 : 0 < u-(-1727/600) := by linarith
  have hq : 0 < (F1BFullFTC.quadOne u) := by unfold F1BFullFTC.quadOne; positivity
  apply ContinuousAt.continuousWithinAt
  unfold kernel
  unfold F1BFullFTC.quadOne at *
  fun_prop (disch := positivity)

def mass : ℝ := primitive (927/200)-primitive 2

theorem integral_exact : (∫ u in (2:ℝ)..(927/200), kernel u) = mass := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    apply primitive_deriv
    rw [uIcc_of_le (by norm_num : (2:ℝ) ≤ 927/200)] at hu
    exact hu.1
  · exact kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num)

end F1FreshFTC.BOne
