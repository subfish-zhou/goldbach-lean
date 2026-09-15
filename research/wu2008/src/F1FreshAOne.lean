import F1FreshPole

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment
open scoped Interval
namespace F1FreshFTC.AOne

def c0_1 : ℝ := -160012718415/16357269481
def c0_2 : ℝ := 327535424/184897545
def c0_3 : ℝ := -1236/6635
def c0_4 : ℝ := 0
def c1_1 : ℝ := -115673796818912/46522118805183
def c1_2 : ℝ := -228907337728/250928364645
def c1_3 : ℝ := -1427858944/270688635
def c1_4 : ℝ := -1358848/292005
def c2_1 : ℝ := 11316121417482364182358781122/12038264683564313069307948339
def c2_2 : ℝ := 0
def c2_3 : ℝ := 0
def c2_4 : ℝ := 0
def f : ℝ := 4958225900/439514019
def g : ℝ := 80482169200/439514019
def p0 : ℝ := 0
def p1 : ℝ := 0

def kernel (u : ℝ) : ℝ := (u-2)^7*(5*u+14)*(927/200-u)/((105)*(u-(0))^3*(u-(-2))^4*(u-(-1327/200))^1*(u^2+16*u+4))
def partialValue (u : ℝ) : ℝ := (poleKernel (0) c0_1 c0_2 c0_3 u+c0_4/(u-(0))^4)+
  (poleKernel (-2) c1_1 c1_2 c1_3 u+c1_4/(u-(-2))^4)+
  (poleKernel (-1327/200) c2_1 c2_2 c2_3 u+c2_4/(u-(-1327/200))^4)+(f*u+g)/(u^2+16*u+4)+p0+p1*u
def primitive (u : ℝ) : ℝ := pole4 (0) c0_1 c0_2 c0_3 c0_4 u+
  pole4 (-2) c1_1 c1_2 c1_3 c1_4 u+
  pole4 (-1327/200) c2_1 c2_2 c2_3 c2_4 u+F1JointFTC.quadraticPrimitive f g u+p0*u+(p1/2)*u^2

theorem partial_exact {u : ℝ} (hu : 2 ≤ u) : kernel u = partialValue u := by
  have hu0 : 0 < u := by linarith
  have h0 : 0 < u-(0) := by linarith
  have h1 : 0 < u-(-2) := by linarith
  have h2 : 0 < u-(-1327/200) := by linarith
  have hq : 0 < (u^2+16*u+4) := by positivity
  unfold kernel partialValue poleKernel
  field_simp (disch := positivity)
  unfold c0_1 c0_2 c0_3 c0_4 c1_1 c1_2 c1_3 c1_4 c2_1 c2_2 c2_3 c2_4 f g p0 p1
  ring_nf
  field_simp
  ring

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := pole4_deriv (0) c0_1 c0_2 c0_3 c0_4 u (by linarith)
  have h1 := pole4_deriv (-2) c1_1 c1_2 c1_3 c1_4 u (by linarith)
  have h2 := pole4_deriv (-1327/200) c2_1 c2_2 c2_3 c2_4 u (by linarith)
  have hq := F1JointFTC.quadraticPrimitive_deriv f g hu
  have hp := (((hasDerivAt_id u).const_mul p0).add (((hasDerivAt_id u).pow 2).const_mul (p1/2)))
  rw [partial_exact hu]
  convert ((((h0.add h1).add h2).add hq).add hp) using 1 <;> first | rfl | (funext x; dsimp [primitive]; ring) | (dsimp [partialValue]; ring)

theorem kernel_continuousOn : ContinuousOn kernel (Icc 2 (927/200)) := by
  intro u hu
  have hu := hu.1
  have hu0 : 0 < u := by linarith
  have h0 : 0 < u-(0) := by linarith
  have h1 : 0 < u-(-2) := by linarith
  have h2 : 0 < u-(-1327/200) := by linarith
  have hq : 0 < (u^2+16*u+4) := by positivity
  apply ContinuousAt.continuousWithinAt
  unfold kernel
  fun_prop (disch := positivity)

def mass : ℝ := primitive (927/200)-primitive 2

theorem integral_exact : (∫ u in (2:ℝ)..(927/200), kernel u) = mass := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    apply primitive_deriv
    rw [uIcc_of_le (by norm_num : (2:ℝ) ≤ 927/200)] at hu
    exact hu.1
  · exact kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num)

end F1FreshFTC.AOne
