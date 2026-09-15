import F1FreshPole

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment
open scoped Interval
namespace F1FreshFTC.ATwo

def c0_1 : ℝ := 309/9289
def c0_2 : ℝ := 0
def c0_3 : ℝ := 0
def c0_4 : ℝ := 0
def c1_1 : ℝ := -25881227965351963303645865671/212542318675726636140790413124230
def c1_2 : ℝ := 0
def c1_3 : ℝ := 0
def c1_4 : ℝ := 0
def c2_1 : ℝ := 279577721/979326180
def c2_2 : ℝ := -727/91620
def c2_3 : ℝ := 0
def c2_4 : ℝ := 0
def c3_1 : ℝ := 1930938412229467936/9399150105321564315
def c3_2 : ℝ := 1399534164992/79460550232245
def c3_3 : ℝ := 15560644096/1469140508745
def c3_4 : ℝ := 2438144/3018092805
def f : ℝ := -1846998100/167820849
def g : ℝ := 586809200/167820849
def p0 : ℝ := 0
def p1 : ℝ := 0

def kernel (u : ℝ) : ℝ := (u-2)^7*(17*u-10)*(927/200-u)/((34020)*(u-(0))^1*(u-(-1327/200))^1*(u-(1))^2*(u-(2/3))^4*(21*u^2-24*u+4))
def partialValue (u : ℝ) : ℝ := (poleKernel (0) c0_1 c0_2 c0_3 u+c0_4/(u-(0))^4)+
  (poleKernel (-1327/200) c1_1 c1_2 c1_3 u+c1_4/(u-(-1327/200))^4)+
  (poleKernel (1) c2_1 c2_2 c2_3 u+c2_4/(u-(1))^4)+
  (poleKernel (2/3) c3_1 c3_2 c3_3 u+c3_4/(u-(2/3))^4)+(f*u+g)/(21*u^2-24*u+4)+p0+p1*u
def primitive (u : ℝ) : ℝ := pole4 (0) c0_1 c0_2 c0_3 c0_4 u+
  pole4 (-1327/200) c1_1 c1_2 c1_3 c1_4 u+
  pole4 (1) c2_1 c2_2 c2_3 c2_4 u+
  pole4 (2/3) c3_1 c3_2 c3_3 c3_4 u+F1ActualSecondFTC.affinePrimitive f g u+p0*u+(p1/2)*u^2

theorem partial_exact {u : ℝ} (hu : 2 ≤ u) : kernel u = partialValue u := by
  have hu0 : 0 < u := by linarith
  have h0 : 0 < u-(0) := by linarith
  have h1 : 0 < u-(-1327/200) := by linarith
  have h2 : 0 < u-(1) := by linarith
  have h3 : 0 < u-(2/3) := by linarith
  have hq : 0 < (21*u^2-24*u+4) := by nlinarith [sq_nonneg (u-2)]
  unfold kernel partialValue poleKernel
  generalize hr1 : (-1327/200:ℝ) = r1 at *
  generalize hr3 : (2/3:ℝ) = r3 at *
  generalize hqq : (21*u^2-24*u+4) = qq at *
  field_simp [h0.ne',h1.ne',h2.ne',h3.ne',hq.ne']
  rw [← hr1, ← hr3, ← hqq]
  unfold c0_1 c0_2 c0_3 c0_4 c1_1 c1_2 c1_3 c1_4 c2_1 c2_2 c2_3 c2_4 c3_1 c3_2 c3_3 c3_4 f g p0 p1
  ring

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := pole4_deriv (0) c0_1 c0_2 c0_3 c0_4 u (by linarith)
  have h1 := pole4_deriv (-1327/200) c1_1 c1_2 c1_3 c1_4 u (by linarith)
  have h2 := pole4_deriv (1) c2_1 c2_2 c2_3 c2_4 u (by linarith)
  have h3 := pole4_deriv (2/3) c3_1 c3_2 c3_3 c3_4 u (by linarith)
  have hq := F1ActualSecondFTC.affinePrimitive_deriv f g hu
  have hp := (((hasDerivAt_id u).const_mul p0).add (((hasDerivAt_id u).pow 2).const_mul (p1/2)))
  rw [partial_exact hu]
  convert (((((h0.add h1).add h2).add h3).add hq).add hp) using 1 <;> first | rfl | (funext x; dsimp [primitive]; ring) | (dsimp [partialValue]; ring)

theorem kernel_continuousOn : ContinuousOn kernel (Icc 2 (927/200)) := by
  intro u hu
  have hu := hu.1
  have hu0 : 0 < u := by linarith
  have h0 : 0 < u-(0) := by linarith
  have h1 : 0 < u-(-1327/200) := by linarith
  have h2 : 0 < u-(1) := by linarith
  have h3 : 0 < u-(2/3) := by linarith
  have hq : 0 < (21*u^2-24*u+4) := by nlinarith [sq_nonneg (u-2)]
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

end F1FreshFTC.ATwo
