import F1FreshPole

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment
open scoped Interval
namespace F1FreshFTC.BTwo

def c0_1 : ℝ := 18383022860504599058382311/88388871099291667566826349430
def c0_2 : ℝ := 0
def c0_3 : ℝ := 0
def c0_4 : ℝ := 0
def c1_1 : ℝ := -3995973046154760054380140871/4788751447172408997393684219414690
def c1_2 : ℝ := 0
def c1_3 : ℝ := 0
def c1_4 : ℝ := 0
def c2_1 : ℝ := 549538882896655078204501634514688/213106632776211324777637562557335
def c2_2 : ℝ := -1795210531569306167608558336/50101406881821161190435375
def c2_3 : ℝ := 9696936616788954423296/35336548733897503125
def c2_4 : ℝ := -4893150004348816/8307628828125
def f : ℝ := -3613612603120956800/184679423953837083
def g : ℝ := -30074270283406521032/184679423953837083
def p0 : ℝ := 4707440/34293483
def p1 : ℝ := -8000/11431161

def kernel (u : ℝ) : ℝ := 8*(u-2)*(927/200-u)^7*(17*(1127/200)+7*(u+1))/((80018127/1000)*(u-(-2))^1*(u-(2/3))^1*(u-(-3581/200))^4*(F1BFullFTC.quadTwo u))
def partialValue (u : ℝ) : ℝ := (poleKernel (-2) c0_1 c0_2 c0_3 u+c0_4/(u-(-2))^4)+
  (poleKernel (2/3) c1_1 c1_2 c1_3 u+c1_4/(u-(2/3))^4)+
  (poleKernel (-3581/200) c2_1 c2_2 c2_3 u+c2_4/(u-(-3581/200))^4)+(f*u+g)/(F1BFullFTC.quadTwo u)+p0+p1*u
def primitive (u : ℝ) : ℝ := pole4 (-2) c0_1 c0_2 c0_3 c0_4 u+
  pole4 (2/3) c1_1 c1_2 c1_3 c1_4 u+
  pole4 (-3581/200) c2_1 c2_2 c2_3 c2_4 u+F1BFullFTC.quadPrimitiveTwo f g u+p0*u+(p1/2)*u^2

theorem partial_exact {u : ℝ} (hu : 2 ≤ u) : kernel u = partialValue u := by
  have hu0 : 0 < u := by linarith
  have h0 : 0 < u-(-2) := by linarith
  have h1 : 0 < u-(2/3) := by linarith
  have h2 : 0 < u-(-3581/200) := by linarith
  have hq : 0 < (F1BFullFTC.quadTwo u) := by unfold F1BFullFTC.quadTwo; positivity
  unfold kernel partialValue poleKernel
  generalize hr1 : (2/3:ℝ) = r1 at *
  generalize hr2 : (-3581/200:ℝ) = r2 at *
  field_simp [h0.ne',h1.ne',h2.ne',hq.ne']
  rw [← hr1, ← hr2]
  unfold c0_1 c0_2 c0_3 c0_4 c1_1 c1_2 c1_3 c1_4 c2_1 c2_2 c2_3 c2_4 f g p0 p1 F1BFullFTC.quadTwo
  ring

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := pole4_deriv (-2) c0_1 c0_2 c0_3 c0_4 u (by linarith)
  have h1 := pole4_deriv (2/3) c1_1 c1_2 c1_3 c1_4 u (by linarith)
  have h2 := pole4_deriv (-3581/200) c2_1 c2_2 c2_3 c2_4 u (by linarith)
  have hq := F1BFullFTC.quadPrimitiveTwo_deriv f g hu
  have hp := (((hasDerivAt_id u).const_mul p0).add (((hasDerivAt_id u).pow 2).const_mul (p1/2)))
  rw [partial_exact hu]
  convert ((((h0.add h1).add h2).add hq).add hp) using 1 <;> first | rfl | (funext x; dsimp [primitive]; ring) | (dsimp [partialValue]; ring)

theorem kernel_continuousOn : ContinuousOn kernel (Icc 2 (927/200)) := by
  intro u hu
  have hu := hu.1
  have hu0 : 0 < u := by linarith
  have h0 : 0 < u-(-2) := by linarith
  have h1 : 0 < u-(2/3) := by linarith
  have h2 : 0 < u-(-3581/200) := by linarith
  have hq : 0 < (F1BFullFTC.quadTwo u) := by unfold F1BFullFTC.quadTwo; positivity
  apply ContinuousAt.continuousWithinAt
  unfold kernel
  unfold F1BFullFTC.quadTwo at *
  fun_prop (disch := positivity)

def mass : ℝ := primitive (927/200)-primitive 2

theorem integral_exact : (∫ u in (2:ℝ)..(927/200), kernel u) = mass := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    apply primitive_deriv
    rw [uIcc_of_le (by norm_num : (2:ℝ) ≤ 927/200)] at hu
    exact hu.1
  · exact kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num)

end F1FreshFTC.BTwo
