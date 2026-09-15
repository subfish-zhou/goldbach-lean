import CrossRational

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1FactorCross
open scoped Interval
namespace F1CrossFTC.AB1

def c2_1 : ℝ := -129762566476292831670863209571946301919849231902418/50043906922302530934513728993964158976373214331
def c2_2 : ℝ := 1123124474134632803285343097786560834968/1104837393625018899890828022053948889
def c2_3 : ℝ := -2589613557484236453190073696/8130631289088555592148097
def c2_4 : ℝ := 0
def c3_1 : ℝ := -52357428620373300891518542646109338513537643852874278167582/8652512928702573199147092977732424679558877989781952242647749
def c3_2 : ℝ := 1142811374162595171682174757876423132900355400/627062567038557057671310059114777883884587661841
def c3_3 : ℝ := -12695656282201209478565751077216/45444308054902326200489135980535469
def c3_4 : ℝ := 0
def c4_1 : ℝ := 19441296358150076858126966672/4080404410734284428955444415
def c4_2 : ℝ := 209237100293198820207442/75354897670329224478375
def c4_3 : ℝ := 0
def c4_4 : ℝ := 0
def c5_1 : ℝ := 1488965076173443319679393086103588233665780096/585667577541871764615650352463138698885645
def c5_2 : ℝ := 15127177150446687898383245381395064134112/13062102451222864352150099436787225125
def c5_3 : ℝ := 373459389493520998891933171877883664/873969434140534169792428831584375
def c5_4 : ℝ := -3479719708008551160354540465392/175428704834668554567948984375
def g2 : ℝ := 8645597256443719862781119174383266471744920/1375353860850817161560779281995348703693
def f2 : ℝ := 441673470932084013296475148272777689224000/458451286950272387186926427331782901231
def p0 : ℝ := 0
def p1 : ℝ := 0

def kernel (u : ℝ) : ℝ := ((-13495561629506303817483/140000000000000000)+(15862079341989968181771/56000000000000000)*u+(-309985662736641834942011/840000000000000000)*u^2+(3888375740194115703064607/15120000000000000000)*u^3+(-45120941502578011110398201/544320000000000000000)*u^4+(-65001520449690241616172731/9797760000000000000000)*u^5+(10999800630560191799611/729000000000000000)*u^6+(-4266957574310533258207/918540000000000000)*u^7+(339137109541025927/1148175000000000)*u^8+(1145207456703469/9185400000000)*u^9+(-79580312831/3444525000)*u^10+(-97461797/191362500)*u^11+(259328/637875)*u^12+(-2596/98415)*u^13)/((u-(-2))^3*(u-(2/3))^3*(u-(-1327/200))^2*(u-(-1727/600))^4*(F1BFullFTC.quadOne u)^1)
def partialValue (u : ℝ) : ℝ := (poleKernel (-2) c2_1 c2_2 c2_3 u+c2_4/(u-(-2))^4)+(poleKernel (2/3) c3_1 c3_2 c3_3 u+c3_4/(u-(2/3))^4)+(poleKernel (-1327/200) c4_1 c4_2 c4_3 u+c4_4/(u-(-1327/200))^4)+(poleKernel (-1727/600) c5_1 c5_2 c5_3 u+c5_4/(u-(-1727/600))^4)+(f2*u+g2)/(F1BFullFTC.quadOne u)+p0+p1*u
def primitive (u : ℝ) : ℝ := F1FreshFTC.pole4 (-2) c2_1 c2_2 c2_3 c2_4 u+F1FreshFTC.pole4 (2/3) c3_1 c3_2 c3_3 c3_4 u+F1FreshFTC.pole4 (-1327/200) c4_1 c4_2 c4_3 c4_4 u+F1FreshFTC.pole4 (-1727/600) c5_1 c5_2 c5_3 c5_4 u+F1BFullFTC.quadPrimitiveOne f2 g2 u+p0*u+(p1/2)*u^2

theorem source_exact {u : ℝ} (hu : 2 ≤ u) : aDiff u*kB1 u/u=kernel u := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  dsimp only [aDiff,kB1,kernel,F1BFullFTC.quadOne]
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
  ring_nf
  field_simp (disch := positivity)
  unfold c2_1 c2_2 c2_3 c2_4 c3_1 c3_2 c3_3 c3_4 c4_1 c4_2 c4_3 c4_4 c5_1 c5_2 c5_3 c5_4 g2 f2 p0 p1
  ring_nf

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := F1FreshFTC.pole4_deriv (-2) c2_1 c2_2 c2_3 c2_4 u (by linarith)
  have h1 := F1FreshFTC.pole4_deriv (2/3) c3_1 c3_2 c3_3 c3_4 u (by linarith)
  have h2 := F1FreshFTC.pole4_deriv (-1327/200) c4_1 c4_2 c4_3 c4_4 u (by linarith)
  have h3 := F1FreshFTC.pole4_deriv (-1727/600) c5_1 c5_2 c5_3 c5_4 u (by linarith)
  have h4 := F1BFullFTC.quadPrimitiveOne_deriv f2 g2 hu
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
  have hp2 : 0 < u-(-2) := by linarith
  have hp3 : 0 < u-(2/3) := by linarith
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

end F1CrossFTC.AB1
