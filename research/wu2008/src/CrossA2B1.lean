import CrossRational

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1FactorCross
open scoped Interval
namespace F1CrossFTC.A2B1

def c0_1 : ℝ := 423045370400134105766639601/18934959655370200601602087876
def c0_2 : ℝ := 0
def c0_3 : ℝ := 0
def c0_4 : ℝ := 0
def c1_1 : ℝ := 80778143873875114619129769653284636077461/198873603843945728133840908761079266043985840
def c1_2 : ℝ := -46564376702810993951976043/4391551029333367323377660856240
def c1_3 : ℝ := 0
def c1_4 : ℝ := 0
def c3_1 : ℝ := 1012320395491341045971669122413605946042990397594461119524362399199831742576/112825027040786337603544602190214252891464764684509760910784182112106840089145
def c3_2 : ℝ := -15027407607599172302840507962715856276257032876821924215562344/8176624717623931673194002863957141322183139700343944869302122805
def c3_3 : ℝ := 180578329182469774320626792407570214811351306592/592574125851436419499388005863465100270935340439745
def c3_4 : ℝ := 101565250257609675828526008617728/42944871111882698259462233501606018205
def c4_1 : ℝ := 1453363275196776874285226548028036682877680921703/351829322154098608856044434929291072652848749514700
def c4_2 : ℝ := 492308694542777411123547688741391/182179130293479973834963211249340000
def c4_3 : ℝ := 0
def c4_4 : ℝ := 0
def c5_1 : ℝ := 191460394075114953184675787227016473595015850940456516810811255364497891401781283754/10429687331721010198566554752763092479158159513780269824754236839845383764553560154225
def c5_2 : ℝ := 58517228166282486913592951949417050984395563840047549346442053031163/6173353486406160820759718755226001420780025562696651221749071405553750
def c5_3 : ℝ := 6986704034847849419278463063667716376671221072361174213/179047013658643418250641713771865044312729171830983062500
def c5_4 : ℝ := -4233379931055414628546541823567604561577/2596468286699472776049976830284334979687500
def g1 : ℝ := 11291071073716477033491804134296701648379250426700500/20938944405986616145618203276629939784492413356887987
def f1 : ℝ := -1369806141157657100764848593878809497645248811075750/2326549378442957349513133697403326642721379261876443
def g2 : ℝ := -588196333657403440336363488569468588227846359155144642589464377/257584787199848269087333859038733107550498297333482260314704344
def f2 : ℝ := -5899563620837840562992446720501882267262928735988951364991175/10732699466660344545305577459947212814604095722228427513112681
def p0 : ℝ := 0
def p1 : ℝ := 0

def kernel (u : ℝ) : ℝ := ((64478794452085673794641/7840000000000000000)+(-443507036333454197740189/8400000000000000000)*u+(307742442767920541645285653/2116800000000000000000)*u^2+(-610557384494971135025558309/2721600000000000000000)*u^3+(32244365083584274858067987/153090000000000000000)*u^4+(-20998316713653687571896525799/176359680000000000000000)*u^5+(39065059784764504225810290631/1175731200000000000000000)*u^6+(8241562265829437228965710491/2743372800000000000000000)*u^7+(-518490997898706914457395520187/84652646400000000000000000)*u^8+(2003405274471889508064971989/925888320000000000000000)*u^9+(-748320920651261969425973/2645395200000000000000)*u^10+(-85936824584623507997/3306744000000000000)*u^11+(336255621832950991/26453952000000000)*u^12+(-3169768758587/3306744000000)*u^13+(-1690749919043/11573604000000)*u^14+(59914441/2066715000)*u^15+(-1646513/1157360400)*u^16)/((u-(0))^1*(u-(1))^2*(u-(2/3))^4*(u-(-1327/200))^2*(u-(-1727/600))^4*((21*u^2-24*u+4))^1*(F1BFullFTC.quadOne u)^1)
def partialValue (u : ℝ) : ℝ := (poleKernel (0) c0_1 c0_2 c0_3 u+c0_4/(u-(0))^4)+(poleKernel (1) c1_1 c1_2 c1_3 u+c1_4/(u-(1))^4)+(poleKernel (2/3) c3_1 c3_2 c3_3 u+c3_4/(u-(2/3))^4)+(poleKernel (-1327/200) c4_1 c4_2 c4_3 u+c4_4/(u-(-1327/200))^4)+(poleKernel (-1727/600) c5_1 c5_2 c5_3 u+c5_4/(u-(-1727/600))^4)+(f1*u+g1)/((21*u^2-24*u+4))+(f2*u+g2)/(F1BFullFTC.quadOne u)+p0+p1*u
def primitive (u : ℝ) : ℝ := F1FreshFTC.pole4 (0) c0_1 c0_2 c0_3 c0_4 u+F1FreshFTC.pole4 (1) c1_1 c1_2 c1_3 c1_4 u+F1FreshFTC.pole4 (2/3) c3_1 c3_2 c3_3 c3_4 u+F1FreshFTC.pole4 (-1327/200) c4_1 c4_2 c4_3 c4_4 u+F1FreshFTC.pole4 (-1727/600) c5_1 c5_2 c5_3 c5_4 u+F1ActualSecondFTC.affinePrimitive f1 g1 u+F1BFullFTC.quadPrimitiveOne f2 g2 u+p0*u+(p1/2)*u^2

theorem source_exact {u : ℝ} (hu : 2 ≤ u) : kA2 u*kB1 u/u=kernel u := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  dsimp only [kA2,kB1,kernel,F1BFullFTC.quadOne]
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
  unfold c0_1 c0_2 c0_3 c0_4 c1_1 c1_2 c1_3 c1_4 c3_1 c3_2 c3_3 c3_4 c4_1 c4_2 c4_3 c4_4 c5_1 c5_2 c5_3 c5_4 g1 f1 g2 f2 p0 p1
  ring_nf
  all_goals (field_simp; ring)

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := F1FreshFTC.pole4_deriv (0) c0_1 c0_2 c0_3 c0_4 u (by linarith)
  have h1 := F1FreshFTC.pole4_deriv (1) c1_1 c1_2 c1_3 c1_4 u (by linarith)
  have h2 := F1FreshFTC.pole4_deriv (2/3) c3_1 c3_2 c3_3 c3_4 u (by linarith)
  have h3 := F1FreshFTC.pole4_deriv (-1327/200) c4_1 c4_2 c4_3 c4_4 u (by linarith)
  have h4 := F1FreshFTC.pole4_deriv (-1727/600) c5_1 c5_2 c5_3 c5_4 u (by linarith)
  have h5 := F1ActualSecondFTC.affinePrimitive_deriv f1 g1 hu
  have h6 := F1BFullFTC.quadPrimitiveOne_deriv f2 g2 hu
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

end F1CrossFTC.A2B1
