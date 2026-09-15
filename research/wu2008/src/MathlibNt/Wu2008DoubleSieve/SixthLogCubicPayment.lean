import MathlibNt.Wu2008DoubleSieve.SixthLogCubicKernel

namespace Wu2008DoubleSieve.SixthLogCubicCorrection
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence SharpMassBalance
open PositiveSixthFTC DynamicSixthEnvelope
open scoped Interval

noncomputable def e : ℝ := lam+b
noncomputable def rationalLogCubic (x : ℝ) : ℝ :=
  (2/(3*x))*(A0 x*lowerLog ((lam-x)/b)+polynomialPart x (lam-x)-polynomialPart x b)

/-- Only the correction uses the lower logarithm; the old negative logarithm is unchanged. -/
theorem rationalLogCubic_lower {x : ℝ} (hx : x ∈ Icc a b) :
    rationalLogCubic x ≤ movingLogCubic x := by
  have hq : 1 ≤ (lam-x)/b := (le_div_iff₀ geometry.2.2.1).2 (by simpa using (moving_geometry hx).1)
  have hl := mul_le_mul_of_nonneg_left (log_lower hq) (moving_log_coefficient_nonneg hx)
  rw [movingLogCubic_eq hx]
  unfold rationalLogCubic
  nlinarith only [hl]

noncomputable def q0 : ℝ := -34977403155419255189042940963244903961610962432/38368580693536798577332675155578918798481915
noncomputable def q1 : ℝ := -214221816325402140730911264632619927377408/93572090472308510515562209708686451905
noncomputable def q2 : ℝ := 812292382566199175660761589977742336/293400871285198519123973369823645
noncomputable def q3 : ℝ := -125342479873502637947705580044288/2146610511228323754757233045
noncomputable def q4 : ℝ := 4324247250000075208216150016/15705259042795441610445
noncomputable def q5 : ℝ := -14138871702942956797952/12767164291546205
noncomputable def q6 : ℝ := 15300362145667514368/5884734164715
noncomputable def q7 : ℝ := -54440650866688/14351505
noncomputable def q8 : ℝ := 1715470336/945
noncomputable def initialLogCoefficient : ℝ := -1515813146569538574569986921474813463731849425088084000017583/8179661338138488581857949777491610681239341857085553248569745
noncomputable def terminalLogCoefficient : ℝ := 4009063088239887948863108734744184983469951171875/8374156592846617114099166598330573732498962403
noncomputable def poleTwo : ℝ := -6363419900039733359736107668567009642578125000/321802560277279528448780310767833264934980647
noncomputable def poleThree : ℝ := 1570182337419041757322561281984765625000000/4122082291824374011966717076120734521614601

/-- Fixed long division, verified as an identity rather than trusted computation. -/
theorem partial_fractions {x : ℝ} (hx : x ≠ 0) (he : e-x ≠ 0) :
    rationalLogCubic x = q0+q1*x^1+q2*x^2+q3*x^3+q4*x^4+q5*x^5+q6*x^6+q7*x^7+q8*x^8+
      initialLogCoefficient/x+terminalLogCoefficient/(e-x)+poleTwo/(e-x)^2+poleThree/(e-x)^3 := by
  have hb : b ≠ 0 := geometry.2.2.1.ne'
  have heq : lam-x+b ≠ 0 := by intro h; apply he; dsimp [e]; linarith
  unfold rationalLogCubic lowerLog polynomialPart A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 Q0 Q1 Q2 Q3 Q4 Q5 Q6 d0 d1 d2 d3
  field_simp [hx,hb,heq,he]
  norm_num [q0,q1,q2,q3,q4,q5,q6,q7,q8,initialLogCoefficient,terminalLogCoefficient,poleTwo,poleThree,
    e,lam,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  ring

noncomputable def polynomialPrimitive (x : ℝ) : ℝ := q0*x^1/1+q1*x^2/2+q2*x^3/3+q3*x^4/4+q4*x^5/5+q5*x^6/6+q6*x^7/7+q7*x^8/8+q8*x^9/9
noncomputable def outerPrimitive (x : ℝ) : ℝ :=
  polynomialPrimitive x+initialLogCoefficient*log x-terminalLogCoefficient*log (e-x)+
    poleTwo/(e-x)+poleThree/(2*(e-x)^2)

theorem outer_derivative {x : ℝ} (hx : x ≠ 0) (he : e-x ≠ 0) :
    HasDerivAt outerPrimitive (rationalLogCubic x) x := by
  rw [partial_fractions hx he]
  have hi := hasDerivAt_id x
  have hd := (hasDerivAt_const x e).sub hi
  have hp := (((((((((((hi.pow 1).const_mul q0).div_const 1).add (((hi.pow 2).const_mul q1).div_const 2)).add (((hi.pow 3).const_mul q2).div_const 3)).add (((hi.pow 4).const_mul q3).div_const 4)).add (((hi.pow 5).const_mul q4).div_const 5)).add (((hi.pow 6).const_mul q5).div_const 6)).add (((hi.pow 7).const_mul q6).div_const 7)).add (((hi.pow 8).const_mul q7).div_const 8)).add (((hi.pow 9).const_mul q8).div_const 9))
  have h := ((((hp.add ((hasDerivAt_log hx).const_mul initialLogCoefficient)).sub
    ((hd.log he).const_mul terminalLogCoefficient)).add
    ((hasDerivAt_const x poleTwo).div hd he)).add
    ((hasDerivAt_const x poleThree).div ((hd.pow 2).const_mul 2) (by exact mul_ne_zero (by norm_num) (pow_ne_zero 2 he))))
  convert h using 1 <;> first
  | rfl
  | (dsimp; field_simp [hx,he]; ring)

theorem denominators {x : ℝ} (hx : x ∈ Icc a b) : x ≠ 0 ∧ e-x ≠ 0 := by
  have hd := RationalMovingSixth.denominators hx
  exact ⟨hd.1,hd.2.2⟩

theorem rationalLogCubic_integrable : IntervalIntegrable rationalLogCubic volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hn (x : ℝ) (hx : x ∈ uIcc a b) := denominators (uIcc_of_le geometry.2.1 ▸ hx)
  have hi : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc a b) := continuousOn_id.inv₀ (fun x hx => (hn x hx).1)
  have he : ContinuousOn (fun x : ℝ => (e-x)⁻¹) (uIcc a b) :=
    (continuousOn_const.sub continuousOn_id).inv₀ (fun x hx => (hn x hx).2)
  have hc : ContinuousOn (fun x : ℝ => q0+q1*x^1+q2*x^2+q3*x^3+q4*x^4+q5*x^5+q6*x^6+q7*x^7+q8*x^8+
      initialLogCoefficient/x+terminalLogCoefficient/(e-x)+poleTwo/(e-x)^2+poleThree/(e-x)^3) (uIcc a b) := by
    simp only [div_eq_mul_inv,← inv_pow]
    fun_prop
  apply hc.congr
  intro x hx
  exact partial_fractions (hn x hx).1 (hn x hx).2

/-- The outer FTC is on the original interval, after the true moving inner FTC. -/
theorem outer_ftc : (∫ x in a..b, rationalLogCubic x) = outerPrimitive b-outerPrimitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ rationalLogCubic_integrable
  intro x hx
  have hd := denominators (uIcc_of_le geometry.2.1 ▸ hx)
  exact outer_derivative hd.1 hd.2

/-- Endpoint signs are checked independently: initial U, terminal L. -/
theorem endpoint_signUL : initialLogCoefficient < 0 ∧ 0 < terminalLogCoefficient := by
  norm_num [initialLogCoefficient,terminalLogCoefficient]

noncomputable def rationalEndpointPart : ℝ := polynomialPrimitive b-polynomialPrimitive a+
  poleTwo*(1/(e-b)-1/(e-a))+(poleThree/2)*(1/(e-b)^2-1/(e-a)^2)

noncomputable def deltaLog : ℝ := 4*(rationalEndpointPart+
  initialLogCoefficient*upperLog (b/a)+terminalLogCoefficient*lowerLog ((e-a)/(e-b)))

theorem endpoint_exact : 4*(outerPrimitive b-outerPrimitive a) = 4*(rationalEndpointPart+
    initialLogCoefficient*log (b/a)+terminalLogCoefficient*log ((e-a)/(e-b))) := by
  have he1 : e-a ≠ 0 := (denominators (left_mem_Icc.mpr geometry.2.1)).2
  have he2 : e-b ≠ 0 := (denominators (right_mem_Icc.mpr geometry.2.1)).2
  rw [log_div geometry.2.2.1.ne' geometry.1.ne',log_div he1 he2]
  unfold outerPrimitive rationalEndpointPart
  field_simp [he1,he2]
  ring

theorem deltaLog_lower : deltaLog ≤ 4*(outerPrimitive b-outerPrimitive a) := by
  have hl := log_upper (t := b/a)
    (by norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have hr := log_lower (t := (e-a)/(e-b))
    (by norm_num [e,lam,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have h1 := mul_le_mul_of_nonpos_left hl endpoint_signUL.1.le
  have h2 := mul_le_mul_of_nonneg_left hr endpoint_signUL.2.le
  rw [endpoint_exact]
  unfold deltaLog
  linarith only [h1,h2]

theorem deltaLog_exact : deltaLog = (1187400847683322048386560078365256261041294877546103876976007289970830388271148310198906709618961179/7545885901676678275919158598554354710005799650469246322063206213824795976825339983586567540013665636 : ℝ) := by
  norm_num [deltaLog,rationalEndpointPart,polynomialPrimitive,q0,q1,q2,q3,q4,q5,q6,q7,q8,
    initialLogCoefficient,terminalLogCoefficient,poleTwo,poleThree,e,lam,a,b,lowerLog,upperLog,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem deltaLog_pos : 0 < deltaLog := by
  rw [deltaLog_exact]
  norm_num

/-- All three payments descend from the single combined actual integral. -/
theorem actual_sixth_ge_rational_corrected :
    RationalMovingSixth.rationalSixth+SixthReciprocalCorrection.deltaSixth+deltaLog ≤
      truncatedSixthLowerF6lin := by
  have hi := intervalIntegral.integral_mono_on geometry.2.1
    ((RationalMovingSixth.integrable.add SixthReciprocalCorrection.rationalCorrection_integrable).add
      rationalLogCubic_integrable)
    ((movingValue_integrable.add SixthReciprocalCorrection.movingCorrection_integrable).add
      movingLogCubic_integrable)
    (fun x hx => add_le_add
      (add_le_add (RationalMovingSixth.rationalMoving_lower hx)
        (SixthReciprocalCorrection.rationalCorrection_lower hx)) (rationalLogCubic_lower hx))
  rw [intervalIntegral.integral_add
    (RationalMovingSixth.integrable.add SixthReciprocalCorrection.rationalCorrection_integrable)
    rationalLogCubic_integrable,
    intervalIntegral.integral_add RationalMovingSixth.integrable
      SixthReciprocalCorrection.rationalCorrection_integrable,
    outer_ftc,SixthReciprocalCorrection.outer_ftc] at hi
  have ho : (∫ x in a..b, RationalMovingSixth.rationalMoving x) =
      RationalMovingSixth.outerPrimitive b-RationalMovingSixth.outerPrimitive a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ RationalMovingSixth.integrable
    intro x hx
    have hd := RationalMovingSixth.denominators (uIcc_of_le geometry.2.1 ▸ hx)
    exact RationalMovingSixth.derivative hd.1 hd.2.1 hd.2.2
  rw [ho] at hi
  linarith only [hi,actual_sixth_ge_joint,RationalMovingSixth.rationalSixth_lower,
    SixthReciprocalCorrection.deltaSixth_lower,deltaLog_lower]

end Wu2008DoubleSieve.SixthLogCubicCorrection
