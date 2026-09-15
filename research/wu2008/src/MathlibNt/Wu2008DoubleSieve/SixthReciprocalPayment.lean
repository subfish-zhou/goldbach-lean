import MathlibNt.Wu2008DoubleSieve.SixthReciprocalKernel

namespace Wu2008DoubleSieve.SixthReciprocalCorrection
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence SharpMassBalance
open PositiveSixthFTC DynamicSixthEnvelope
open scoped Interval

noncomputable def e : ℝ := lam+b
noncomputable def rationalCorrection (x : ℝ) : ℝ :=
  (2/x)*(A0 x*lowerLog ((lam-x)/b)+polynomialPart x (lam-x)-polynomialPart x b)

/-- Only the correction uses the lower logarithm; the old negative logarithm is unchanged. -/
theorem rationalCorrection_lower {x : ℝ} (hx : x ∈ Icc a b) :
    rationalCorrection x ≤ movingCorrection x := by
  have hq : 1 ≤ (lam-x)/b := (le_div_iff₀ geometry.2.2.1).2 (by simpa using (moving_geometry hx).1)
  have hl := mul_le_mul_of_nonneg_left (log_lower hq) (moving_log_coefficient_nonneg hx)
  rw [movingCorrection_eq hx]
  unfold rationalCorrection
  nlinarith only [hl]

noncomputable def q0 : ℝ := -2472010863229095008/7660298574927723

noncomputable def q1 : ℝ := -8942033122816/18681695761

noncomputable def q2 : ℝ := -83865856/136681

noncomputable def q3 : ℝ := -14336/3

noncomputable def initialLogCoefficient : ℝ := 2470725199934989636947656103006421/2903238799818358346206658156999056

noncomputable def terminalLogCoefficient : ℝ := 277006899931687186858844723125/1648697250041516918743832464

noncomputable def poleTwo : ℝ := -31676226705541188766953125/2639842941709306097354414

noncomputable def poleThree : ℝ := 20294516456014510937500/50722016477314735983243

/-- Fixed long division, verified as an identity rather than trusted computation. -/
theorem partial_fractions {x : ℝ} (hx : x ≠ 0) (he : e-x ≠ 0) :
    rationalCorrection x = q0+q1*x+q2*x^2+q3*x^3+
      initialLogCoefficient/x+terminalLogCoefficient/(e-x)+poleTwo/(e-x)^2+poleThree/(e-x)^3 := by
  have hb : b ≠ 0 := geometry.2.2.1.ne'
  have heq : lam-x+b ≠ 0 := by intro h; apply he; dsimp [e]; linarith
  unfold rationalCorrection lowerLog polynomialPart A0 A1 A2 A3 d0 d1 d2
  field_simp [hx,hb,heq,he]
  norm_num [q0,q1,q2,q3,initialLogCoefficient,terminalLogCoefficient,poleTwo,poleThree,
    e,lam,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  ring

noncomputable def polynomialPrimitive (x : ℝ) : ℝ := q0*x+q1*x^2/2+q2*x^3/3+q3*x^4/4
noncomputable def outerPrimitive (x : ℝ) : ℝ :=
  polynomialPrimitive x+initialLogCoefficient*log x-terminalLogCoefficient*log (e-x)+
    poleTwo/(e-x)+poleThree/(2*(e-x)^2)

theorem outer_derivative {x : ℝ} (hx : x ≠ 0) (he : e-x ≠ 0) :
    HasDerivAt outerPrimitive (rationalCorrection x) x := by
  rw [partial_fractions hx he]
  have hi := hasDerivAt_id x
  have hd := (hasDerivAt_const x e).sub hi
  have hp := (((hi.const_mul q0).add (((hi.pow 2).const_mul q1).div_const 2)).add
    (((hi.pow 3).const_mul q2).div_const 3)).add (((hi.pow 4).const_mul q3).div_const 4)
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

theorem rationalCorrection_integrable : IntervalIntegrable rationalCorrection volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hn (x : ℝ) (hx : x ∈ uIcc a b) := denominators (uIcc_of_le geometry.2.1 ▸ hx)
  have hi : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc a b) := continuousOn_id.inv₀ (fun x hx => (hn x hx).1)
  have he : ContinuousOn (fun x : ℝ => (e-x)⁻¹) (uIcc a b) :=
    (continuousOn_const.sub continuousOn_id).inv₀ (fun x hx => (hn x hx).2)
  have hc : ContinuousOn (fun x : ℝ => q0+q1*x+q2*x^2+q3*x^3+
      initialLogCoefficient/x+terminalLogCoefficient/(e-x)+poleTwo/(e-x)^2+poleThree/(e-x)^3) (uIcc a b) := by
    simp only [div_eq_mul_inv,← inv_pow]
    fun_prop
  apply hc.congr
  intro x hx
  exact partial_fractions (hn x hx).1 (hn x hx).2

/-- The outer FTC is on the original interval, after the true moving inner FTC. -/
theorem outer_ftc : (∫ x in a..b, rationalCorrection x) = outerPrimitive b-outerPrimitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ rationalCorrection_integrable
  intro x hx
  have hd := denominators (uIcc_of_le geometry.2.1 ▸ hx)
  exact outer_derivative hd.1 hd.2

/-- Both final log coefficients are positive, independently of the old moving expression. -/
theorem endpoint_signL : 0 < initialLogCoefficient ∧ 0 < terminalLogCoefficient := by
  norm_num [initialLogCoefficient,terminalLogCoefficient]

noncomputable def rationalEndpointPart : ℝ := polynomialPrimitive b-polynomialPrimitive a+
  poleTwo*(1/(e-b)-1/(e-a))+(poleThree/2)*(1/(e-b)^2-1/(e-a)^2)

noncomputable def deltaSixth : ℝ := 4*(rationalEndpointPart+
  initialLogCoefficient*lowerLog (b/a)+terminalLogCoefficient*lowerLog ((e-a)/(e-b)))

theorem endpoint_exact : 4*(outerPrimitive b-outerPrimitive a) = 4*(rationalEndpointPart+
    initialLogCoefficient*log (b/a)+terminalLogCoefficient*log ((e-a)/(e-b))) := by
  have he1 : e-a ≠ 0 := (denominators (left_mem_Icc.mpr geometry.2.1)).2
  have he2 : e-b ≠ 0 := (denominators (right_mem_Icc.mpr geometry.2.1)).2
  rw [log_div geometry.2.2.1.ne' geometry.1.ne',log_div he1 he2]
  unfold outerPrimitive rationalEndpointPart
  field_simp [he1,he2]
  ring

theorem deltaSixth_lower : deltaSixth ≤ 4*(outerPrimitive b-outerPrimitive a) := by
  have hl := log_lower (t := b/a)
    (by norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have hr := log_lower (t := (e-a)/(e-b))
    (by norm_num [e,lam,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have h1 := mul_le_mul_of_nonneg_left hl endpoint_signL.1.le
  have h2 := mul_le_mul_of_nonneg_left hr endpoint_signL.2.le
  rw [endpoint_exact]
  unfold deltaSixth
  linarith only [h1,h2]

theorem deltaSixth_exact : deltaSixth = (1609168471475952604903444376820277244537532780965684646396726475412762/8973226984304932235772272497178442189932542751246851968056677532004417 : ℝ) := by
  norm_num [deltaSixth,rationalEndpointPart,polynomialPrimitive,q0,q1,q2,q3,
    initialLogCoefficient,terminalLogCoefficient,poleTwo,poleThree,e,lam,a,b,lowerLog,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem deltaSixth_pos : 0 < deltaSixth := by
  rw [deltaSixth_exact]
  norm_num

/-- One joint actual lower bound, never the sum of two separate bounds on the same actual term. -/
theorem actual_sixth_ge_rational_corrected :
    RationalMovingSixth.rationalSixth+deltaSixth ≤ truncatedSixthLowerF6lin := by
  have hi := intervalIntegral.integral_mono_on geometry.2.1
    (RationalMovingSixth.integrable.add rationalCorrection_integrable)
    (movingValue_integrable.add movingCorrection_integrable)
    (fun x hx => add_le_add (RationalMovingSixth.rationalMoving_lower hx) (rationalCorrection_lower hx))
  rw [intervalIntegral.integral_add RationalMovingSixth.integrable rationalCorrection_integrable,
    outer_ftc] at hi
  have ho : (∫ x in a..b, RationalMovingSixth.rationalMoving x) =
      RationalMovingSixth.outerPrimitive b-RationalMovingSixth.outerPrimitive a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ RationalMovingSixth.integrable
    intro x hx
    have hd := RationalMovingSixth.denominators (uIcc_of_le geometry.2.1 ▸ hx)
    exact RationalMovingSixth.derivative hd.1 hd.2.1 hd.2.2
  rw [ho] at hi
  linarith only [hi,actual_sixth_ge_joint,RationalMovingSixth.rationalSixth_lower,deltaSixth_lower]

end Wu2008DoubleSieve.SixthReciprocalCorrection
