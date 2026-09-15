import MathlibNt.Wu2008DoubleSieve.DynamicSixthEnvelope

namespace Wu2008DoubleSieve.RationalMovingSixth
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence SharpMassBalance
open PositiveSixthFTC DynamicSixthEnvelope
open scoped Interval

noncomputable def e : ℝ := lam+b
noncomputable def quadraticCoefficient : ℝ := 1/(3*b)
noncomputable def linearCoefficient : ℝ := 1/3-(8*m+8*e+1)/(24*b)
noncomputable def constantCoefficient : ℝ :=
  -(m-1/12)-m/3+(m*(8*e+1)+e)/(24*b)-8*b/3
noncomputable def initialLogCoefficient : ℝ := m*(m-1/12)-m*e/(24*b)+b*m/(3*e)
noncomputable def terminalLogCoefficient : ℝ := -b/3*(1-16*b-m/e)

noncomputable def rationalMoving (x : ℝ) : ℝ :=
  128*((m-x)*((m+1/4)/x-3)+(lam-x)*(2-1/(4*x))*upperLog ((lam-x)/b))

 theorem movingValue_eq {x : ℝ} (hx : x ∈ Icc a b) :
    movingValue x =
      128*((m-x)*((m+1/4)/x-3)+(lam-x)*(2-1/(4*x))*log ((lam-x)/b)) := by
  have hq := geometry.2.2.1.trans_le (moving_geometry hx).1
  rw [log_div hq.ne' geometry.2.2.1.ne']
  unfold movingValue innerPrimitive m
  field_simp [(geometry.1.trans_le hx.1).ne']
  ring

 theorem rationalMoving_lower {x : ℝ} (hx : x ∈ Icc a b) :
    rationalMoving x ≤ movingValue x := by
  have hq : 1 ≤ (lam-x)/b := (le_div_iff₀ geometry.2.2.1).2 (by
    simpa using (moving_geometry hx).1)
  have hl := mul_le_mul_of_nonpos_left (log_upper hq) (moving_log_coefficient_nonpos hx)
  rw [movingValue_eq hx]
  unfold rationalMoving
  nlinarith

 theorem partial_fractions {x : ℝ} (hx : x ≠ 0) (hq : lam-x ≠ 0) (he : e-x ≠ 0) :
    rationalMoving x = 128*(quadraticCoefficient*x^2+linearCoefficient*x+
      constantCoefficient+initialLogCoefficient/x+terminalLogCoefficient/(e-x)) := by
  have hb : b ≠ 0 := geometry.2.2.1.ne'
  have he0 : e ≠ 0 := by norm_num [e,lam,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hel : lam+b-x ≠ 0 := he
  have heq : lam-x+b ≠ 0 := by intro h; apply hel; linarith
  unfold rationalMoving quadraticCoefficient linearCoefficient constantCoefficient
    initialLogCoefficient terminalLogCoefficient upperLog
  dsimp [e,m] at he0 ⊢
  field_simp [hx,hq,hb,he0,hel,heq]
  ring

noncomputable def outerPrimitive (x : ℝ) : ℝ := 128*(
  quadraticCoefficient*x^3/3+linearCoefficient*x^2/2+constantCoefficient*x+
    initialLogCoefficient*log x-terminalLogCoefficient*log (e-x))

 theorem derivative {x : ℝ} (hx : x ≠ 0) (hq : lam-x ≠ 0) (he : e-x ≠ 0) :
    HasDerivAt outerPrimitive (rationalMoving x) x := by
  rw [partial_fractions hx hq he]
  have h := ((((((((hasDerivAt_id x).pow 3).const_mul quadraticCoefficient).div_const 3).add
    ((((hasDerivAt_id x).pow 2).const_mul linearCoefficient).div_const 2)).add
    ((hasDerivAt_id x).const_mul constantCoefficient)).add
    ((hasDerivAt_log hx).const_mul initialLogCoefficient)).sub
    ((((hasDerivAt_const x e).sub (hasDerivAt_id x)).log he).const_mul terminalLogCoefficient)).const_mul 128
  convert h using 1 <;> first | rfl | (dsimp; field_simp; ring)

 theorem denominators {x : ℝ} (hx : x ∈ Icc a b) :
    x ≠ 0 ∧ lam-x ≠ 0 ∧ e-x ≠ 0 := by
  have hq := geometry.2.2.1.trans_le (moving_geometry hx).1
  refine ⟨(geometry.1.trans_le hx.1).ne',hq.ne',?_⟩
  have hb := geometry.2.2.1
  dsimp [e]
  linarith

 theorem integrable : IntervalIntegrable rationalMoving volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hx0 (x : ℝ) (hx : x ∈ uIcc a b) := denominators (uIcc_of_le geometry.2.1 ▸ hx)
  have hi : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc a b) :=
    continuousOn_id.inv₀ (fun x hx => (hx0 x hx).1)
  have he : ContinuousOn (fun x : ℝ => (e-x)⁻¹) (uIcc a b) :=
    (continuousOn_const.sub continuousOn_id).inv₀ (fun x hx => (hx0 x hx).2.2)
  have hc : ContinuousOn (fun x => 128*(quadraticCoefficient*x^2+linearCoefficient*x+
      constantCoefficient+initialLogCoefficient/x+terminalLogCoefficient/(e-x))) (uIcc a b) := by
    simp only [div_eq_mul_inv]
    fun_prop
  apply hc.congr
  intro x hx
  exact partial_fractions (hx0 x hx).1 (hx0 x hx).2.1 (hx0 x hx).2.2

 theorem full_mask_rational_ftc :
    4*(outerPrimitive b-outerPrimitive a) ≤ truncatedSixthLowerF6lin := by
  have hi := intervalIntegral.integral_mono_on geometry.2.1 integrable movingValue_integrable
    (fun x hx => rationalMoving_lower hx)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt _ integrable] at hi
  · linarith [actual_sixth_ge_moving]
  · intro x hx
    have hd := denominators (uIcc_of_le geometry.2.1 ▸ hx)
    exact derivative hd.1 hd.2.1 hd.2.2

noncomputable def rationalSixth : ℝ := 512*(
  quadraticCoefficient*(b^3-a^3)/3+linearCoefficient*(b^2-a^2)/2+constantCoefficient*(b-a)+
    initialLogCoefficient*lowerLog (b/a)+terminalLogCoefficient*lowerLog ((e-a)/(e-b)))

 theorem rationalSixth_lower : rationalSixth ≤ 4*(outerPrimitive b-outerPrimitive a) := by
  have he1 : e-b ≠ 0 := by norm_num [e,lam,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have he2 : e-a ≠ 0 := by norm_num [e,lam,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have h1 := log_lower (t := b/a)
    (by norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have h2 := log_lower (t := (e-a)/(e-b))
    (by norm_num [e,lam,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  rw [log_div geometry.2.2.1.ne' geometry.1.ne'] at h1
  rw [log_div he2 he1] at h2
  unfold rationalSixth outerPrimitive
  norm_num [quadraticCoefficient,linearCoefficient,constantCoefficient,
    initialLogCoefficient,terminalLogCoefficient,e,m,lam,a,b,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta] at h1 h2 ⊢
  linarith

 theorem actual_sixth_ge_rational : rationalSixth ≤ truncatedSixthLowerF6lin :=
  rationalSixth_lower.trans full_mask_rational_ftc

noncomputable def balance : ℝ :=
  54035471/1012500+3/2+rationalSixth+47/481250-VariableCoefficientBalance.rationalG-12-21/20

 theorem complete_coefficient_gt_balance :
    balance < TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have hb := SharpSingleBalance.base_sharp_lower
  have hg := VariableCoefficientBalance.full_G_rational
  have hj := SharpJBalance.weighted_J_lt_twelve
  have h4 := SharpMassBalance.four_weighted_lt_21_twentieths
  have hp := SharpMassBalance.fifth_gt_three_halves
  have hq := actual_sixth_ge_rational
  change SingleUpperClassicalLimit.Glin (1/3)+
    SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma ≤ VariableCoefficientBalance.rationalG at hg
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient balance
  linarith

 theorem sixth_recovers_one_fifth :
    PositiveClassicalCoefficient.rectangleBound+1/5 < rationalSixth := by
  norm_num [rationalSixth,quadraticCoefficient,linearCoefficient,constantCoefficient,
    initialLogCoefficient,terminalLogCoefficient,e,m,lam,a,b,lowerLog,upperLog,
    PositiveClassicalCoefficient.rectangleBound,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

 theorem balance_gt_three_halves : (3/2 : ℝ) < balance := by
  norm_num [balance,rationalSixth,quadraticCoefficient,linearCoefficient,constantCoefficient,
    initialLogCoefficient,terminalLogCoefficient,e,m,lam,a,b,lowerLog,upperLog,
    VariableCoefficientBalance.rationalG,VariableGIntegral.logCoefficient,
    VariableGIntegral.linearCoefficient,VariableGIntegral.a,VariableGIntegral.s,VariableGIntegral.c,
    SharpSingleBalance.c,SharpSingleBalance.a,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma]

 theorem complete_coefficient_gt_three_halves :
    (3/2 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient :=
  balance_gt_three_halves.trans complete_coefficient_gt_balance

/-- A substantive improvement over the inherited exact rectangle balance, not decimal rounding. -/
 theorem exact_balance_improvement :
    (54035471/1012500+3/2+PositiveClassicalCoefficient.rectangleBound+47/481250-
      179/4-12-21/20)+6/5 < balance := by
  have hg := VariableCoefficientBalance.G_payment_saves_one
  have hs := sixth_recovers_one_fifth
  unfold balance
  linarith

 theorem lower_envelope_below_benchmark : balance < (899/250 : ℝ) := by
  norm_num [balance,rationalSixth,quadraticCoefficient,linearCoefficient,constantCoefficient,
    initialLogCoefficient,terminalLogCoefficient,e,m,lam,a,b,lowerLog,upperLog,
    VariableCoefficientBalance.rationalG,VariableGIntegral.logCoefficient,
    VariableGIntegral.linearCoefficient,VariableGIntegral.a,VariableGIntegral.s,VariableGIntegral.c,
    SharpSingleBalance.c,SharpSingleBalance.a,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma]

 theorem literal_coefficient_gt_three_halves :
    (3/2 : ℝ) <
      24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha))+
      8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))+fifthPairFlin+
      truncatedSixthLowerF6lin+47/481250-
      SingleUpperClassicalLimit.Glin (1/3)-
      SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma-8*J9-
      16*SeventhEighth.J7-8*SeventhEighth.J8-
      8*FourRoughClosedMass.I10-8*FourRoughClosedMass.I11 :=
  complete_coefficient_gt_three_halves

end Wu2008DoubleSieve.RationalMovingSixth
