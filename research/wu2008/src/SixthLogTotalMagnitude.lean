import ClassicalLossBottleneck
import PsiG18Strength

namespace Wu2008DoubleSieve.SixthLogTotalMagnitude
open Real Set MeasureTheory SharpLogRecurrence JointLogTotalComparison TotalEndpointComparison
open ClassicalLossBottleneck ClassicalAnalyticLeaves SharpMassBalance
open PositiveSixthFTC DynamicSixthEnvelope
open scoped Interval
noncomputable section

theorem lower_gap_monotone : MonotoneOn (fun t => log t-lowerLog t) (Ici 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
    (fun x hx => (lower_gap_derivative hx).continuousAt.continuousWithinAt)
    (fun x hx => (lower_gap_derivative (interior_subset hx)).hasDerivWithinAt)
  intro x hx
  have hx1 : 1 ≤ x := interior_subset hx
  exact div_nonneg (by positivity) (by positivity)

theorem original_gap_factor {t : ℝ} (ht : 1 ≤ t) :
    upperLog t-lowerLog t = (t-1)/6*((t-1)/t)*((t-1)/(t+1))^3 := by
  have h0 : t ≠ 0 := by linarith
  have h1 : t+1 ≠ 0 := by linarith
  unfold upperLog lowerLog
  field_simp
  ring

theorem original_gap_linear {t m : ℝ} (ht : 1 ≤ t) (hm : 1 < m) (htm : t ≤ m) :
    log t-lowerLog t ≤ (3/5)*(upperLog m-lowerLog m)/(m-1)*(t-1) := by
  have ht0 : 0 < t := by linarith
  have hm0 : 0 < m := by linarith
  have h1 : (t-1)/t ≤ (m-1)/m := by
    apply (div_le_div_iff₀ ht0 hm0).2
    nlinarith only [htm]
  have h2 : (t-1)/(t+1) ≤ (m-1)/(m+1) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).2
    nlinarith only [htm]
  have hp := mul_le_mul h1 (pow_le_pow_left₀ (by positivity) h2 3)
    (by positivity : 0 ≤ ((t-1)/(t+1))^3) (by positivity : 0 ≤ (m-1)/m)
  have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ (t-1)/6 by positivity)
  have hg : upperLog t-lowerLog t ≤ (upperLog m-lowerLog m)/(m-1)*(t-1) := by
    rw [original_gap_factor ht,original_gap_factor hm.le]
    calc
      _ = (t-1)/6*((t-1)/t*((t-1)/(t+1))^3) := by ring
      _ ≤ (t-1)/6*((m-1)/m*((m-1)/(m+1))^3) := hmul
      _ = _ := by field_simp [show m-1 ≠ 0 by linarith]
  have h := log_le_V ht
  unfold V at h
  calc
    _ ≤ (3/5)*(upperLog t-lowerLog t) := by linarith only [h]
    _ ≤ (3/5)*((upperLog m-lowerLog m)/(m-1)*(t-1)) :=
      mul_le_mul_of_nonneg_left hg (by norm_num)
    _ = _ := by ring

theorem target_slack_bounds : 0 ≤ targetSlack ∧ targetSlack < 1/100000 := by
  have h := log_lower (by norm_num : (1:ℝ) ≤ 5000/4469)
  refine ⟨targetSlack_nonnegative,?_⟩
  unfold targetSlack V
  norm_num [upperLog,lowerLog] at h ⊢
  linarith only [h]

theorem log_remainder_cap : 0 ≤ logRemainder ∧ logRemainder < 1/20 := by
  have e0 : log 2-lowerLog 2 ≤ (3/5)*(upperLog 2-lowerLog 2) := by
    have h := log_le_V (show 1 ≤ 2 by fixed_num)
    unfold V at h
    linarith only [h]
  have h0 := mul_le_mul_of_nonneg_left e0 (show 0 ≤ c2 by fixed_num)
  have e1 : V (4/3)-log (4/3) ≤ (3/5)*(upperLog (4/3)-lowerLog (4/3)) := by
    have h := log_lower (show 1 ≤ (4/3) by fixed_num)
    unfold V
    linarith only [h]
  have h1 := mul_le_mul_of_nonneg_left e1 (show 0 ≤ c43 by fixed_num)
  have e2 : log (5/4)-lowerLog (5/4) ≤ (3/5)*(upperLog (5/4)-lowerLog (5/4)) := by
    have h := log_le_V (show 1 ≤ (5/4) by fixed_num)
    unfold V at h
    linarith only [h]
  have h2 := mul_le_mul_of_nonneg_left e2 (show 0 ≤ c54 by fixed_num)
  have e3 : V rH-log rH ≤ (3/5)*(upperLog rH-lowerLog rH) := by
    have h := log_lower (show 1 ≤ rH by fixed_num)
    unfold V
    linarith only [h]
  have h3 := mul_le_mul_of_nonneg_left e3 (show 0 ≤ cH by fixed_num)
  have e4 : log (FixedCoefficientUpperEnclosure.b/FixedCoefficientUpperEnclosure.a)-lowerLog (FixedCoefficientUpperEnclosure.b/FixedCoefficientUpperEnclosure.a) ≤ (3/5)*(upperLog (FixedCoefficientUpperEnclosure.b/FixedCoefficientUpperEnclosure.a)-lowerLog (FixedCoefficientUpperEnclosure.b/FixedCoefficientUpperEnclosure.a)) := by
    have h := log_le_V (show 1 ≤ (FixedCoefficientUpperEnclosure.b/FixedCoefficientUpperEnclosure.a) by fixed_num)
    unfold V at h
    linarith only [h]
  have h4 := mul_le_mul_of_nonneg_left e4 (show 0 ≤ cD by fixed_num)
  have e5 : log Phase25.ratioz-lowerLog Phase25.ratioz ≤ (3/5)*(upperLog Phase25.ratioz-lowerLog Phase25.ratioz) := by
    have h := log_le_V (show 1 ≤ Phase25.ratioz by fixed_num)
    unfold V at h
    linarith only [h]
  have h5 := mul_le_mul_of_nonneg_left e5 (show 0 ≤ Phase25.kx by fixed_num)
  have e6 : log (Phase25.ratiob/Phase25.ratioz)-lowerLog (Phase25.ratiob/Phase25.ratioz) ≤ (3/5)*(upperLog (Phase25.ratiob/Phase25.ratioz)-lowerLog (Phase25.ratiob/Phase25.ratioz)) := by
    have h := log_le_V (show 1 ≤ (Phase25.ratiob/Phase25.ratioz) by fixed_num)
    unfold V at h
    linarith only [h]
  have h6 := mul_le_mul_of_nonneg_left e6 (show 0 ≤ Phase25.qb1 by fixed_num)
  have e7 : V (Phase25.ratioz/Phase25.ratiom)-log (Phase25.ratioz/Phase25.ratiom) ≤ (3/5)*(upperLog (Phase25.ratioz/Phase25.ratiom)-lowerLog (Phase25.ratioz/Phase25.ratiom)) := by
    have h := log_lower (show 1 ≤ (Phase25.ratioz/Phase25.ratiom) by fixed_num)
    unfold V
    linarith only [h]
  have h7 := mul_le_mul_of_nonneg_left e7 (show 0 ≤ Phase25.qm1 by fixed_num)
  have e8 : log (Phase25.ratiop/Phase25.ratioz)-lowerLog (Phase25.ratiop/Phase25.ratioz) ≤ (3/5)*(upperLog (Phase25.ratiop/Phase25.ratioz)-lowerLog (Phase25.ratiop/Phase25.ratioz)) := by
    have h := log_le_V (show 1 ≤ (Phase25.ratiop/Phase25.ratioz) by fixed_num)
    unfold V at h
    linarith only [h]
  have h8 := mul_le_mul_of_nonneg_left e8 (show 0 ≤ Phase25.qp1 by fixed_num)
  have he := logRemainder_expansion
  refine ⟨logRemainder_nonnegative,?_⟩
  norm_num [c2,c43,c54,cH,cD,rH,A1,H,gap,quad,lin,
  FifthClassicalShape.ell,FifthClassicalShape.k,FifthClassicalShape.c,FifthClassicalShape.f,
  FifthClassicalShape.q,SharpMassBalance.s0,SharpMassBalance.fifthDensity,
  SharpMassBalance.a,SharpMassBalance.b,lowerLog,upperLog,V,
  SignedTotalCorrelation.jTwo,SharpJBalance.ninthA,SharpJBalance.s,
  SeventhEighth.sigma,SeventhEighth.alpha,GConvexChord.C,GConvexChord.r4,GConvexChord.r5,
  Phase25.ratioz,Phase25.ratiob,Phase25.ratiom,Phase25.ratiop,
  Phase25.polez,Phase25.poleb,Phase25.polem,Phase25.polep,
  Phase25.kx,Phase25.qb1,Phase25.qm1,Phase25.qp1,
  a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  norm_num [c2,c43,c54,cH,cD,rH,A1,H,gap,quad,lin,
  FifthClassicalShape.ell,FifthClassicalShape.k,FifthClassicalShape.c,FifthClassicalShape.f,
  FifthClassicalShape.q,SharpMassBalance.s0,SharpMassBalance.fifthDensity,
  SharpMassBalance.a,SharpMassBalance.b,lowerLog,upperLog,V,
  SignedTotalCorrelation.jTwo,SharpJBalance.ninthA,SharpJBalance.s,
  SeventhEighth.sigma,SeventhEighth.alpha,GConvexChord.C,GConvexChord.r4,GConvexChord.r5,
  Phase25.ratioz,Phase25.ratiob,Phase25.ratiom,Phase25.ratiop,
  Phase25.polez,Phase25.poleb,Phase25.polem,Phase25.polep,
  Phase25.kx,Phase25.qb1,Phase25.qm1,Phase25.qp1,
  a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma] at he
  linarith only [he,h0,h1,h2,h3,h4,h5,h6,h7,h8]

theorem jextra_bounds : 0 ≤ (JointJLossStrength.recovery-JointJLossStrength.fixedRecovery)/4 ∧
    (JointJLossStrength.recovery-JointJLossStrength.fixedRecovery)/4 < 1/100 := by
  have hgap := log_lower (show 1 ≤ (1-2*SharpJBalance.s)/SharpJBalance.s by
    norm_num [SharpJBalance.s,SeventhEighth.sigma,SeventhEighth.alpha])
  have h1 := log_upper (show 1 ≤ SharpJBalance.s/SharpJBalance.b by
    norm_num [SharpJBalance.s,SharpJBalance.b,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have h2 := log_upper (show 1 ≤ (1-SharpJBalance.b)/(1-SharpJBalance.s) by
    norm_num [SharpJBalance.s,SharpJBalance.b,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have hg : JointJLossStrength.gap ≤ upperLog ((1-2*SharpJBalance.s)/SharpJBalance.s)-
      lowerLog ((1-2*SharpJBalance.s)/SharpJBalance.s) := by
    unfold JointJLossStrength.gap
    linarith only [hgap]
  have hm : JointJLossStrength.mass ≤ upperLog (SharpJBalance.s/SharpJBalance.b)+
      upperLog ((1-SharpJBalance.b)/(1-SharpJBalance.s)) := by
    unfold JointJLossStrength.mass
    linarith only [h1,h2]
  have hp := mul_le_mul hg hm (show 0 ≤ JointJLossStrength.mass by
    unfold JointJLossStrength.mass
    apply add_nonneg <;> apply log_nonneg <;>
      norm_num [SharpJBalance.s,SharpJBalance.b,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
    (show 0 ≤ upperLog ((1-2*SharpJBalance.s)/SharpJBalance.s)-
      lowerLog ((1-2*SharpJBalance.s)/SharpJBalance.s) by
      norm_num [upperLog,lowerLog,SharpJBalance.s,SeventhEighth.sigma,SeventhEighth.alpha])
  refine ⟨by linarith only [JointJLossStrength.fixedRecovery_le_recovery],?_⟩
  unfold JointJLossStrength.recovery JointJLossStrength.fixedRecovery
  norm_num [JointJLossStrength.massPayment,upperLog,lowerLog,SharpJBalance.s,SharpJBalance.b,
    SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2] at hp ⊢
  linarith only [hp]

theorem square_bounds : 0 ≤ quad/4*(D-FifthClassicalShape.ell)^2 ∧
    quad/4*(D-FifthClassicalShape.ell)^2 < 1/100000 := by
  have hl := log_lower (show 1 ≤ FixedCoefficientUpperEnclosure.b/FixedCoefficientUpperEnclosure.a by fixed_num)
  have hu := log_upper (show 1 ≤ FixedCoefficientUpperEnclosure.b/FixedCoefficientUpperEnclosure.a by fixed_num)
  have hq : 0 ≤ quad := by fixed_num
  have hbounds : 0 ≤ D-FifthClassicalShape.ell ∧ D-FifthClassicalShape.ell ≤
      upperLog (FixedCoefficientUpperEnclosure.b/FixedCoefficientUpperEnclosure.a)-
      lowerLog (FixedCoefficientUpperEnclosure.b/FixedCoefficientUpperEnclosure.a) := by
    unfold D FifthClassicalShape.ell
    exact ⟨sub_nonneg.mpr hl,sub_le_sub_right hu _⟩
  have hp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hbounds.1 hbounds.2 2) (show 0 ≤ quad/4 by positivity)
  refine ⟨by positivity,?_⟩
  norm_num [quad,FifthClassicalShape.k,FifthClassicalShape.c,FifthClassicalShape.f,
    FifthClassicalShape.q,SharpMassBalance.s0,SharpMassBalance.fifthDensity,
    a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,upperLog,lowerLog] at hp ⊢
  linarith only [hp]

/-- Constants at the existing geometric endpoints, not new cut points. -/
def firstCap : ℝ := ((3/5)*(upperLog (31153/10300)-lowerLog (31153/10300))/(31153/10300-1))/
  a/(2*a^2*b)
def secondCap : ℝ := ((8/3)/(1/2-b))/a*((3/5)*(upperLog (41453/20600)-lowerLog (41453/20600))+
  (3/5)*(upperLog (74881/33175)-lowerLog (74881/33175)))

theorem firstCap_nonnegative : 0 ≤ firstCap := by
  norm_num [firstCap,upperLog,lowerLog,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem first_layer_pointwise {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b (lam-x)) :
    sixthLogRegular x y ≤ Phase25.exactKernel x y+firstCap*(s-y) := by
  have hg := Phase25.mask_geometry hx hy
  have ha := geometry.1
  have hb := geometry.2.2.1
  have hyS := hy.2.trans (moving_geometry hx).2
  have hs2 : 2 ≤ truncatedSixthLowerS 0 x y := by
    apply (le_div_iff₀ ha).2
    dsimp [truncatedSixthLowerC]
    simpa only [sub_zero] using hg.2.2.2.2
  have hsm := sixth_parameter_cap hx ⟨hy.1,hyS⟩
  have h := original_gap_linear (t := truncatedSixthLowerS 0 x y-1)
    (by linarith) (by norm_num : (1:ℝ) < 31153/10300) (by linarith)
  have hlin : truncatedSixthLowerS 0 x y-1-1 ≤ (s-y)/a := by
    apply (le_div_iff₀ ha).2
    have he : (truncatedSixthLowerS 0 x y-1-1)*a = 1/2-x-y-2*a := by
      unfold truncatedSixthLowerS truncatedSixthLowerC
      field_simp
      ring
    rw [he]
    have hxa := hx.1
    norm_num [s,a,truncatedSixthLowerSigma,truncatedSixthLowerAlpha] at hxa ⊢
    linarith
  have hlinmul := mul_le_mul_of_nonneg_left hlin
    (show 0 ≤ (3/5)*(upperLog (31153/10300)-lowerLog (31153/10300))/(31153/10300-1) by
      norm_num [upperLog,lowerLog])
  have hden : 2*a^2*b ≤ x*y*(1/2-x-y) := by
    have hxy := mul_le_mul hx.1 hy.1 hb.le hg.1.le
    have hp := mul_le_mul hxy hg.2.2.2.2 (by positivity : 0 ≤ 2*a) (mul_nonneg hg.1.le hg.2.1.le)
    nlinarith only [hp]
  have he : Phase25.exactKernel x y = lowerLog (truncatedSixthLowerS 0 x y-1)/(x*y*(1/2-x-y)) := by
    have hz' : 1-x*2-y*2 ≠ 0 := by linarith [hg.2.2.2.1]
    simp only [Phase25.exactKernel,lowerLog,truncatedSixthLowerS,truncatedSixthLowerC,lam,sub_zero]
    field_simp [ha.ne',hg.1.ne',hg.2.1.ne',hg.2.2.2.1.ne',hz']
    ring
  rw [sixth_log_retained hx hy,he]
  have hnum := h.trans hlinmul
  have hdiv := div_le_div_of_nonneg_right hnum
    (mul_pos (mul_pos hg.1 hg.2.1) hg.2.2.2.1).le
  have hdiv2 := div_le_div_of_nonneg_left
    (show 0 ≤ ((3/5)*(upperLog (31153/10300)-lowerLog (31153/10300))/(31153/10300-1))*((s-y)/a) by
      apply mul_nonneg
      · norm_num [upperLog,lowerLog]
      · exact div_nonneg (sub_nonneg.mpr hyS) ha.le)
    (show 0 < 2*a^2*b by positivity) hden
  rw [sub_div] at hdiv
  have he2 : ((3/5)*(upperLog (31153/10300)-lowerLog (31153/10300))/(31153/10300-1))*((s-y)/a)/(2*a^2*b) =
      firstCap*(s-y) := by unfold firstCap; ring
  rw [he2] at hdiv2
  linarith only [hdiv,hdiv2]

theorem S_upper {c h : ℝ} (hc : 0 < c) (hh : 0 ≤ h) (hhc : h ≤ c) : Phase25.S c h ≤ (8/3)/c := by
  have he : Phase25.S c h = (8/3)/c-
      (2*h/c^2+2*h*(c-h)/c^3+(2/3)*h^3/c^4) := by
    unfold Phase25.S
    field_simp
    ring
  rw [he]
  have hn : 0 ≤ 2*h/c^2+2*h*(c-h)/c^3+(2/3)*h^3/c^4 := by positivity
  linarith only [hn]

theorem second_layer_pointwise {x : ℝ} (hx : x ∈ Icc a b) :
    Phase25.movingExact x ≤ Phase25.rationalInner (1/2-x)+secondCap := by
  have hg := Phase25.outer_geometry hx
  have ha := geometry.1
  have hb := geometry.2.2.1
  have h1 : 1 ≤ (1/2-x-b)/(2*a) := (le_div_iff₀ (by positivity)).2 (by linarith [hg.2.2.2.2])
  have h2 : 1 ≤ (1/2-x-2*a)/b := (le_div_iff₀ hb).2 (by linarith [hg.2.2.2.2])
  have hu1 : (1/2-x-b)/(2*a) ≤ 41453/20600 := by
    apply (div_le_iff₀ (by positivity)).2
    have hh := hx.1
    norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta] at hh ⊢
    linarith
  have hu2 : (1/2-x-2*a)/b ≤ 74881/33175 := by
    apply (div_le_iff₀ hb).2
    have hh := hx.1
    norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta] at hh ⊢
    linarith
  have he1 := lower_gap_monotone h1 (show (1:ℝ) ≤ 41453/20600 by norm_num) hu1
  have he2 := lower_gap_monotone h2 (show (1:ℝ) ≤ 74881/33175 by norm_num) hu2
  have hu1' := log_le_V (by norm_num : (1:ℝ) ≤ 41453/20600)
  have hu2' := log_le_V (by norm_num : (1:ℝ) ≤ 74881/33175)
  have herr : (log ((1/2-x-b)/(2*a))-lowerLog ((1/2-x-b)/(2*a)))+
      (log ((1/2-x-2*a)/b)-lowerLog ((1/2-x-2*a)/b)) ≤
      (3/5)*(upperLog (41453/20600)-lowerLog (41453/20600))+
      (3/5)*(upperLog (74881/33175)-lowerLog (74881/33175)) := by
    unfold V at hu1' hu2'
    linarith only [he1,he2,hu1',hu2']
  have hs := Phase25.S_pos (h := 2*a) hg.2.1 (by linarith [hg.2.2.2.1])
  have hsup := S_upper hg.2.1 (show 0 ≤ 2*a by positivity) (by linarith [hg.2.2.2.1])
  have hc : 0 < (1/2:ℝ)-b := by norm_num [b,truncatedSixthLowerBeta]
  have hcap := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 8/3) hc (show 1/2-b ≤ 1/2-x by linarith [hx.2])
  have hcoef : Phase25.S (1/2-x) (2*a)/x ≤ ((8/3)/(1/2-b))/a :=
    (div_le_div_of_nonneg_right (hsup.trans hcap) hg.1.le).trans
      (div_le_div_of_nonneg_left (by positivity) ha hx.1)
  have hp := mul_le_mul hcoef herr
    (show 0 ≤ (log ((1/2-x-b)/(2*a))-lowerLog ((1/2-x-b)/(2*a)))+
      (log ((1/2-x-2*a)/b)-lowerLog ((1/2-x-2*a)/b)) from
      add_nonneg (sub_nonneg.mpr (log_lower h1)) (sub_nonneg.mpr (log_lower h2)))
    (by positivity : 0 ≤ ((8/3)/(1/2-b))/a)
  rw [Phase25.movingExact_endpoint,Phase25.endpoint_difference hg.2.2.1 hg.2.2.2.1]
  unfold Phase25.rationalInner secondCap
  rw [show (1/2:ℝ)-(1/2-x)=x by ring]
  ring_nf at hp ⊢
  linarith only [hp]

/-- The full original log integral, with both old envelope losses bounded. -/
theorem sixth_log_inner_cap {x : ℝ} (hx : x ∈ Icc a b) :
    (∫ y in b..s, sixthLogRegular x y) ≤
      Phase25.rationalInner (1/2-x)+secondCap+firstCap*(s-b)^2/2 := by
  have hc := sixth_log_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
  have hp : Continuous (fun y : ℝ => firstCap*(s-y)) := by fun_prop
  have he : (∫ y in b..(lam-x), firstCap*(s-y)) =
      firstCap*((s-b)^2-(s-(lam-x))^2)/2 := by
    have hd (y : ℝ) : HasDerivAt (fun y : ℝ => -firstCap*(s-y)^2/2) (firstCap*(s-y)) y := by
      convert (((((hasDerivAt_const y s).sub (hasDerivAt_id y)).pow 2).const_mul (-firstCap)).div_const 2) using 1 <;>
        first | rfl | (dsimp; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) (hp.intervalIntegrable b (lam-x))]
    ring
  have hi := intervalIntegral.integral_mono_on (μ := volume) (moving_geometry hx).1
    (hc.intervalIntegrable b (lam-x)) ((Phase25.inner_integrable hx).add (hp.intervalIntegrable b (lam-x)))
    (fun y hy => first_layer_pointwise hx hy)
  rw [intervalIntegral.integral_add (Phase25.inner_integrable hx) (hp.intervalIntegrable b (lam-x)),
    Phase25.inner_ftc hx,he] at hi
  have hcomp : (∫ y in (lam-x)..s, sixthLogRegular x y) = 0 := by
    calc
      _ = ∫ _y in (lam-x)..s, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        have hy' : y ∈ Icc (lam-x) s := uIcc_of_le (moving_geometry hx).2 ▸ hy
        have hh := sixth_log_pointwise hx ⟨(moving_geometry hx).1.trans hy'.1,hy'.2⟩
        rw [sixth_complement_zero hx hy'] at hh
        have hn := sixth_log_nonnegative x y
        linarith only [hh.1,hn]
      _ = 0 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable b (lam-x)) (hc.intervalIntegrable (lam-x) s)
  simp only [Function.comp_apply] at hi hadd
  rw [hcomp,add_zero] at hadd
  rw [← hadd]
  have hnon := mul_nonneg firstCap_nonnegative (sq_nonneg (s-(lam-x)))
  linarith only [hi,hnon,second_layer_pointwise hx]

/-- A strict bound on the actual entire two-layer log-envelope loss, not a lower certificate. -/
theorem sixth_loss_bounds : 0 ≤ sixthLogIntegral-AnalyticTotalThreshold.sixthEndpoint ∧
    sixthLogIntegral-AnalyticTotalThreshold.sixthEndpoint < 7/25 := by
  have hc : Continuous (fun x : ℝ => ∫ y in b..s, sixthLogRegular x y) := by
    apply gamma5Gain_moving_integral (f := sixthLogRegular) sixth_log_continuous <;> fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) geometry.2.1
    (hc.intervalIntegrable a b)
    ((Phase25.rationalInner_integrable.add intervalIntegrable_const).add intervalIntegrable_const)
    (fun x hx => sixth_log_inner_cap hx)
  rw [intervalIntegral.integral_add
    (Phase25.rationalInner_integrable.add intervalIntegrable_const) intervalIntegrable_const,
    intervalIntegral.integral_add Phase25.rationalInner_integrable intervalIntegrable_const,
    Phase25.outer_ftc] at hi
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hi
  have hcap : 4*(b-a)*(secondCap+firstCap*(s-b)^2/2) < (7/25:ℝ) := by
    norm_num [firstCap,secondCap,upperLog,lowerLog,a,b,s,truncatedSixthLowerAlpha,
      truncatedSixthLowerBeta,truncatedSixthLowerSigma]
  refine ⟨sub_nonneg.mpr sixth_endpoint_le_logIntegral,?_⟩
  unfold sixthLogIntegral AnalyticTotalThreshold.sixthEndpoint
  linarith only [hi,hcap]

/-- Every signed term is retained in the exact difference for the latest certificate. -/
theorem recovered_exact_difference : AnalyticTotalThreshold.target-recoveredCoefficient =
    rationalDeficit-Phase18.g18-Phase20.psiPaymentLoss-logRemainder-
    (JointJLossStrength.recovery-JointJLossStrength.fixedRecovery)/4-targetSlack-
    quad/4*(D-FifthClassicalShape.ell)^2-(sixthLogIntegral-AnalyticTotalThreshold.sixthEndpoint)/4 := by
  have h := exact_target_full_coefficient_difference
  unfold recoveredCoefficient
  linarith only [h]

/-- Two-sided quantitative distance from the original logarithmic target. -/
theorem recovered_deficit_bounds : (1/250:ℝ) < AnalyticTotalThreshold.target-recoveredCoefficient ∧
    AnalyticTotalThreshold.target-recoveredCoefficient < 3/20 := by
  have hD : (7/50:ℝ) < rationalDeficit ∧ rationalDeficit < 3/20 := by norm_num [rationalDeficit]
  have hP := PsiG18Strength.two_recoveries_bounds
  have hL := log_remainder_cap
  have hJ := jextra_bounds
  have hT := target_slack_bounds
  have hS := square_bounds
  have h6 := sixth_loss_bounds
  rw [recovered_exact_difference]
  constructor <;> linarith only [hD.1,hD.2,hP.1,hP.2,hL.1,hL.2,hJ.1,hJ.2,hT.1,hT.2,hS.1,hS.2,h6.1,h6.2]

/-- This concrete certificate is insufficient. No upper bound on actual Q is asserted. -/
theorem recovered_strict_upper : recoveredCoefficient < 8*log (5000/4469)-1/250 := by
  have h := recovered_deficit_bounds.1
  unfold AnalyticTotalThreshold.target at h
  linarith only [h]

end
end Wu2008DoubleSieve.SixthLogTotalMagnitude
