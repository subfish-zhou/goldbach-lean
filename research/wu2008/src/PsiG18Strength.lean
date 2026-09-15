import JointLogTotalComparison

namespace Wu2008DoubleSieve.PsiG18Strength
open Real Set MeasureTheory
noncomputable section

/-- Both sides enclose the literal logarithmic C18, not an H upper bound. -/
theorem C18_bounds : (1071/10000 : ℝ) < Phase18.C18 ∧ Phase18.C18 < 108/1000 := by
  have h1 := SharpLogRecurrence.log_lower (by norm_num : (1 : ℝ) ≤ 1327/814)
  have h2 := SharpLogRecurrence.log_upper (by norm_num : (1 : ℝ) ≤ 1327/814)
  have h3 := SharpLogRecurrence.log_lower (by norm_num : (1 : ℝ) ≤ 1840/1327)
  have h4 := SharpLogRecurrence.log_upper (by norm_num : (1 : ℝ) ≤ 1840/1327)
  norm_num [SharpLogRecurrence.lowerLog,SharpLogRecurrence.upperLog] at h1 h2 h3 h4
  unfold Phase18.C18 Phase18.C Phase18.Gamma
  rw [Phase11.Ctail_exact,Phase12.Cmid_exact]
  norm_num [Phase18.coupled,Phase18.U,Phase18.V,Phase16.L0,Phase16.r0,Phase14.w0]
  constructor <;> linarith only [h1,h2,h3,h4]

/-- Existing fixed source and feedback constants, with no change to the recurrence. -/
theorem g18_bounds : (285/1000000 : ℝ) < Phase18.g18 ∧ Phase18.g18 < 354/1000000 := by
  have hd := sub_pos.mpr Phase17.rhoCoupled_bounds.2
  have hp : 0 < HighSixPhase9.sourceP := by norm_num [HighSixPhase9.sourceP]
  have hl := mul_lt_mul_of_pos_right C18_bounds.1 hp
  have hu := mul_lt_mul_of_pos_right C18_bounds.2 hp
  have hr := Phase17.rhoCoupled_upper
  have hn := Phase17.rhoCoupled_bounds.1
  unfold Phase18.g18
  constructor
  · apply (lt_div_iff₀ hd).2
    norm_num [HighSixPhase9.sourceP] at hl ⊢
    linarith only [hl,hn]
  · apply (div_lt_iff₀ hd).2
    norm_num [HighSixPhase9.sourceP] at hu ⊢
    linarith only [hu,hr]

/-- The original prime window stays strictly to the right of 1/4. -/
theorem prime_kernel_bounds {t : ℝ} (ht : t ∈ Icc HighSix.left HighSix.right) :
    1/(HighSix.left*(1/2-HighSix.left)) ≤ 1/(t*(1/2-0-t)) ∧
    1/(t*(1/2-0-t)) ≤ 1/(HighSix.right*(1/2-HighSix.right)) := by
  have ht0 : 0 < t := by norm_num [HighSix.left] at ht; linarith [ht.1]
  have hc : 0 < 1/2-t := by norm_num [HighSix.right] at ht; linarith [ht.2]
  have htl : 0 ≤ t-HighSix.left := sub_nonneg.mpr ht.1
  have hrt : 0 ≤ HighSix.right-t := sub_nonneg.mpr ht.2
  have hsl : 0 ≤ t+HighSix.left-1/2 := by norm_num [HighSix.left] at *; linarith [ht.1]
  have hsr : 0 ≤ HighSix.right+t-1/2 := by norm_num [HighSix.left,HighSix.right] at *; linarith [ht.1]
  have hdl : t*(1/2-t) ≤ HighSix.left*(1/2-HighSix.left) := by
    nlinarith only [mul_nonneg htl hsl]
  have hdr : HighSix.right*(1/2-HighSix.right) ≤ t*(1/2-t) := by
    nlinarith only [mul_nonneg hrt hsr]
  norm_num only [sub_zero]
  exact ⟨one_div_le_one_div_of_le (mul_pos ht0 hc) hdl,
    one_div_le_one_div_of_le (by norm_num [HighSix.right]) hdr⟩

/-- Exact endpoint bounds for the same integral, not sampled quadrature. -/
theorem prime_integral_bounds :
    ((HighSix.right-HighSix.left)/(HighSix.left*(1/2-HighSix.left))) ≤ HighSix.primeIntegral 0 ∧
    HighSix.primeIntegral 0 ≤ ((HighSix.right-HighSix.left)/(HighSix.right*(1/2-HighSix.right))) := by
  have hi := HighSixDeltaLimit.prime_kernel_integrable (δ := 0) (by norm_num)
  have hab : HighSix.left ≤ HighSix.right := by norm_num [HighSix.left,HighSix.right]
  have hl := intervalIntegral.integral_mono_on hab intervalIntegrable_const hi
    (fun t ht => (prime_kernel_bounds ht).1)
  have hu := intervalIntegral.integral_mono_on hab hi intervalIntegrable_const
    (fun t ht => (prime_kernel_bounds ht).2)
  rw [intervalIntegral.integral_const,smul_eq_mul] at hl hu
  constructor
  · simpa only [HighSix.primeIntegral,div_eq_mul_inv,one_mul] using hl
  · simpa only [HighSix.primeIntegral,div_eq_mul_inv,one_mul] using hu

/-- The genuine negative omega term remains in this exact source identity. -/
theorem original_psi_identity :
    firstFunctionalGainPsiOne HighSix.s HighSix.S =
      (∫ v in HighSixPhase5.q..HighSixPhase5.r, HighSixPhase5.combined v)-
      (∫ v in (1 : ℝ)..HighSixPhase5.q, HighSixPhase5.baseLog v)-
      omega3XIntegralEnvelope HighSix.s HighSix.S := by
  exact HighSixPhase5.original_combined

/-- A denominator bound on the entire existing transformed interval. -/
theorem combined_upper {v : ℝ} (hv : v ∈ Icc HighSixPhase5.q HighSixPhase5.r) :
    HighSixPhase5.combined v ≤ (2*v-HighSixPhase5.r)/(4*(HighSixPhase5.r+1)) := by
  have hv1 : 1 ≤ v := by norm_num [HighSixPhase5.q] at hv; linarith [hv.1]
  have hv0 : 0 < v := by linarith
  have hlog : log v ≤ 1/2 := by
    have hm := log_le_log hv0 hv.2
    have hu := SharpLogRecurrence.log_upper (by norm_num [HighSixPhase5.r] : 1 ≤ HighSixPhase5.r)
    norm_num [HighSixPhase5.r,SharpLogRecurrence.upperLog] at hu hm
    linarith only [hm,hu]
  have hn : 0 ≤ 2*v-HighSixPhase5.r := by
    norm_num [HighSixPhase5.q,HighSixPhase5.r] at hv ⊢; linarith [hv.1]
  have hden : 2*(HighSixPhase5.r+1) ≤ 2*(179/50-1-v)*(v+1) := by
    have hm := mul_nonneg (sub_nonneg.mpr hv.2)
      (show 0 ≤ v by exact hv0.le)
    norm_num [HighSixPhase5.r] at *
    nlinarith only [hm]
  have hd : 0 < 2*(179/50-1-v)*(v+1) := by
    have h := (show 0 < 2*(HighSixPhase5.r+1) by norm_num [HighSixPhase5.r]).trans_le hden
    exact h
  have hnum := mul_le_mul_of_nonneg_left hlog hn
  have he : HighSixPhase5.combined v = (2*v-HighSixPhase5.r)*log v/(2*(179/50-1-v)*(v+1)) := by
    unfold HighSixPhase5.combined HighSixPhase5.r
    congr 1; ring
  rw [he]
  calc
    _ ≤ ((2*v-HighSixPhase5.r)*(1/2))/(2*(179/50-1-v)*(v+1)) :=
      div_le_div_of_nonneg_right hnum hd.le
    _ ≤ ((2*v-HighSixPhase5.r)*(1/2))/(2*(HighSixPhase5.r+1)) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num [HighSixPhase5.r]) hden
    _ = _ := by norm_num [HighSixPhase5.r]; ring

/-- Original universal log lower bound, with no added series term. -/
theorem base_lower {v : ℝ} (hv : v ∈ Icc 1 HighSixPhase5.q) :
    2*(v-1)/(HighSixPhase5.q+1)^2 ≤ HighSixPhase5.baseLog v := by
  have hp : 0 < v+1 := by linarith [hv.1]
  have hlog := HighSixPhase5.log_lower hv.1
  calc
    _ ≤ 2*(v-1)/(v+1)^2 := div_le_div_of_nonneg_left (by linarith [hv.1])
      (sq_pos_of_pos hp) (pow_le_pow_left₀ hp.le (by linarith [hv.2]) 2)
    _ = (2*(v-1)/(v+1))/(v+1) := by rw [div_div,pow_two]
    _ ≤ HighSixPhase5.baseLog v := div_le_div_of_nonneg_right hlog hp.le

/-- Only the sign of the subtracted omega is relaxed, and only for this upper bound. -/
theorem psi_upper : firstFunctionalGainPsiOne HighSix.s HighSix.S ≤ (247583537/6985258410 : ℝ) := by
  have hc := intervalIntegral.integral_mono_on
    (show HighSixPhase5.q ≤ HighSixPhase5.r by norm_num [HighSixPhase5.q,HighSixPhase5.r])
    (HighSixPhase5.combined_continuous.intervalIntegrable_of_Icc (by norm_num [HighSixPhase5.q,HighSixPhase5.r]))
    (show IntervalIntegrable (fun v : ℝ => (2*v-HighSixPhase5.r)/(4*(HighSixPhase5.r+1))) volume _ _ from
      (by fun_prop : Continuous (fun v : ℝ => (2*v-HighSixPhase5.r)/(4*(HighSixPhase5.r+1)))).intervalIntegrable _ _)
    (fun v hv => combined_upper hv)
  have hb := intervalIntegral.integral_mono_on
    (show (1 : ℝ) ≤ HighSixPhase5.q by norm_num [HighSixPhase5.q])
    (show IntervalIntegrable (fun v : ℝ => 2*(v-1)/(HighSixPhase5.q+1)^2) volume _ _ from
      (by fun_prop : Continuous (fun v : ℝ => 2*(v-1)/(HighSixPhase5.q+1)^2)).intervalIntegrable _ _)
    ((HighSixPhase5.baseLog_continuous (b := HighSixPhase5.q) le_rfl).intervalIntegrable_of_Icc (by norm_num [HighSixPhase5.q]))
    (fun v hv => base_lower hv)
  have hcftc : (∫ v in HighSixPhase5.q..HighSixPhase5.r,
      (2*v-HighSixPhase5.r)/(4*(HighSixPhase5.r+1))) =
      (HighSixPhase5.r-HighSixPhase5.q)*HighSixPhase5.q/(4*(HighSixPhase5.r+1)) := by
    have hd (v : ℝ) : HasDerivAt
        (fun x : ℝ => (x^2-HighSixPhase5.r*x)/(4*(HighSixPhase5.r+1)))
        ((2*v-HighSixPhase5.r)/(4*(HighSixPhase5.r+1))) v := by
      convert (((hasDerivAt_id v).pow 2).sub
        ((hasDerivAt_id v).const_mul HighSixPhase5.r)).div_const (4*(HighSixPhase5.r+1)) using 1 <;>
        first | rfl | (dsimp; ring)
    have hi : IntervalIntegrable (fun v : ℝ =>
        (2*v-HighSixPhase5.r)/(4*(HighSixPhase5.r+1))) volume HighSixPhase5.q HighSixPhase5.r :=
      (by fun_prop : Continuous (fun v : ℝ =>
        (2*v-HighSixPhase5.r)/(4*(HighSixPhase5.r+1)))).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v) hi]
    ring
  have hbftc : (∫ v in (1 : ℝ)..HighSixPhase5.q, 2*(v-1)/(HighSixPhase5.q+1)^2) =
      (HighSixPhase5.q-1)^2/(HighSixPhase5.q+1)^2 := by
    have hd (v : ℝ) : HasDerivAt
        (fun x : ℝ => (x-1)^2/(HighSixPhase5.q+1)^2)
        (2*(v-1)/(HighSixPhase5.q+1)^2) v := by
      convert (((hasDerivAt_id v).sub_const 1).pow 2).div_const ((HighSixPhase5.q+1)^2) using 1 <;>
        first | rfl | (dsimp; ring)
    have hi : IntervalIntegrable (fun v : ℝ =>
        2*(v-1)/(HighSixPhase5.q+1)^2) volume 1 HighSixPhase5.q :=
      (by fun_prop : Continuous (fun v : ℝ =>
        2*(v-1)/(HighSixPhase5.q+1)^2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v) hi]
    norm_num
  rw [hcftc] at hc
  rw [hbftc] at hb
  have ho := (omega3XIntegralEnvelope_bounds
    (s := HighSix.s) (t := HighSix.S) (by norm_num [HighSix.s])
    (by norm_num [HighSix.s,HighSix.S]) (by norm_num [HighSix.S])).1
  rw [original_psi_identity]
  norm_num [HighSixPhase5.q,HighSixPhase5.r] at hc hb ⊢
  linarith only [hc,hb,ho]

/-- A genuine positive magnitude from the same Phi and the sharper original window. -/
theorem psi_loss_lower : (15/1000000 : ℝ) < Phase20.psiPaymentLoss := by
  have hp := HighSixPhase5.psi_lower
  have h := mul_le_mul hp prime_integral_bounds.1
    (by norm_num [HighSix.left,HighSix.right]) (HighSixPhase5.psi_positive.le)
  unfold Phase20.psiPaymentLoss Phase20.rawPsi
  norm_num [Phase20.fixedPsi,HighSix.left,HighSix.right,HighSix.s,HighSix.S] at h ⊢
  linarith only [h]

/-- The upper bound is on the actual defined product, not merely its lower certificate. -/
theorem psi_loss_upper : Phase20.psiPaymentLoss ≤
    (328543353599/72210108813375 : ℝ)-Phase20.fixedPsi := by
  have h := mul_le_mul psi_upper prime_integral_bounds.2
    HighSixPhase6.primeIntegral_zero_positive.le (by norm_num)
  unfold Phase20.psiPaymentLoss Phase20.rawPsi
  norm_num [HighSix.left,HighSix.right] at h
  linarith only [h]

/-- Full two-sided magnitude for exactly the two requested recoveries. -/
theorem two_recoveries_bounds : (3/10000 : ℝ) < Phase18.g18+Phase20.psiPaymentLoss ∧
    Phase18.g18+Phase20.psiPaymentLoss < 1/200 := by
  have hl := psi_loss_lower
  have hu := psi_loss_upper
  have hg := g18_bounds
  norm_num [Phase20.fixedPsi] at hu
  constructor <;> linarith only [hl,hu,hg.1,hg.2]

/-- These two actual terms alone do not cover D0; no assertion about Q follows. -/
theorem remaining_debit_bounds :
    JointLogTotalComparison.rationalDeficit-1/200 <
      JointLogTotalComparison.rationalDeficit-Phase18.g18-Phase20.psiPaymentLoss ∧
    JointLogTotalComparison.rationalDeficit-Phase18.g18-Phase20.psiPaymentLoss <
      JointLogTotalComparison.rationalDeficit-3/10000 := by
  constructor <;> linarith only [two_recoveries_bounds.1,two_recoveries_bounds.2]

theorem remaining_debit_positive : (19/200 : ℝ) <
    JointLogTotalComparison.rationalDeficit-Phase18.g18-Phase20.psiPaymentLoss := by
  linarith only [remaining_debit_bounds.1,JointLogTotalComparison.rational_magnitude.2]

/-- A quantitative interval for the latest complete target difference. -/
theorem full_difference_bounds :
    JointLogTotalComparison.rationalDeficit-1/200-JointLogTotalComparison.logRemainder-
      (JointJLossStrength.recovery-JointJLossStrength.fixedRecovery)/4-JointLogTotalComparison.targetSlack <
      AnalyticTotalThreshold.target-JointEndpointPayment.analyticLower ∧
    AnalyticTotalThreshold.target-JointEndpointPayment.analyticLower <
      JointLogTotalComparison.rationalDeficit-3/10000-JointLogTotalComparison.logRemainder-
      (JointJLossStrength.recovery-JointJLossStrength.fixedRecovery)/4-JointLogTotalComparison.targetSlack := by
  rw [JointLogTotalComparison.exact_target_parent_difference]
  constructor <;> linarith only [remaining_debit_bounds.1,remaining_debit_bounds.2]

end
end Wu2008DoubleSieve.PsiG18Strength
