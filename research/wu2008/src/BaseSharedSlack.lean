import GlobalLowerSlack

/-! Recover the original low-window trapezoid defect, after all old payments.
The polynomial below is the primitive of a uniform derivative inequality,
not a Taylor approximation. Every interval is inherited unchanged. -/
noncomputable section
open Real Set MeasureTheory
open scoped Interval
open Wu2008DoubleSieve
open ClassicalAnalyticLeaves
open FixedCoefficientUpperEnclosure (a s)
open FixedCoefficientHLowerEnclosure (c)
open Phase22 (u)
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
namespace BaseSharedSlack

/-- A uniform analytic remainder for the already used trapezoid bound. -/
theorem trapezoid_defect {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    log (1+z)+z^3/24 ≤ z*(2+z)/(2*(1+z)) := by
  let F : ℝ → ℝ := fun x => x*(2+x)/(2*(1+x))-log (1+x)-x^3/24
  have hd (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      HasDerivAt F (x^2/(2*(1+x)^2)-x^2/8) x := by
    have hn : 1+x ≠ 0 := by linarith [hx.1]
    convert (((((hasDerivAt_id x).mul ((hasDerivAt_id x).const_add 2)).div
      (((hasDerivAt_id x).const_add 1).const_mul 2) (mul_ne_zero (by norm_num) hn)).sub
      (((hasDerivAt_id x).const_add 1).log hn)).sub
      (((hasDerivAt_id x).pow 3).div_const 24)) using 1 <;>
      first | rfl | (dsimp; field_simp [hn]; ring)
  have hm : MonotoneOn F (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hh := interior_subset hx
      rw [(hd x hh).deriv]
      apply sub_nonneg.mpr
      have hx0 : 0 < 1+x := by linarith [hh.1]
      apply (le_div_iff₀ (show 0 < 2*(1+x)^2 by positivity)).2
      have hb : (1+x)^2 ≤ 4 := by nlinarith [hh.1,hh.2]
      nlinarith only [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hb)]
  have hh := hm (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1) ⟨hz,hz1⟩ hz
  have hzero : F 0=0 := by norm_num [F]
  rw [hzero] at hh
  dsimp [F] at hh
  linarith only [hh]

/-- The same whole first recurrence, with its discarded chord error retained. -/
theorem initial_density_defect {v : ℝ} (hv : 3 ≤ v) (hv4 : v ≤ 4) :
    (v-3)^3/72 ≤ (v-3)/(2*(v-2))-log (v-2)/(v-1) := by
  have h := trapezoid_defect (show 0 ≤ v-3 by linarith) (show v-3 ≤ 1 by linarith)
  rw [show 1+(v-3)=v-2 by ring,show 2+(v-3)=v-1 by ring] at h
  have hn : 0 < v-1 := by linarith
  have hn2 : v-2 ≠ 0 := by linarith
  have hh := div_le_div_of_nonneg_right h hn.le
  have he : ((v-3)*(v-1)/(2*(v-2)))/(v-1)=(v-3)/(2*(v-2)) := by
    field_simp
  rw [he,add_div] at hh
  have hb : (v-3)^3/72 ≤ ((v-3)^3/24)/(v-1) := by
    apply (le_div_iff₀ hn).2
    have hp := mul_nonneg (pow_nonneg (show 0 ≤ v-3 by linarith) 3)
      (show 0 ≤ 4-v by linarith)
    nlinarith only [hp]
  linarith only [hh,hb]

theorem upper_recurrence_defect {v : ℝ} (hv : 3 ≤ v) (hv4 : v ≤ 4) :
    wuUpperCoefficient v+(v-3)^4/288 ≤ (v-1-log (v-2))/2 := by
  let F : ℝ → ℝ := fun x => (x-1-log (x-2))/2-wuUpperCoefficient x-(x-3)^4/288
  have hd (x : ℝ) (hx : x ∈ Icc (3:ℝ) 4) : HasDerivAt F
      ((x-3)/(2*(x-2))-log (x-2)/(x-1)-(x-3)^3/72) x := by
    have hn : x-2 ≠ 0 := by linarith [hx.1]
    convert (((((hasDerivAt_id x).sub_const 1).sub
      (((hasDerivAt_id x).sub_const 2).log hn)).div_const 2).sub
      (JointSharedTightEnclosure.initial_derivative hx.1 (by linarith [hx.2])) |>.sub
      (((((hasDerivAt_id x).sub_const 3).pow 4)).div_const 288)) using 1 <;>
      first | rfl | (dsimp; field_simp [hn]; ring)
  have hm : MonotoneOn F (Icc (3:ℝ) 4) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hh := interior_subset hx
      rw [(hd x hh).deriv]
      exact sub_nonneg.mpr (initial_density_defect hh.1 hh.2)
  have hh := hm (by norm_num : (3:ℝ) ∈ Icc (3:ℝ) 4) ⟨hv,hv4⟩ hv
  have he : wuUpperCoefficient 3=1 := jr1965F_normalized_initial (by norm_num) le_rfl
  have hzero : F 3=0 := by norm_num [F,he]
  rw [hzero] at hh
  dsimp [F] at hh
  linarith only [hh]

theorem low_pointwise_gain {v : ℝ} (hv : 3 ≤ v) (hv4 : v ≤ 4) :
    (v-3)^4/288 ≤ SharedRationalEnvelope.p v-wuUpperCoefficient v := by
  have hh := upper_recurrence_defect hv hv4
  have hl := SharpLogRecurrence.log_lower (show 1 ≤ v-2 by linarith)
  unfold SharedRationalEnvelope.p
  linarith only [hh,hl]

def rate : ℝ := 16*(8-24*s)/288
def density (t : ℝ) : ℝ := rate*(u t-3)^4
def lowGain : ℝ := rate*a/5
def gain : ℝ := 122829709442/361709124148125

theorem low_density_gain {t : ℝ} (ht : t ∈ Icc (c 4) s) :
    density t ≤ SharedRationalEnvelope.weight t*
      (SharedRationalEnvelope.p (u t)-wuUpperCoefficient (u t)) := by
  obtain ⟨ht0,hd,hu3,hu4⟩ := SharedRationalEnvelope.geometry ht
  have hs : 0 < 8-24*s := by linarith [SharedRationalEnvelope.window_order.2.2]
  have hden : t*(1/2-t) ≤ 1/16 := by nlinarith [sq_nonneg (t-1/4)]
  have hw : 16*(8-24*s) ≤ SharedRationalEnvelope.weight t := by
    apply (le_div_iff₀ (mul_pos ht0 hd)).2
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hden),ht.2]
  have hp := low_pointwise_gain hu3 hu4
  have hm := mul_le_mul hw hp (by positivity : 0 ≤ (u t-3)^4/288)
    (by linarith : 0 ≤ SharedRationalEnvelope.weight t)
  unfold density rate
  nlinarith only [hm]

theorem lowGain_ftc : (∫ t in c 4..s, density t) = lowGain := by
  have hc : Continuous density := by unfold density u; fun_prop
  have hd (t : ℝ) : HasDerivAt (fun t => -rate*a/5*(u t-3)^5) (density t) t := by
    convert (((((hasDerivAt_const t (1/2:ℝ)).sub (hasDerivAt_id t)).div_const a).sub_const 3).pow 5
      |>.const_mul (-rate*a/5)) using 1 <;>
      first | rfl | (dsimp [density,u]; field_simp [truncatedSixthLower_parameters.1.ne']; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hc.intervalIntegrable _ _)]
  have h4 : u (c 4)=4 := by norm_num [u,a,c,truncatedSixthLowerAlpha]
  have h3 : u s=3 := by norm_num [u,a,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  rw [h4,h3]
  dsimp [lowGain]; ring

theorem low_gain_paid : lowGain ≤ BaseGSharedActualRecovery.lowKernel := by
  have ho := SharedRationalEnvelope.window_order
  have hU : ContinuousOn (fun t => wuUpperCoefficient (u t)) (Icc (c 4) s) := by
    apply continuousOn_wuUpperCoefficient.comp (by unfold u; fun_prop)
    intro t ht
    change 0 < u t
    linarith [(SharedRationalEnvelope.geometry ht).2.2.1]
  have hw : ContinuousOn SharedRationalEnvelope.weight (Icc (c 4) s) := by
    unfold SharedRationalEnvelope.weight
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact mul_ne_zero (SharedRationalEnvelope.geometry ht).1.ne'
      (SharedRationalEnvelope.geometry ht).2.1.ne'
  have hi := (hw.mul (SharedRationalEnvelope.p_continuous.sub hU)).intervalIntegrable_of_Icc
    (μ := volume) ho.2.1
  have hd : Continuous density := by unfold density u; fun_prop
  have hm := intervalIntegral.integral_mono_on ho.2.1 (hd.intervalIntegrable _ _) hi
    (fun t ht => low_density_gain ht)
  rw [lowGain_ftc] at hm
  rw [BaseGSharedActualRecovery.low_explicit]
  exact hm

/-- Retain a sharper denominator on the original beta recurrence interval. -/
def betaRate : ℝ := (625/2809-1/9)/(78/25)
def betaGain : ℝ := betaRate*(78/25-3)^3/3

theorem initial_log_lower {v : ℝ} (hv : 3 ≤ v) :
    2*(v-3)/(v-1) ≤ log (v-2) := by
  have hl := SharpLogRecurrence.log_lower (show 1 ≤ v-2 by linarith)
  have hn : 0 < v-1 := by linarith
  have hz : 0 ≤ v-3 := by linarith
  have hp : 0 ≤ (2:ℝ)*((v-3)/(v-1))^3/3 := by positivity
  unfold SharpLogRecurrence.lowerLog at hl
  rw [show v-2-1=v-3 by ring,show v-2+1=v-1 by ring] at hl
  have he : 2*(v-3)/(v-1)=2*((v-3)/(v-1)) := by ring
  rw [he]
  linarith only [hl,hp]

theorem beta_upper_lower {v : ℝ} (hv : 3 ≤ v) (hvhi : v ≤ 78/25) :
    1+(625/2809)*(v-3)^2 ≤ wuUpperCoefficient v := by
  let F : ℝ → ℝ := fun x => wuUpperCoefficient x-1-(625/2809)*(x-3)^2
  have hd (x : ℝ) (hx : x ∈ Icc (3:ℝ) (78/25)) :
      HasDerivAt F (log (x-2)/(x-1)-(1250/2809)*(x-3)) x := by
    convert ((JointSharedTightEnclosure.initial_derivative hx.1 (by linarith [hx.2])).sub_const 1).sub
      (((((hasDerivAt_id x).sub_const 3).pow 2)).const_mul (625/2809)) using 1 <;>
      first | rfl | (dsimp; ring)
  have hm : MonotoneOn F (Icc (3:ℝ) (78/25)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hh := interior_subset hx
      have hn : 0 < x-1 := by linarith [hh.1]
      have hz : 0 ≤ x-3 := by linarith [hh.1]
      have hl := div_le_div_of_nonneg_right (initial_log_lower hh.1) hn.le
      have he : (2*(x-3)/(x-1))/(x-1)=2*(x-3)/(x-1)^2 := by
        field_simp
      rw [he] at hl
      have hb : (x-1)^2 ≤ (2809/625:ℝ) := by nlinarith [hh.1,hh.2]
      have hp : (1250/2809)*(x-3) ≤ 2*(x-3)/(x-1)^2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hn)).2
        nlinarith only [mul_nonneg hz (sub_nonneg.mpr hb)]
      rw [(hd x hh).deriv]
      linarith only [hl,hp]
  have hh := hm (by norm_num : (3:ℝ) ∈ Icc (3:ℝ) (78/25)) ⟨hv,hvhi⟩ hv
  have he : wuUpperCoefficient 3=1 := jr1965F_normalized_initial (by norm_num) le_rfl
  have hzero : F 3=0 := by norm_num [F,he]
  rw [hzero] at hh
  dsimp [F] at hh
  linarith only [hh]

theorem beta_density_gain {v : ℝ} (hv : v ∈ Icc (3:ℝ) (78/25)) :
    betaRate*(v-3)^2 ≤ (wuUpperCoefficient v-(1+(v-3)^2/9))/v := by
  have hv0 : 0 < v := by linarith [hv.1]
  have hl := beta_upper_lower hv.1 hv.2
  have hn : 0 ≤ (625/2809-1/9:ℝ)*(v-3)^2 := by positivity
  have hm := div_le_div_of_nonneg_left hn hv0 hv.2
  have hh : (625/2809-1/9:ℝ)*(v-3)^2 ≤ wuUpperCoefficient v-(1+(v-3)^2/9) := by
    linarith only [hl]
  have hp := div_le_div_of_nonneg_right hh hv0.le
  unfold betaRate
  linarith only [hm,hp]

theorem beta_gain_paid : betaGain ≤ BaseGSharedActualRecovery.betaKernel := by
  have ho : (3:ℝ) ≤ 78/25 := by norm_num
  have hu := wuUpperCoefficient_div_intervalIntegrable (by norm_num : (0:ℝ)<3) ho
  have hq := BaseRecurrenceLower.polynomial_div_integrable
    (fun v : ℝ => 1+(v-3)^2/9) (by fun_prop) (by norm_num : (0:ℝ)<3) ho
  have hi : IntervalIntegrable (fun v : ℝ => (wuUpperCoefficient v-(1+(v-3)^2/9))/v)
      volume 3 (78/25) := by
    simp_rw [sub_div]
    exact hu.sub hq
  have hc : Continuous (fun v : ℝ => betaRate*(v-3)^2) := by fun_prop
  have hm := intervalIntegral.integral_mono_on ho (hc.intervalIntegrable _ _) hi
    (fun v hv => beta_density_gain hv)
  have hd (v : ℝ) : HasDerivAt (fun v : ℝ => betaRate*(v-3)^3/3)
      (betaRate*(v-3)^2) v := by
    convert (((((hasDerivAt_id v).sub_const 3).pow 3).const_mul betaRate).div_const 3) using 1 <;>
      first | rfl | (dsimp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v) (hc.intervalIntegrable _ _)] at hm
  change _ ≤ BaseGSharedActualRecovery.betaKernel at hm
  dsimp [betaGain]
  norm_num at hm ⊢
  exact hm

theorem base_gain_paid : 8*betaGain ≤ AnalyticTotalThreshold.baseLoss := by
  have he := GlobalLowerSlack.base_slack_identity
  have h1 := SharpLogRecurrence.log_lower (by norm_num : (1:ℝ) ≤ 3/2)
  have h2 := SharpLogRecurrence.log_lower (by norm_num : (1:ℝ) ≤ 26/25)
  linarith only [he,h1,h2,beta_gain_paid]

theorem gain_exact : (8*betaGain+lowGain)/4=gain := by
  norm_num [betaGain,betaRate,lowGain,rate,gain,a,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]

theorem gain_positive : 0 < gain := by norm_num [gain]

theorem gain_bounds : (339/1000000:ℝ) < gain ∧ gain < 340/1000000 := by norm_num [gain]

theorem gain_nonnegative : 0 ≤ gain := gain_positive.le

/-- This block excludes G, the collected log payment, fifth, sixth, and retained payments. -/
def block : ℝ := (AnalyticTotalThreshold.baseLoss+GlobalLowerSlack.highSlack+
  GlobalLowerSlack.middleSlack+BaseGSharedActualRecovery.lowKernel)/4

theorem block_payment : gain ≤ block := by
  obtain ⟨_,hh,hm,_⟩ := GlobalLowerSlack.component_nonnegative
  unfold block
  linarith only [hh,hm,base_gain_paid,low_gain_paid,gain_exact]

/-- Leave the whole sixth and retained blocks available for independent composition. -/
def other : ℝ := (GlobalLowerSlack.jSlack+GlobalLowerSlack.jPaymentSlack+
  (GlobalLowerSlack.fifthLogSlack-GlobalLowerSlack.fifthGain)+GlobalLowerSlack.fifthRecurrence+
  GlobalLowerSlack.sixthLogSlack+GlobalLowerSlack.sixthRecurrence+GlobalLowerSlack.fourSlack+
  GlobalLowerSlack.analyticPaymentSlack)/4+GlobalLowerSlack.retainedPaymentSlack+
  (FullAdmissibleSeed.Gamma6-FullAdmissibleStrength.polynomialPayment)/4+
  (2*(U8CanonicalMother.L-U8CanonicalMother.I)-U8ActualThreshold.gainLower)

theorem split_unpaid : GlobalLowerSlack.unpaid=block+other := by
  unfold GlobalLowerSlack.unpaid GlobalLowerSlack.realSlack block other
  ring

theorem other_positive : 0 < other := by
  obtain ⟨_,_,_,_,hj,hjp,_,h5r,h6,h6r,h4⟩ := GlobalLowerSlack.component_nonnegative
  have hf := GlobalLowerSlack.fifth_gain_paid
  have hp := GlobalLowerSlack.payment_nonnegative
  have hG := FullAdmissibleStrength.polynomial_payment
  have hU := U8ActualThreshold.exact_weight_gain_bounds.1
  unfold other
  linarith only [hj,hjp,h5r,h6,h6r,h4,hf,hp.1,hp.2,hG,hU]

def coefficient : ℝ := GlobalLowerSlack.lowerCoefficient+gain

theorem actual_remaining_identity : U8CanonicalMother.improvedCoefficient-coefficient =
    (block-gain)+other := by
  have he := GlobalLowerSlack.actual_remaining_identity
  rw [split_unpaid] at he
  unfold coefficient
  linarith only [he]

theorem actual_lower : coefficient < U8CanonicalMother.improvedCoefficient := by
  have he := actual_remaining_identity
  have hb := block_payment
  have ho := other_positive
  linarith only [he,hb,ho]

theorem strict_improvement : GlobalLowerSlack.lowerCoefficient < coefficient := by
  unfold coefficient
  linarith only [gain_positive]

theorem strict_ordinary_P2 :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        coefficient*U8CanonicalMother.M N <
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  have hp : 0 < (U8CanonicalMother.improvedCoefficient-coefficient)/2 :=
    half_pos (sub_pos.mpr actual_lower)
  obtain ⟨δ,hδ,hδhi,T,hT,h⟩ := U8CanonicalMother.improved_ordinary_P2 _ hp
  refine ⟨δ,hδ,hδhi,T,hT,?_⟩
  intro N hN he
  have hs : 0 < U8CanonicalMother.M N := HighSixPhase6.original_scale_positive (hT.trans hN)
  have hc : coefficient < U8CanonicalMother.improvedCoefficient-
      (U8CanonicalMother.improvedCoefficient-coefficient)/2 := by linarith only [hp]
  exact (mul_lt_mul_of_pos_right hc hs).trans_le (h N hN he)

end BaseSharedSlack
