import F1SignedUpperWhole

noncomputable section
open Real Set Wu2008DoubleSieve SharpLogRecurrence
open F1JointFTC F1JointSplit F1FullRecoveryPayment F1ActualSecondFTC F1BFullFTC
namespace CliF1AffinePaymentParent
open F1SignedUpperFTC

def polyPrimitive (x t : ℝ) : ℝ :=
  ((x-1)/8)*(t-1)^8-(1/9)*(t-1)^9

def correctionPrimitive (x t : ℝ) : ℝ :=
  polyPrimitive x t * 12 / (x^4*((x+1)^5*35))

def primitive (x t : ℝ) : ℝ := F1SignedUpperFTC.primitive x t + correctionPrimitive x t

def payment (x : ℝ) : ℝ :=
  F1SignedUpperFTC.payment x + (x-1)^9/(210*x^4*(x+1)^5)

theorem correctionPrimitive_at_one (x : ℝ) : correctionPrimitive x 1 = 0 := by
  norm_num [correctionPrimitive,polyPrimitive]

theorem correctionPrimitive_at_self {x : ℝ} (hx : 1 ≤ x) : correctionPrimitive x x =
    (x-1)^9/(210*x^4*(x+1)^5) := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x + 1 ≠ 0 := by linarith
  unfold correctionPrimitive polyPrimitive
  field_simp [hx0,hx1]
  ring

theorem primitive_at_self {x : ℝ} (hx : 1 ≤ x) : primitive x x = payment x := by
  unfold primitive payment F1SignedUpperFTC.payment
  rw [correctionPrimitive_at_self hx]

theorem polyPrimitive_deriv (x t : ℝ) :
    HasDerivAt (polyPrimitive x) ((t-1)^7*(x-t)) t := by
  have hbase := ((((hasDerivAt_id t).sub_const 1).pow 8).const_mul ((x-1)/8)).sub
      ((((hasDerivAt_id t).sub_const 1).pow 9).const_mul (1/9))
  convert hbase using 1 <;> first
    | rfl
    | (norm_num; ring)

theorem correctionPrimitive_deriv (x t : ℝ) :
    HasDerivAt (correctionPrimitive x)
      (12*(t-1)^7*(x-t)/(35*x^4*(x+1)^5)) t := by
  have h := ((polyPrimitive_deriv x t).const_mul 12).div_const (35*x^4*(x+1)^5)
  convert h using 1 <;> first
    | rfl
    | (funext y; dsimp [correctionPrimitive]; ring)
    | ring

theorem primitive_deriv (x t : ℝ) :
    HasDerivAt (primitive x)
      ((t-1)^7*(3*t+1)/(35*x^3*(x+1)^5)+
        12*(t-1)^7*(x-t)/(35*x^4*(x+1)^5)) t := by
  have h := (F1SignedUpperFTC.primitive_deriv x t).add (correctionPrimitive_deriv x t)
  have hfun : primitive x =ᶠ[nhds t] (F1SignedUpperFTC.primitive x + correctionPrimitive x) := by
    exact Filter.Eventually.of_forall (by intro y; rfl)
  have hprime := h.congr_of_eventuallyEq hfun
  simpa [primitive, correctionPrimitive, mul_comm, mul_left_comm, mul_assoc] using hprime

theorem reciprocal_affine_lower {x t : ℝ} (ht : 1 ≤ t) (htx : t ≤ x) :
    1/(x^3*(x+1)^5)+3*(x-t)/(x^4*(x+1)^5) ≤
      1/(t^3*(t+1)^5) := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t+1 := by linarith
  have hx1 : 1 ≤ x := ht.trans htx
  have hx0 : 0 < x := by linarith
  have hxp : 0 < x+1 := by linarith
  have hcube_gap : 0 ≤ (x-t)^2*(3*t^2+2*t*x+x^2) := by positivity
  have hcube_poly : 0 ≤ x^4 - t^3*(x+3*(x-t)) := by
    rw [show x^4 - t^3*(x+3*(x-t)) =
        (x-t)^2*(3*t^2+2*t*x+x^2) by ring]
    exact hcube_gap
  have hcube_mul : t^3*(x+3*(x-t)) ≤ x^4 := by linarith only [hcube_poly]
  have hcube : 1/x^3 + 3*(x-t)/x^4 ≤ 1/t^3 := by
    have hmul : t^3*(x+3*(x-t)) ≤ x^4 := hcube_mul
    rw [show 1/x^3 + 3*(x-t)/x^4 = (x+3*(x-t))/x^4 by
      field_simp [ne_of_gt hx0]]
    rw [div_le_iff₀ (by positivity : 0 < x^4)]
    rw [show (1 / t ^ 3) * x ^ 4 = x^4 / t^3 by ring]
    have hmul' : (x+3*(x-t))*t^3 ≤ x^4 := by nlinarith only [hmul]
    exact (le_div_iff₀ (by positivity : 0 < t^3)).mpr hmul'
  have hpow : (t+1)^5 ≤ (x+1)^5 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) 5
  have hplus : 1/(x+1)^5 ≤ 1/(t+1)^5 := by
    exact one_div_le_one_div_of_le (by positivity) hpow
  have hmul := mul_le_mul hcube hplus (by positivity : 0 ≤ 1/(x+1)^5)
    (by positivity : 0 ≤ 1/t^3)
  rw [show 1/(x^3*(x+1)^5)+3*(x-t)/(x^4*(x+1)^5) =
      (1/x^3+3*(x-t)/x^4)*(1/(x+1)^5) by
    field_simp [ne_of_gt hx0, ne_of_gt hxp]]
  rw [show 1/(t^3*(t+1)^5) = 1/t^3*(1/(t+1)^5) by
    field_simp [ne_of_gt ht0, ne_of_gt ht1]]
  exact hmul

theorem payment_le_error {x : ℝ} (hx : 1 ≤ x) : payment x ≤ high x - log x := by
  let f : ℝ → ℝ := fun t => high t - log t - primitive x t
  have hd (t : ℝ) (ht : t ∈ Icc 1 x) :=
    (F1SignedUpperFTC.high_error_deriv ht.1).sub (primitive_deriv x t)
  have hm : MonotoneOn f (Icc 1 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 x)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have htI : t ∈ Icc 1 x := interior_subset ht
    have htpos : 0 < t := by linarith [htI.1]
    have hxpos : 0 < x := by linarith [htI.1, htI.2]
    have ht1pos : 0 < t + 1 := by linarith
    have hx1pos : 0 < x + 1 := by linarith
    have hn : 0 ≤ (t-1)^7*(3*t+1)/35 := by
      have ht0 : 0 ≤ t - 1 := sub_nonneg.mpr htI.1
      have ht1 : 0 ≤ 3*t + 1 := by nlinarith [htI.1]
      positivity
    have hr := reciprocal_affine_lower htI.1 htI.2
    have hmul := mul_le_mul_of_nonneg_left hr hn
    have hbase_nonneg : 0 ≤ 3*(t-1)^7*(x-t)/(35*x^4*(x+1)^5) := by
      have htm : 0 ≤ x - t := sub_nonneg.mpr htI.2
      have ht0 : 0 ≤ t - 1 := sub_nonneg.mpr htI.1
      positivity
    have hfactor : (4:ℝ) ≤ 3*t+1 := by linarith [htI.1]
    have hcorr0 := mul_le_mul_of_nonneg_left hfactor hbase_nonneg
    have hcorr : 12*(t-1)^7*(x-t)/(35*x^4*(x+1)^5) ≤
        ((t-1)^7*(3*t+1)/35)*(3*(x-t)/(x^4*(x+1)^5)) := by
      convert hcorr0 using 1 <;> first
        | rfl
        | (solve | ring)
        | field_simp [ne_of_gt hxpos, ne_of_gt hx1pos]
    have hmul' : (t-1)^7*(3*t+1)/(35*x^3*(x+1)^5)+
          ((t-1)^7*(3*t+1)/35)*(3*(x-t)/(x^4*(x+1)^5)) ≤
        (t-1)^7*(3*t+1)/(35*t^3*(t+1)^5) := by
      convert hmul using 1 <;> first
        | rfl
        | (solve | ring)
        | field_simp [ne_of_gt htpos, ne_of_gt ht1pos, ne_of_gt hxpos, ne_of_gt hx1pos]
    have htarget : (t-1)^7*(3*t+1)/(35*x^3*(x+1)^5)+
          12*(t-1)^7*(x-t)/(35*x^4*(x+1)^5) ≤
        (t-1)^7*(3*t+1)/(35*t^3*(t+1)^5) := by
      exact (add_le_add (le_refl _) hcorr).trans hmul'
    apply sub_nonneg.mpr
    exact htarget
  have h := hm (show (1:ℝ) ∈ Icc 1 x from ⟨le_rfl,hx⟩)
    (show x ∈ Icc 1 x from ⟨hx,le_rfl⟩) hx
  have hf : f 1 = 0 := by
    norm_num [f,primitive,correctionPrimitive_at_one,F1SignedUpperFTC.primitive,high,
      upperGapPayment,JointLogTotalComparison.V,upperLog,lowerLog]
  rw [hf] at h
  have hxval : f x = high x - log x - payment x := by
    dsimp [f]
    rw [primitive_at_self hx]
  rw [hxval] at h
  linarith only [h]

theorem correction_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ (x-1)^9/(210*x^4*(x+1)^5) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 ≤ x-1 := sub_nonneg.mpr hx
  positivity

theorem correction_pos {x : ℝ} (hx : 1 < x) :
    0 < (x-1)^9/(210*x^4*(x+1)^5) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x-1 := sub_pos.mpr hx
  positivity

theorem old_payment_le_payment {x : ℝ} (hx : 1 ≤ x) :
    F1SignedUpperFTC.payment x ≤ payment x := by
  unfold payment
  linarith only [correction_nonneg hx]

theorem old_payment_lt_payment {x : ℝ} (hx : 1 < x) :
    F1SignedUpperFTC.payment x < payment x := by
  unfold payment
  linarith only [correction_pos hx]

theorem payment_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ payment x := by
  linarith only [F1SignedUpperFTC.payment_nonneg hx, old_payment_le_payment hx]

theorem payment_pos {x : ℝ} (hx : 1 < x) : 0 < payment x := by
  linarith only [F1SignedUpperFTC.payment_pos hx, old_payment_lt_payment hx]

def splitPayment (x : ℝ) : ℝ := payment ((1+x)/2) + payment (2*x/(1+x))

theorem splitPayment_le_error {x : ℝ} (hx : 1 ≤ x) :
    splitPayment x ≤ splitHigh x - log x := by
  have ha := payment_le_error (FirstIntegralRecovery.split_arguments hx).1
  have hb := payment_le_error (FirstIntegralRecovery.split_arguments hx).2
  rw [FirstIntegralRecovery.split_log_identity hx]
  unfold splitPayment splitHigh
  linarith only [ha,hb]

theorem splitPayment_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ splitPayment x :=
  add_nonneg (payment_nonneg (FirstIntegralRecovery.split_arguments hx).1)
    (payment_nonneg (FirstIntegralRecovery.split_arguments hx).2)

theorem splitPayment_pos {x : ℝ} (hx : 1 < x) : 0 < splitPayment x :=
  add_pos_of_pos_of_nonneg (payment_pos (by linarith : 1 < (1+x)/2))
    (payment_nonneg (FirstIntegralRecovery.split_arguments hx.le).2)

theorem old_splitPayment_le {x : ℝ} (hx : 1 ≤ x) :
    F1SignedUpperFTC.splitPayment x ≤ splitPayment x := by
  have ha := old_payment_le_payment (FirstIntegralRecovery.split_arguments hx).1
  have hb := old_payment_le_payment (FirstIntegralRecovery.split_arguments hx).2
  unfold F1SignedUpperFTC.splitPayment splitPayment
  linarith only [ha,hb]

theorem old_splitPayment_lt {x : ℝ} (hx : 1 < x) :
    F1SignedUpperFTC.splitPayment x < splitPayment x := by
  have ha := old_payment_lt_payment (by linarith : 1 < (1+x)/2)
  have hb := old_payment_le_payment (FirstIntegralRecovery.split_arguments hx.le).2
  unfold F1SignedUpperFTC.splitPayment splitPayment
  linarith only [ha,hb]

theorem negative_payment {c x : ℝ} (hc : c ≤ 0) (hx : 1 ≤ x) :
    c*splitHigh x+(-c)*splitPayment x ≤ c*log x := by
  have h := mul_le_mul_of_nonneg_left (splitPayment_le_error hx) (neg_nonneg.mpr hc)
  linarith only [h]

def oldPayment : ℝ := (-(WholeCommonLog.coeffThreeHalf))*splitPayment (3/2)+
  (-(WholeCommonLog.coeffD))*splitPayment (4508/3981)+
  (-(WholeCommonLog.poleZero))*splitPayment (927/800)+
  (-(WholeCommonLog.coeffAP))*splitPayment (crossOnePlus)+
  (-(WholeCommonLog.coeffTM))*splitPayment (crossTwoMinus)+
  (-(WholeCommonLog.coeffBM))*splitPayment (bCrossOneMinus)

theorem oldPayment_le_balance : oldPayment ≤ WholeCommonLog.collected-WholeCommonLog.lower-TailEndpointPayment.recovery := by
  obtain ⟨hxm,hxp,hym,hyp⟩ := cross_arguments
  obtain ⟨hbxm,hbxp,hbym,hbyp⟩ := b_cross_arguments
  have h0 := mul_le_mul_of_nonpos_left log_two_le WholeCommonLog.coeffTwo_sign
  have h1 := negative_payment WholeCommonLog.coeffThreeHalf_sign (by norm_num : (1:ℝ) ≤ 3/2)
  have h2 := ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 1127/600)
  have h3 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 3884129/3606400)) WholeCommonLog.coeffA_sign
  have h4 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 4508/2927)) WholeCommonLog.coeffAC_sign
  have h5 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 2400/2381)) (neg_nonneg.mpr WholeCommonLog.coeffB_sign)
  have h6 := negative_payment WholeCommonLog.coeffD_sign (by norm_num : (1:ℝ) ≤ 4508/3981)
  have h7 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 2254/1727)) WholeCommonLog.coeffS_sign
  have h8 := negative_payment WholeCommonLog.poleZero_sign (by norm_num : (1:ℝ) ≤ 927/800)
  have h9 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 727/600)) WholeCommonLog.poleOne_sign
  have h10 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hxm) WholeCommonLog.coeffAM_sign
  have h11 := negative_payment WholeCommonLog.coeffAP_sign hxp
  have h12 := negative_payment WholeCommonLog.coeffTM_sign hym
  have h13 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hyp) WholeCommonLog.coeffTP_sign
  have h14 := negative_payment WholeCommonLog.coeffBM_sign hbxm
  have h15 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hbxp) WholeCommonLog.coeffBP_sign
  have h16 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hbym) WholeCommonLog.coeffDM_sign
  have h17 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hbyp) WholeCommonLog.coeffDP_sign
  unfold oldPayment WholeCommonLog.collected WholeCommonLog.lower TailEndpointPayment.recovery
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17]

theorem oldPayment_pos : 0 < oldPayment := by
  obtain ⟨_,hxp,hym,_⟩ := cross_arguments
  obtain ⟨hbxm,_,_,_⟩ := b_cross_arguments
  have hc : WholeCommonLog.coeffThreeHalf < 0 := by
    rw [WholeCommonLog.coeffThreeHalf_exact]
    norm_num
  have hp := mul_pos (neg_pos.mpr hc) (splitPayment_pos (by norm_num : (1:ℝ) < 3/2))
  have h6 := mul_nonneg (neg_nonneg.mpr WholeCommonLog.coeffD_sign) (splitPayment_nonneg (by norm_num : (1:ℝ) ≤ 4508/3981))
  have h8 := mul_nonneg (neg_nonneg.mpr WholeCommonLog.poleZero_sign) (splitPayment_nonneg (by norm_num : (1:ℝ) ≤ 927/800))
  have h11 := mul_nonneg (neg_nonneg.mpr WholeCommonLog.coeffAP_sign) (splitPayment_nonneg hxp)
  have h12 := mul_nonneg (neg_nonneg.mpr WholeCommonLog.coeffTM_sign) (splitPayment_nonneg hym)
  have h14 := mul_nonneg (neg_nonneg.mpr WholeCommonLog.coeffBM_sign) (splitPayment_nonneg hbxm)
  unfold oldPayment
  linarith only [hp,h6,h8,h11,h12,h14]

def newPayment : ℝ := (-(TailWholeCommonLog.coeffThreeHalf))*splitPayment (3/2)+
  (-(TailWholeCommonLog.coeffA))*splitPayment (3884129/3606400)+
  (-(TailWholeCommonLog.coeffAC))*splitPayment (4508/2927)+
  (-(-TailWholeCommonLog.coeffB))*splitPayment (2400/2381)+
  (-(TailWholeCommonLog.coeffS))*splitPayment (2254/1727)+
  (-(TailWholeCommonLog.poleOne))*splitPayment (727/600)+
  (-(TailWholeCommonLog.coeffAM))*splitPayment (crossOneMinus)+
  (-(TailWholeCommonLog.coeffBP))*splitPayment (bCrossOnePlus)+
  (-(TailWholeCommonLog.coeffDP))*splitPayment (bCrossTwoPlus)

theorem newPayment_le_balance : newPayment ≤ TailWholeCommonLog.collected-TailWholeCommonLog.lower-TailWholeCommonLog.recovery := by
  obtain ⟨hxm,hxp,hym,hyp⟩ := cross_arguments
  obtain ⟨hbxm,hbxp,hbym,hbyp⟩ := b_cross_arguments
  have h0 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 2)) TailWholeCommonLog.coeffTwo_sign
  have h1 := negative_payment TailWholeCommonLog.coeffThreeHalf_sign (by norm_num : (1:ℝ) ≤ 3/2)
  have h2 := ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 1127/600)
  have h3 := negative_payment TailWholeCommonLog.coeffA_sign (by norm_num : (1:ℝ) ≤ 3884129/3606400)
  have h4 := negative_payment TailWholeCommonLog.coeffAC_sign (by norm_num : (1:ℝ) ≤ 4508/2927)
  have h5 := negative_payment (neg_nonpos.mpr TailWholeCommonLog.coeffB_sign) (by norm_num : (1:ℝ) ≤ 2400/2381)
  have h6 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 4508/3981)) TailWholeCommonLog.coeffD_sign
  have h7 := negative_payment TailWholeCommonLog.coeffS_sign (by norm_num : (1:ℝ) ≤ 2254/1727)
  have h8 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 927/800)) TailWholeCommonLog.poleZero_sign
  have h9 := negative_payment TailWholeCommonLog.poleOne_sign (by norm_num : (1:ℝ) ≤ 727/600)
  have h10 := negative_payment TailWholeCommonLog.coeffAM_sign hxm
  have h11 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hxp) TailWholeCommonLog.coeffAP_sign
  have h12 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hym) TailWholeCommonLog.coeffTM_sign
  have h13 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hyp) TailWholeCommonLog.coeffTP_sign
  have h14 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hbxm) TailWholeCommonLog.coeffBM_sign
  have h15 := negative_payment TailWholeCommonLog.coeffBP_sign hbxp
  have h16 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hbym) TailWholeCommonLog.coeffDM_sign
  have h17 := negative_payment TailWholeCommonLog.coeffDP_sign hbyp
  unfold newPayment TailWholeCommonLog.collected TailWholeCommonLog.lower TailWholeCommonLog.recovery
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17]

theorem newPayment_pos : 0 < newPayment := by
  obtain ⟨hxm,_,_,_⟩ := cross_arguments
  obtain ⟨_,hbxp,_,hbyp⟩ := b_cross_arguments
  have hc : TailWholeCommonLog.coeffThreeHalf < 0 := by
    rw [TailWholeCommonLog.coeffThreeHalf_exact]
    norm_num
  have hp := mul_pos (neg_pos.mpr hc) (splitPayment_pos (by norm_num : (1:ℝ) < 3/2))
  have h3 := mul_nonneg (neg_nonneg.mpr TailWholeCommonLog.coeffA_sign) (splitPayment_nonneg (by norm_num : (1:ℝ) ≤ 3884129/3606400))
  have h4 := mul_nonneg (neg_nonneg.mpr TailWholeCommonLog.coeffAC_sign) (splitPayment_nonneg (by norm_num : (1:ℝ) ≤ 4508/2927))
  have h5 := mul_nonneg (neg_nonneg.mpr (neg_nonpos.mpr TailWholeCommonLog.coeffB_sign)) (splitPayment_nonneg (by norm_num : (1:ℝ) ≤ 2400/2381))
  have h7 := mul_nonneg (neg_nonneg.mpr TailWholeCommonLog.coeffS_sign) (splitPayment_nonneg (by norm_num : (1:ℝ) ≤ 2254/1727))
  have h9 := mul_nonneg (neg_nonneg.mpr TailWholeCommonLog.poleOne_sign) (splitPayment_nonneg (by norm_num : (1:ℝ) ≤ 727/600))
  have h10 := mul_nonneg (neg_nonneg.mpr TailWholeCommonLog.coeffAM_sign) (splitPayment_nonneg hxm)
  have h15 := mul_nonneg (neg_nonneg.mpr TailWholeCommonLog.coeffBP_sign) (splitPayment_nonneg hbxp)
  have h17 := mul_nonneg (neg_nonneg.mpr TailWholeCommonLog.coeffDP_sign) (splitPayment_nonneg hbyp)
  unfold newPayment
  linarith only [hp,h3,h4,h5,h7,h9,h10,h15,h17]

def finite : ℝ := max (max
  (WholeCommonLog.lower+TailEndpointPayment.recovery+oldPayment)
  (TailWholeCommonLog.lower+TailWholeCommonLog.recovery+newPayment))
  (F1TailFixedWhole.paid+oldPayment)

theorem finite_le_collected : finite ≤ TailWholeCommonLog.collected := by
  have hm : 0 ≤ ActualTailFinite.mass := by
    rw [← ActualTailFinite.mass_exact]
    exact ActualTailConsumption.mass_bounds.1
  have ho : WholeCommonLog.lower+TailEndpointPayment.recovery+oldPayment ≤ TailWholeCommonLog.collected := by
    rw [← TailWholeCommonLog.collected_exact]
    linarith only [oldPayment_le_balance,hm]
  have hn : TailWholeCommonLog.lower+TailWholeCommonLog.recovery+newPayment ≤ TailWholeCommonLog.collected := by
    linarith only [newPayment_le_balance]
  have hp : F1TailFixedWhole.paid+oldPayment ≤ TailWholeCommonLog.collected := by
    rw [← TailWholeCommonLog.collected_exact]
    unfold F1TailFixedWhole.paid
    linarith only [oldPayment_le_balance,F1TailFixedWhole.payment_le_mass]
  exact max_le (max_le ho hn) hp

def endpointBalance : ℝ := TailWholeCommonLog.collected-finite

theorem endpointBalance_nonneg : 0 ≤ endpointBalance :=
  sub_nonneg.mpr finite_le_collected

theorem finite_firstMain_exact : Wu08TerminalAlignment.firstMain =
    8*(finite+endpointBalance+TailEndpointPayment.tailRemainder+FreshCommonLog.eLoss) := by
  rw [TailWholeCommonLog.firstMain_exact]
  unfold endpointBalance
  ring

theorem finite_le_actual : 8*finite ≤ Wu08TerminalAlignment.firstMain := by
  rw [finite_firstMain_exact]
  linarith only [endpointBalance_nonneg,TailEndpointPayment.tailRemainder_nonneg,
    FreshCommonLog.eLoss_nonneg]

theorem actual_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (8*finite-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  have he : 0 < Wu08TerminalAlignment.firstMain-8*finite+ε := by
    linarith only [finite_le_actual,hε]
  obtain ⟨T,hT,hcount⟩ := Wu08TerminalAlignment.first_actual_count he
  refine ⟨T,hT,?_⟩
  intro N hN hEven
  convert hcount N hN hEven using 1
  ring

theorem previous_payment_le_payment {x : ℝ} (hx : 1 ≤ x) :
    F1SignedUpperFTC.splitPayment x ≤ splitPayment x := old_splitPayment_le hx

theorem previous_payment_lt_payment {x : ℝ} (hx : 1 < x) :
    F1SignedUpperFTC.splitPayment x < splitPayment x := old_splitPayment_lt hx

end CliF1AffinePaymentParent
