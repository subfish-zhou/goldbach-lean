import AnalyticTotalThreshold

namespace Wu2008DoubleSieve.TotalEndpointComparison
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientUpperEnclosure (a b s)
open FixedCoefficientHLowerEnclosure (c)
open scoped Interval
noncomputable section

/-- The original affine coordinate, not a new parameter. -/
def H : ℝ := 1/(2*a)-1
def gap (w : ℝ) : ℝ := -w^3/12+3*w^2/4-5*w/2+4-4/w+4/w^2-8/(3*w^3)
def A1 : ℝ := 256/3-64/H+64/H^2-128/(3*H^3)
def A2 : ℝ := -160/3+64/H-128/(3*H^2)
def A3 : ℝ := 64/3-128/(3*H)

theorem H_pos : 0 < H := by norm_num [H,a,truncatedSixthLowerAlpha]

theorem original_gap {w : ℝ} (hw : w ≠ 0) :
    VariableUpperEnvelope.cubic (w+1)-SharedRationalEnvelope.p (w+1) = gap w := by
  unfold VariableUpperEnvelope.cubic SharedRationalEnvelope.p lowerLog gap
  have he : w+1-2+1=w := by ring
  rw [he]
  field_simp
  ring

/-- Finite partial fractions of the complete existing rational density. -/
theorem partial_fractions {w : ℝ} (hw : w ≠ 0) (hp : w+1 ≠ 0)
    (hm : H-w ≠ 0) :
    (-8/(w+1)+16/(H-w))*gap w =
      2*w^2+(4*H/3-56/3)*w+(200/3-12*H+4*H^2/3)+
      A1/w+A2/w^2+A3/w^3-144/(w+1)+16*gap H/(H-w) := by
  unfold gap A1 A2 A3
  field_simp [hw,hp,hm,H_pos.ne']
  ring

def primitive (w : ℝ) : ℝ :=
  2*w^3/3+(2*H/3-28/3)*w^2+(200/3-12*H+4*H^2/3)*w+
  A1*log w-A2/w-A3/(2*w^2)-144*log (w+1)-16*gap H*log (H-w)

theorem primitive_derivative {w : ℝ} (hw : w ≠ 0) (hp : w+1 ≠ 0)
    (hm : H-w ≠ 0) :
    HasDerivAt primitive ((-8/(w+1)+16/(H-w))*gap w) w := by
  rw [partial_fractions hw hp hm]
  have hi := hasDerivAt_id w
  have h := (((((((((hi.pow 3).const_mul 2).div_const 3).add
    ((hi.pow 2).const_mul (2*H/3-28/3))).add
    (hi.const_mul (200/3-12*H+4*H^2/3))).add
    ((hasDerivAt_log hw).const_mul A1)).sub
    ((hasDerivAt_const w A2).div hi hw)).sub
    ((hasDerivAt_const w A3).div ((hi.pow 2).const_mul 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hw)))).sub
    (((hi.add_const 1).log hp).const_mul 144)).sub
    ((((hasDerivAt_const w H).sub hi).log hm).const_mul (16*gap H))
  convert h using 1 <;> first | rfl | (dsimp; field_simp; ring)

theorem coordinate_geometry {t : ℝ} (ht : t ∈ Icc (c 4) s) :
    0 < Phase22.u t-1 ∧ 0 < Phase22.u t ∧ 0 < H-(Phase22.u t-1) := by
  obtain ⟨ht0,_,hu,_⟩ := SharedRationalEnvelope.geometry ht
  have ha := truncatedSixthLower_parameters.1
  have he : H-(Phase22.u t-1)=t/a := by
    unfold H Phase22.u
    field_simp
    ring
  refine ⟨by linarith,by linarith,?_⟩
  rw [he]
  exact div_pos ht0 ha

theorem pullback_derivative {t : ℝ} (ht : t ∈ Icc (c 4) s) :
    HasDerivAt (fun t => -primitive (Phase22.u t-1))
      (SharedRationalEnvelope.gainDensity t) t := by
  obtain ⟨hw,hp,hm⟩ := coordinate_geometry ht
  have ha := truncatedSixthLower_parameters.1
  have hd := primitive_derivative hw.ne'
    (by simpa only [sub_add_cancel] using hp.ne') hm.ne'
  have hc := ((((hasDerivAt_const t (1/2 : ℝ)).sub (hasDerivAt_id t)).div_const a).sub_const 1)
  have hh := (hd.comp t hc).neg
  have hg := original_gap hw.ne'
  rw [sub_add_cancel] at hg
  have hh' : HasDerivAt (fun t => -primitive (Phase22.u t-1))
      (-((-8/(Phase22.u t-1+1)+16/(H-(Phase22.u t-1)))*
        gap (Phase22.u t-1)*((0-1)/a))) t := hh
  convert hh' using 1
  unfold SharedRationalEnvelope.gainDensity SharedRationalEnvelope.weight
  rw [hg]
  unfold H Phase22.u
  obtain ⟨ht0,hdt,_,_⟩ := SharedRationalEnvelope.geometry ht
  have hn : 1-2*t ≠ 0 := by linarith
  field_simp [ha.ne',ht0.ne',hdt.ne',hn]
  ring_nf
  field_simp [show 1-t*2 ≠ 0 by linarith]
  ring

/-- Exact FTC of the entire shared integral on its original window. -/
theorem shared_ftc : SharedRationalEnvelope.deltaShared = primitive 3-primitive 2 := by
  have hi : IntervalIntegrable SharedRationalEnvelope.gainDensity volume (c 4) s :=
    SharedRationalEnvelope.density_continuous.intervalIntegrable_of_Icc
    SharedRationalEnvelope.window_order.2.1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => pullback_derivative
      (uIcc_of_le SharedRationalEnvelope.window_order.2.1 ▸ ht)) hi
  have h4 : Phase22.u (c 4)-1=3 := by
    norm_num [Phase22.u,a,c,truncatedSixthLowerAlpha]
  have h3 : Phase22.u s-1=2 := by
    norm_num [Phase22.u,a,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  rw [h4,h3] at he
  unfold SharedRationalEnvelope.deltaShared
  linarith only [he]

/-- The rational part of the exact shared endpoint difference. -/
def rationalShared : ℝ := 98/3-26*H/3+4*H^2/3+A2/6+5*A3/72

theorem shared_log_endpoint : SharedRationalEnvelope.deltaShared = rationalShared+
    A1*log (3/2)-144*log (4/3)-16*gap H*log ((H-3)/(H-2)) := by
  rw [shared_ftc]
  have h2 : H-2 ≠ 0 := by norm_num [H,a,truncatedSixthLowerAlpha]
  have h3 : H-3 ≠ 0 := by norm_num [H,a,truncatedSixthLowerAlpha]
  rw [log_div (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
    log_div (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0),
    log_div h3 h2]
  unfold primitive rationalShared
  norm_num
  ring

def rationalJoint : ℝ := rationalShared-
  (32-SignedTotalCorrelation.jTwo)*lowerLog 2-44*lowerLog (4/3)-
  8*GConvexChord.C*lowerLog (5/4)

/-- Opposite occurrences are collected before any signed log enclosure. -/
theorem shared_residual_joint : SharedRationalEnvelope.deltaShared+
    SignedTotalCorrelation.retainedResidual = rationalJoint+
    (A1+32-SignedTotalCorrelation.jTwo)*log 2-(A1+100)*log (4/3)+
    8*GConvexChord.C*log (5/4)-16*gap H*log ((H-3)/(H-2)) := by
  rw [shared_log_endpoint]
  have hl : log (3/2) = log 2-log (4/3) := by
    rw [log_div (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
      log_div (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
    have h4 : log (4:ℝ)=2*log 2 := by
      rw [show (4:ℝ)=2*2 by norm_num,log_mul (by norm_num) (by norm_num)]
      ring
    rw [h4]
    ring
  rw [hl]
  unfold rationalJoint SignedTotalCorrelation.retainedResidual
    SignedTotalCorrelation.e2 SignedTotalCorrelation.e43 SignedTotalCorrelation.e54
  ring

/-- All non-common sixth endpoint terms stay exact. -/
def sixthRest : ℝ := Phase25.endpointRational+Phase25.qz1*log Phase25.ratioz+
  Phase25.qb1*log Phase25.ratiob+Phase25.qm1*log Phase25.ratiom+
  Phase25.qp1*log Phase25.ratiop

def D : ℝ := log (b/a)
def quad : ℝ := 2*SharpMassBalance.fifthDensity+4*FifthClassicalShape.k*b
def lin : ℝ := 4*Phase25.kx-4*FifthClassicalShape.k*(b-a)

theorem joint_endpoint : AnalyticTotalThreshold.fifthEndpoint+
    AnalyticTotalThreshold.sixthEndpoint = quad*D^2+lin*D+4*sixthRest := by
  unfold AnalyticTotalThreshold.fifthEndpoint AnalyticTotalThreshold.sixthEndpoint
  rw [Phase25.endpoint_exact]
  have hl : log b-log a=log (b/a) :=
    (log_div (by norm_num [b,truncatedSixthLowerBeta])
      (by norm_num [a,truncatedSixthLowerAlpha])).symm
  rw [hl]
  unfold quad lin D sixthRest
  ring

/-- Every original residual and the complete shared FTC remain in this total. -/
def rest : ℝ := Phase23.modelBase-GConvexChord.rationalG-
  UnroundedPayments.weightedJUpper+SignedTotalCorrelation.correlationGain+
  SignedTotalCorrelation.retainedResidual+(primitive 3-primitive 2)+
  4*sixthRest+47/481250-Phase24.newFour

def affineTotal : ℝ :=
  (rest+(2*quad*FifthClassicalShape.ell+lin)*D-quad*FifthClassicalShape.ell^2)/4+
  Phase20.rawPsi+Phase18.g18+(2*BaseHGain.originalGain+fifthHGain/4)

/-- Exact positive square left after joint, not separate, log comparison. -/
theorem total_square_identity : AnalyticTotalThreshold.coefficient-affineTotal =
    quad/4*(D-FifthClassicalShape.ell)^2 := by
  have he := joint_endpoint
  unfold AnalyticTotalThreshold.coefficient AnalyticTotalThreshold.classicalEndpoint
    AnalyticTotalThreshold.signedModel affineTotal rest
  rw [← shared_ftc]
  nlinarith only [he]

theorem quad_pos : 0 < quad := by
  have hd := UnroundedPayments.fifth_payment_positive.1
  have hk : 0 < FifthClassicalShape.k :=
    div_pos FifthClassicalShape.c_pos (sq_pos_of_pos truncatedSixthLower_parameters.1)
  have hb : 0 < b := by norm_num [b,truncatedSixthLowerBeta]
  unfold quad
  positivity

/-- A strict unconditional analytic comparison for the same full coefficient. -/
theorem affineTotal_lt_coefficient : affineTotal < AnalyticTotalThreshold.coefficient := by
  have hl : FifthClassicalShape.ell < D :=
    UnroundedPayments.lowerLog_lt_log
      (by norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have hp := mul_pos (div_pos quad_pos (by norm_num : (0:ℝ)<4))
    (sq_pos_of_pos (sub_pos.mpr hl))
  rw [← total_square_identity] at hp
  exact sub_pos.mp hp

/-- This joint affine comparison strictly dominates the previous full residual
certificate even after its original raw Psi has already been restored. -/
theorem restored_certificate_lt_affineTotal :
    SharedRationalPayment.residualCoefficient+Phase20.psiPaymentLoss < affineTotal := by
  have hl : FifthClassicalShape.ell < D :=
    UnroundedPayments.lowerLog_lt_log
      (by norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  obtain ⟨hd,he⟩ := UnroundedPayments.fifth_payment_positive
  have hk : 0 < FifthClassicalShape.k :=
    div_pos FifthClassicalShape.c_pos (sq_pos_of_pos truncatedSixthLower_parameters.1)
  have hb : 0 < b := by norm_num [b,truncatedSixthLowerBeta]
  have hm : 0 < b*FifthClassicalShape.ell-(b-a) := by
    norm_num [FifthClassicalShape.ell,lowerLog,a,b,
      truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hell : 0 < FifthClassicalShape.ell := he
  have hslope : 0 < 2*quad*FifthClassicalShape.ell-4*FifthClassicalShape.k*(b-a) := by
    unfold quad
    have hde := mul_pos hd hell
    have hbe := mul_pos hb hell
    have hkm := mul_pos hk (show 0 < 2*b*FifthClassicalShape.ell-(b-a) by linarith)
    nlinarith only [hde,hkm]
  have hprod := mul_pos hslope (sub_pos.mpr hl)
  have h5 : AnalyticTotalThreshold.fifthEndpoint-FifthClassicalShape.payment-
      quad*(D-FifthClassicalShape.ell)^2 =
      (2*quad*FifthClassicalShape.ell-4*FifthClassicalShape.k*(b-a))*
        (D-FifthClassicalShape.ell) := by
    unfold AnalyticTotalThreshold.fifthEndpoint FifthClassicalShape.payment
      UnroundedPayments.fifthRational FifthClassicalShape.gain quad D
    rw [log_div (by norm_num [b,truncatedSixthLowerBeta])
      (by norm_num [a,truncatedSixthLowerAlpha])]
    unfold FifthClassicalShape.ell
    ring
  have hret := AnalyticTotalThreshold.retained_replacements_identity
  have hsq := total_square_identity
  have h6 := AnalyticTotalThreshold.newSixth_le_endpoint
  nlinarith only [hprod,h5,hret,hsq,h6]

end
end Wu2008DoubleSieve.TotalEndpointComparison
