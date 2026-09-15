import E05SixthMajorKernel

noncomputable section
open Real Set MeasureTheory
open Wu2008DoubleSieve
open Wu2008DoubleSieve.PositiveSixthFTC
open Wu2008DoubleSieve.DynamicSixthEnvelope
open Wu2008DoubleSieve.SharpLogRecurrence
open Wu2008DoubleSieve.SharpMassBalance
open Wu2008DoubleSieve.ClassicalLossBottleneck
open scoped Interval

namespace WuTarget.E05SixthMajor

def outerCredit : ℝ := 4*Phase25.kx*E05Sixth.fifthLogTerm (b/a)

theorem endpoint_payment :
    Phase25.newSixth+outerCredit ≤
      4*(Phase25.outerPrimitive b-Phase25.outerPrimitive a) := by
  have h0 := log_lower (t := Phase25.ratioz) (by
    norm_num [Phase25.ratioz,Phase25.polez,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have h1 := log_lower (t := Phase25.ratiob/Phase25.ratioz) (by
    norm_num [Phase25.ratiob,Phase25.ratioz,Phase25.polez,Phase25.poleb,
      a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have h2 := log_upper (t := Phase25.ratioz/Phase25.ratiom) (by
    norm_num [Phase25.ratioz,Phase25.ratiom,Phase25.polez,Phase25.polem,
      a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have h3 := log_lower (t := Phase25.ratiop/Phase25.ratioz) (by
    norm_num [Phase25.ratiop,Phase25.ratioz,Phase25.polez,Phase25.polep,
      a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have h4 := E05Sixth.log_fifth_lower (t := b/a) (by
    norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have nz : Phase25.ratioz ≠ 0 := by
    norm_num [Phase25.ratioz,Phase25.polez,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have nb : Phase25.ratiob ≠ 0 := by
    norm_num [Phase25.ratiob,Phase25.poleb,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have nm : Phase25.ratiom ≠ 0 := by
    norm_num [Phase25.ratiom,Phase25.polem,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have np : Phase25.ratiop ≠ 0 := by
    norm_num [Phase25.ratiop,Phase25.polep,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  rw [log_div nb nz] at h1
  rw [log_div nz nm] at h2
  rw [log_div np nz] at h3
  have h0p := mul_le_mul_of_nonneg_left h0 (show 0 ≤ Phase25.kx by norm_num [Phase25.kx])
  have h1p := mul_le_mul_of_nonneg_left h1 (show 0 ≤ Phase25.qb1 by norm_num [Phase25.qb1])
  have h2p := mul_le_mul_of_nonneg_left h2 (show 0 ≤ Phase25.qm1 by norm_num [Phase25.qm1])
  have h3p := mul_le_mul_of_nonneg_left h3 (show 0 ≤ Phase25.qp1 by norm_num [Phase25.qp1])
  have h4p := mul_le_mul_of_nonneg_left h4 (show 0 ≤ Phase25.kx by norm_num [Phase25.kx])
  rw [Phase25.endpoint_exact]
  unfold Phase25.newSixth outerCredit
  nlinarith only [h0p,h1p,h2p,h3p,h4p,
    congrArg (fun t => t*log Phase25.ratioz) Phase25.residue_sum]

theorem full_inner_payment {x : ℝ} (hx : x ∈ Icc a b) :
    Phase25.rationalInner (1/2-x)+innerCorrection x+densityInner x ≤
      ∫ y in b..s, sixthLogRegular x y := by
  have hc : Continuous (fun y : ℝ => sixthLogRegular x y) :=
    sixth_log_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
  have hiCorrection : IntervalIntegrable (densityCorrection x) volume b (lam-x) :=
    (by unfold densityCorrection; fun_prop : Continuous (densityCorrection x)).intervalIntegrable _ _
  have hi := intervalIntegral.integral_mono_on (μ := volume) (moving_geometry hx).1
    ((Phase25.inner_integrable hx).add hiCorrection) (hc.intervalIntegrable b (lam-x))
    (fun y hy => density_correction_paid hx hy)
  rw [intervalIntegral.integral_add (Phase25.inner_integrable hx) hiCorrection,
    Phase25.inner_ftc hx,density_inner_ftc] at hi
  have hn : 0 ≤ ∫ y in (lam-x)..s, sixthLogRegular x y :=
    intervalIntegral.integral_nonneg (moving_geometry hx).2
      (fun y _ => sixth_log_nonnegative x y)
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable b (lam-x)) (hc.intervalIntegrable (lam-x) s)
  linarith only [hi,hn,he,inner_correction_paid hx]

theorem full_endpoint_payment :
    4*(Phase25.outerPrimitive b-Phase25.outerPrimitive a)+innerCredit+
      E05Sixth.sixthCredit+fifthExtraCredit+seventhCredit ≤ sixthLogIntegral := by
  have hc : Continuous (fun x : ℝ => ∫ y in b..s, sixthLogRegular x y) := by
    apply gamma5Gain_moving_integral (f := sixthLogRegular) sixth_log_continuous <;> fun_prop
  have hiInner : IntervalIntegrable innerCorrection volume a b :=
    (by unfold innerCorrection; fun_prop : Continuous innerCorrection).intervalIntegrable _ _
  have hiDensity : IntervalIntegrable densityInner volume a b :=
    (by unfold densityInner E05Sixth.correctionInner; fun_prop :
      Continuous densityInner).intervalIntegrable _ _
  have hi := intervalIntegral.integral_mono_on (μ := volume) geometry.2.1
    ((Phase25.rationalInner_integrable.add hiInner).add hiDensity) (hc.intervalIntegrable a b)
    (fun x hx => full_inner_payment hx)
  rw [intervalIntegral.integral_add (Phase25.rationalInner_integrable.add hiInner) hiDensity,
    intervalIntegral.integral_add Phase25.rationalInner_integrable hiInner,Phase25.outer_ftc] at hi
  unfold sixthLogIntegral
  linarith only [hi,inner_correction_ftc,density_outer_ftc]

def newCredit : ℝ := innerCredit+fifthExtraCredit+seventhCredit+outerCredit
def majorLower : ℝ := E05Sixth.sixthLower+newCredit

theorem majorLower_le_log : majorLower ≤ sixthLogIntegral := by
  unfold majorLower E05Sixth.sixthLower newCredit
  linarith only [full_endpoint_payment,endpoint_payment]

theorem majorLower_le_actual : majorLower ≤ Wu08TerminalAlignment.sixthMain := by
  have hr := sixth_recurrence_integral_cap.1
  change 0 ≤ Wu08TerminalAlignment.sixthMain-sixthLogIntegral at hr
  linarith only [majorLower_le_log,hr]

theorem target_arithmetic :
    (381/100:ℝ) ≤ 3783117/1000000+newCredit := by
  norm_num [newCredit,innerCredit,innerRate,innerDenom1,innerDenom2,
    fifthExtraCredit,seventhCredit,outerCredit,E05Sixth.denominatorCap,
    E05Sixth.fifthLogTerm,z0,Phase25.kx,a,b,lam,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem target_paid_locally : (381/100:ℝ) ≤ Wu08TerminalAlignment.sixthMain := by
  have hb := E05Sixth.sixthLower_bounds.1
  have ht := target_arithmetic
  have hp := majorLower_le_actual
  unfold majorLower at hp
  linarith only [hb,ht,hp]

end WuTarget.E05SixthMajor
