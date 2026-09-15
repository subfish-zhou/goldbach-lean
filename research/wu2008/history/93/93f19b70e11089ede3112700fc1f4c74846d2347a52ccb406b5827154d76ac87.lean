import WE10FourCross

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open FourRoughClosedMass ClassicalLogFourBounds Wu08OriginalFourWeights
open WuTarget.W13

namespace WuTarget.E10Four

theorem rebateCoeff_pos : 0 < rebateCoeff := by
  have hg := cross_geometry ⟨le_refl alpha, fixed_geometry.2.2.1⟩
  have hb := hg.2.1
  unfold rebateCoeff kappa
  exact div_pos (mul_pos (by norm_num)
    (div_pos fixed_geometry.2.1 hg.2.2.2)) (by positivity)

theorem rebate_nonneg {x : ℝ} (hx : x ∈ Icc alpha beta) : 0 ≤ rebate x := by
  have hl : 0 ≤ log x-log alpha :=
    sub_nonneg.mpr (log_le_log fixed_geometry.2.1 hx.1)
  exact div_nonneg
    (mul_nonneg (mul_nonneg rebateCoeff_pos.le hl) (sq_nonneg _))
    (cross_geometry hx).1.le

theorem outer11_rebate {x : ℝ} (hx : x ∈ Icc alpha beta) :
    regularOuter11 x+rebate x ≤ (4/7)*crossLog*
      (FourLogAffine.C0*FourLogAffine.ell x^2/2+
        FourLogAffine.ell x^3/(3*beta))/x := by
  have hx0 := (cross_geometry hx).1
  have hb := (cross_geometry hx).2.1
  have he := FourLogAffine.ell_nonneg hx.1 hx.2
  let B := FourLogAffine.C0*FourLogAffine.ell x^2/2+
    FourLogAffine.ell x^3/(3*beta)
  have hB : FourLogAffine.ell x^2/(2*beta) ≤ B := by
    have hm := mul_le_mul_of_nonneg_right FourLogAffine.C0_lower (sq_nonneg (FourLogAffine.ell x))
    have hn : 0 ≤ FourLogAffine.ell x^3/(3*beta) := by positivity
    dsimp only [B]
    ring_nf at hm hn ⊢
    linarith only [hm, hn]
  have hB0 : 0 ≤ B := (by positivity : 0 ≤ FourLogAffine.ell x^2/(2*beta)).trans hB
  have hr : rebate x ≤ (4/7)*crossLoss x*B/x := by
    have hid : rebate x = (4/7)*crossLoss x*(FourLogAffine.ell x^2/(2*beta))/x := by
      unfold rebate rebateCoeff crossLoss FourLogAffine.ell
      ring
    rw [hid]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hB
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4/7) (crossLoss_nonneg hx))) hx0.le
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (cross_correlation hx) hB0)
      (by norm_num : (0 : ℝ) ≤ 4/7)) hx0.le
  have ho := outer11_correlated hx
  change regularOuter11 x ≤ (4/7)*cross x*B/x at ho
  change regularOuter11 x+rebate x ≤ (4/7)*crossLog*B/x
  ring_nf at hc ho hr ⊢
  linarith only [hc, ho, hr]

theorem outer_pair_rebate {x : ℝ} (hx : x ∈ Icc alpha beta) :
    regularOuter10 x+regularOuter11 x+rebate x ≤ profile x := by
  have hx0 := (cross_geometry hx).1
  have hb := (cross_geometry hx).2.1
  have hE := FourLogAffine.ell_nonneg hx.1 hx.2
  have hC := FourLogAffine.C0_pos
  have hw := log_caps.2.2.1.trans FourLogAffine.fixed_log_bounds.2.2.2.2
  have h3 := mul_le_mul_of_nonneg_right C0_le_upper (pow_nonneg hE 3)
  have h2 := mul_le_mul_of_nonneg_right C0_le_upper (pow_nonneg hE 2)
  have hten :
      (4/7)*(FourLogAffine.C0*FourLogAffine.ell x^3/6+
        FourLogAffine.ell x^4/(8*beta))/x ≤
      (4/7)*(c0Upper*FourLogAffine.ell x^3/6+
        FourLogAffine.ell x^4/(8*beta))/x := by
    apply div_le_div_of_nonneg_right _ hx0.le
    linarith only [h3]
  have hbracket :
      FourLogAffine.C0*FourLogAffine.ell x^2/2+
        FourLogAffine.ell x^3/(3*beta) ≤
      c0Upper*FourLogAffine.ell x^2/2+
        FourLogAffine.ell x^3/(3*beta) := by linarith only [h2]
  have hbracket0 :
      0 ≤ FourLogAffine.C0*FourLogAffine.ell x^2/2+
        FourLogAffine.ell x^3/(3*beta) := by positivity
  have heleven := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (mul_le_mul FourLogAffine.fixed_log_bounds.2.2.2.2 hbracket hbracket0 hw)
      (show (0 : ℝ) ≤ 4/7 by norm_num)) hx0.le
  have h10 := (FourLogAffine.outer10_upper hx.1 hx.2).trans hten
  have h11 := outer11_rebate hx
  simp only [profile, a2, a3, a4, tail, FourLogAffine.ell] at h10 h11 heleven ⊢
  ring_nf at h10 h11 heleven ⊢
  linarith only [h10, h11, heleven]

theorem rebate_eq (x : ℝ) :
    rebate x = rebateCoeff*(tailLog*tail 2 x-tail 3 x) := by
  unfold rebate tailLog tail
  ring

theorem rebate_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable rebate volume a b := by
  have he : rebate = fun x => rebateCoeff*(tailLog*tail 2 x-tail 3 x) :=
    funext rebate_eq
  rw [he]
  exact (((tail_continuousOn 2 ha hab).intervalIntegrable.const_mul tailLog).sub
    (tail_continuousOn 3 ha hab).intervalIntegrable).const_mul rebateCoeff

theorem rebate_integral :
    (∫ x in alpha..beta, rebate x) = rebateCoeff*tailLog^4/12 := by
  have hab := fixed_geometry.2.2.1
  have h2 := (tail_continuousOn 2 fixed_geometry.2.1 hab).intervalIntegrable (μ := volume)
  have h3 := (tail_continuousOn 3 fixed_geometry.2.1 hab).intervalIntegrable (μ := volume)
  have ht (n : ℕ) :
      (∫ x in alpha..beta, tail n x) = tailLog^(n+1)/((n : ℝ)+1) := by
    simpa only [one_mul,tail,tailLog] using
      integral_log_tail (C := (1 : ℝ)) fixed_geometry.2.1 hab n
  rw [show rebate = fun x => rebateCoeff*(tailLog*tail 2 x-tail 3 x) from funext rebate_eq,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (h2.const_mul tailLog) h3,
    intervalIntegral.integral_const_mul, ht 2, ht 3]
  norm_num only [Nat.cast_ofNat]
  ring

theorem original_pair_rebate :
    original10+original11+(36/5)*(∫ x in alpha..beta, rebate x) ≤
      a2*moment 2+a3*moment 3+a4*moment 4 := by
  have hc0 := geometry.1.trans_le geometry.2.1
  have hs10 := weighted_integrable regularOuter10_continuous
  have hs11 := weighted_integrable regularOuter11_continuous
  change IntervalIntegrable (fun x => regularOuter10 x/(1-x)) volume alpha cut at hs10
  change IntervalIntegrable (fun x => regularOuter11 x/(1-x)) volume alpha cut at hs11
  have hl10 := regularOuter10_continuous.intervalIntegrable (μ := volume) cut beta
  have hl11 := regularOuter11_continuous.intervalIntegrable (μ := volume) cut beta
  have hrs := rebate_integrable geometry.1 geometry.2.1
  have hrl := rebate_integrable hc0 geometry.2.2.1
  have hs := intervalIntegral.integral_mono_on geometry.2.1
    ((hs10.add hs11).add hrs) weighted_profile_integrable (fun x hx => by
      have hxb : x ∈ Icc alpha beta := ⟨hx.1,hx.2.trans geometry.2.2.1⟩
      have hden : 0 < 1-x := by linarith only [hx.2,geometry.2.2.2]
      have hr := rebate_nonneg hxb
      have hrdiv : rebate x ≤ rebate x/(1-x) := by
        apply (le_div_iff₀ hden).mpr
        have hx0 := (cross_geometry hxb).1
        nlinarith only [mul_nonneg hr hx0.le]
      have hp := div_le_div_of_nonneg_right (outer_pair_rebate hxb) hden.le
      simp only [add_div] at hp
      linarith only [hp,hrdiv])
  have hl := intervalIntegral.integral_mono_on geometry.2.2.1
    ((hl10.add hl11).add hrl) (profile_integrable hc0 geometry.2.2.1)
    (fun x hx => outer_pair_rebate ⟨geometry.2.1.trans hx.1,hx.2⟩)
  rw [intervalIntegral.integral_add (hs10.add hs11) hrs,
    intervalIntegral.integral_add hs10 hs11, weighted_profile_integral] at hs
  rw [intervalIntegral.integral_add (hl10.add hl11) hrl,
    intervalIntegral.integral_add hl10 hl11,
    profile_integral hc0 geometry.2.2.1] at hl
  have hr0 : 0 ≤ ∫ x in cut..beta, rebate x :=
    intervalIntegral.integral_nonneg geometry.2.2.1
      (fun x hx => rebate_nonneg ⟨geometry.2.1.trans hx.1,hx.2⟩)
  rw [← intervalIntegral.integral_add_adjacent_intervals hrs hrl]
  unfold original10 original11 original moment
  dsimp only [cut] at hs hl hr0 ⊢
  ring_nf at hs hl hr0 ⊢
  linarith only [hs,hl,hr0]

end WuTarget.E10Four
