import WR2XiExactLoss

/-! Positivity after removing exactly the illegal Gamma5 region. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve MotherPair
open WuPaper.RMapMMatrix
open Wu2004MeanValue.GammaFiveLossBudget
open scoped Interval

theorem original66_eq_triangle (f : ℝ → ℝ) (p : SecondFunctionalParameters) :
    original66 f p = triangleGain p.S (1/p.kappa2) false f := by
  unfold original66 triangleGain
  simp only [Bool.false_eq_true, false_implies, if_true]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [show p.S - p.S*x - p.S*u = p.S*(1-x-u) by ring]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem gamma5_legal_profile_nonneg (r : Fin 4) {f : ℝ → ℝ}
    (hf : ∀ t ∈ Icc (1:ℝ) 3, 0 ≤ f t) :
    0 ≤ triangleGain (rowParameters r).1 (rowParameters r).2 true f := by
  have hp : 0 < (rowParameters r).1 ∧ 1/(rowParameters r).1 ≤ (rowParameters r).2 ∧
      1 ≤ (rowParameters r).1*(1-2*(rowParameters r).2) ∧ (rowParameters r).1 ≤ 5 := by
    fin_cases r <;> norm_num [rowParameters]
  unfold triangleGain
  apply intervalIntegral.integral_nonneg hp.2.1
  intro x hx
  apply intervalIntegral.integral_nonneg hx.2
  intro u hu
  split_ifs
  · have hx0 : 0 < x := (one_div_pos.mpr hp.1).trans_le hx.1
    have hu0 : 0 < u := hx0.trans_le hu.1
    have hxs := (div_le_iff₀ hp.1).mp hx.1
    have hus := (div_le_iff₀ hp.1).mp (hx.1.trans hu.1)
    have hb := mul_nonneg hp.1.le
      (show 0 ≤ 2*(rowParameters r).2-x-u by linarith [hx.2,hu.2])
    have hv : (rowParameters r).1*(1-x-u) ∈ Icc (1:ℝ) 3 :=
      ⟨by nlinarith [hp.2.2.1], by nlinarith [hp.2.2.2]⟩
    apply div_nonneg (hf _ hv)
    apply mul_nonneg (mul_nonneg hx0.le hu0.le)
    nlinarith [hv.1]
  · exact le_rfl

/-- The corrected integral is nonnegative, proved through the legal triangle. -/
theorem Xi2_corrected_integral_nonneg (r : Fin 4) {f : ℝ → ℝ}
    (hi : IntervalIntegrable f volume 1 3) (hm : Measurable f)
    (hb : ∀ t, |f t| ≤ 1) (hf : ∀ t ∈ Icc (1:ℝ) 3, 0 ≤ f t) :
    0 ≤ (∫ t in (1:ℝ)..3, f t * Xi2 (gamma5OriginalRow r) t) -
      (∫ t in (1:ℝ)..3, f t * generalKernel (rowParameters r).1 (rowParameters r).2 t) := by
  have hp : PropositionFourGeometry (gamma5OriginalRow r) := original_four_rows_qualified r
  rw [Xi2_original_identity hi hp]
  obtain ⟨hs, hS, hS5, hk1, hk2, hk3, hsS, h2S, h3S, hr2, hr3⟩ :=
    second_parameter_bounds hp
  have hj1 := originalJ_nonneg hf hs hS hS5 hsS hp.2.2.2.2.2.2.2.2.1
  have hj2 := originalJ_nonneg hf hk2 hS hS5 h2S hr2
  have hj3 := originalJ_nonneg hf hk3 hS hS5 h3S hr3
  have he1 := (profiles_nonneg hf).2.2 _ ⟨hS, hS5⟩
  have he2 := (profiles_nonneg hf).2.2 _ ⟨hk1, hp.2.2.2.2.2.2.2.1.trans hS5⟩
  have h67 := original67_nonneg hf hp
  have h68 := original68_nonneg hf hp
  have hl := gamma5_legal_profile_nonneg r hf
  have hd := gamma5_triangle_loss_identity r f hm hb
  have h66 := original66_eq_triangle f (gamma5OriginalRow r)
  have hparams := gamma5_original_row_parameters r
  rw [hparams.1,hparams.2] at h66
  linarith only [hj1,hj2,hj3,he1,he2,h67,h68,hl,hd,h66]

end WuPaper.R2Xi
