import FullSourceLog

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve Row4LogProfile

namespace FullSourceLog

/-- The exact original h-kernel is pointwise above this new fixed-mask kernel. -/
theorem original_kernel_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000)
    (z : ℝ × ℝ) : uniformKernel (1/1000) z ≤ truncatedSixthMassHKernel δ z :=
  (uniform_le_moving hδ.le hδhi z).trans (moving_lower hδ hδhi z)

/-- Full-domain comparison: no portion of the mask is silently removed. -/
theorem scaled_old_kernel_lower (z : ℝ × ℝ) :
    (300*H0)*FullAdmissibleSeed.uniformKernel (1/1000) z ≤ uniformKernel (1/1000) z := by
  unfold FullAdmissibleSeed.uniformKernel uniformKernel
  split_ifs with hz
  · have hz0 := region_mono (by norm_num : (0:ℝ) ≤ 1/1000) hz
    have hb := truncatedSixthLower_region_bounds (δ := 0) le_rfl hz0.1
    have hd := denominator_pos (δ := 0) le_rfl hz0
    calc
      _ = ((300*H0)*FullAdmissibleSeed.seed (truncatedSixthLowerS 0 z.1 z.2)) /
          (z.1*z.2*(truncatedSixthLowerC 0-z.1-z.2)) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (scaled_seed_lower hb.2.2.2.1) hd.le
  · simp only [mul_zero,le_refl]

theorem old_kernel_lower (z : ℝ × ℝ) :
    FullAdmissibleSeed.uniformKernel (1/1000) z ≤ uniformKernel (1/1000) z := by
  have hn := FullAdmissibleSeed.uniform_nonneg (by norm_num : (0:ℝ) ≤ 1/1000) z
  have hf : 1 ≤ 300*H0 := by linarith only [H0_margin]
  exact (le_mul_of_one_le_left hn hf).trans (scaled_old_kernel_lower z)

theorem gamma_scaled_lower : (300*H0)*FullAdmissibleSeed.Gamma6 ≤ GammaLog6 := by
  have ho := FullAdmissibleSeed.uniform_integrable (by norm_num : (0:ℝ) < 1/1000) le_rfl
  have hn := uniform_integrable (by norm_num : (0:ℝ) < 1/1000) le_rfl
  have hi := integral_mono (ho.const_mul (300*H0)) hn scaled_old_kernel_lower
  rw [integral_const_mul] at hi
  unfold GammaLog6 Gamma FullAdmissibleSeed.Gamma6 FullAdmissibleSeed.Gamma
  nlinarith only [hi]

/-- Strictness comes from the full source factor and the already-certified positive
old integral, not a new artificial subrectangle or a reused count strictness. -/
theorem gamma_strict_improvement : FullAdmissibleSeed.Gamma6 < GammaLog6 := by
  have hp : 0 < FullAdmissibleSeed.Gamma6 :=
    (by norm_num : (0:ℝ) < 1/1000).trans FullAdmissibleStrength.gamma6_magnitude
  have hf : 1 < 300*H0 := by linarith only [H0_margin]
  have hx : FullAdmissibleSeed.Gamma6 < (300*H0)*FullAdmissibleSeed.Gamma6 := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hf hp
  exact hx.trans_le gamma_scaled_lower

theorem gamma_dominates : FullAdmissibleSeed.Gamma6 ≤ GammaLog6 := gamma_strict_improvement.le

def sourceLogGain : ℝ := GammaLog6-FullAdmissibleSeed.Gamma6

theorem sourceLogGain_pos : 0 < sourceLogGain := sub_pos.mpr gamma_strict_improvement

theorem gain_lower : (300*H0-1)*FullAdmissibleSeed.Gamma6 ≤ sourceLogGain := by
  unfold sourceLogGain
  nlinarith only [gamma_scaled_lower]

/-- The gain replaces the old seed in the same literal F6 mass; it is not an
addition of two independent lower bounds and does not redefine any old Q. -/
theorem actual_count_with_gain {ε : ℝ} (hε : 0 < ε) :
    0 < sourceLogGain ∧
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (truncatedSixthLowerF6lin+FullAdmissibleSeed.Gamma6+sourceLogGain-ε)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
      (truncatedSixthMass N ((N : ℝ)^truncatedSixthLowerAlpha)
        ((N : ℝ)^truncatedSixthLowerBeta) ((N : ℝ)^truncatedSixthLowerSigma)
        ((N : ℝ)^truncatedSixthLowerLambda) : ℝ) := by
  refine ⟨sourceLogGain_pos,?_⟩
  obtain ⟨T,hT,h⟩ := actual_count_lower hε
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hid : truncatedSixthLowerF6lin+FullAdmissibleSeed.Gamma6+sourceLogGain-ε =
      truncatedSixthLowerF6lin+GammaLog6-ε := by unfold sourceLogGain; ring
  rw [hid]
  exact h N hN he

end FullSourceLog
