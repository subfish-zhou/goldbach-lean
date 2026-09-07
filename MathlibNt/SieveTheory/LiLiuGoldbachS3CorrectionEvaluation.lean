import MathlibNt.SieveTheory.LiLiuGoldbachS3CorrectionPolynomials

open Set MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.S3Correction

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem log_le_L {x : ℝ} (hx : 0 ≤ x) : Real.log (1+x) ≤ L x := by
  let F : ℝ → ℝ := fun y => L y - Real.log (1+y)
  have hd : ∀ y ∈ Icc (0 : ℝ) x,
      HasDerivAt F (dL y - 1/(1+y)) y := by
    intro y hy
    have hlog : HasDerivAt (fun y : ℝ => Real.log (1+y)) (1/(1+y)) y := by
      convert (Real.hasDerivAt_log (by linarith [hy.1] : (1+y) ≠ 0)).comp y
        ((hasDerivAt_id y).const_add 1) using 1 <;> first | rfl | (simp only [mul_one, one_div])
    exact (L_deriv y).sub hlog
  have hp : ∀ y ∈ Icc (0 : ℝ) x, 0 ≤ dL y - 1/(1+y) := by
    intro y hy
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by linarith [hy.1] : 0 < 1+y)).2
    have he := L_residual y
    have hpow := pow_nonneg hy.1 33
    nlinarith only [he, hpow]
  have hm : MonotoneOn F (Icc (0 : ℝ) x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => hp y (interior_subset hy))
  have h := hm (show (0 : ℝ) ∈ Icc 0 x from ⟨le_rfl, hx⟩)
    (show x ∈ Icc 0 x from ⟨hx, le_rfl⟩) hx
  have hz : F 0 = 0 := by simp [F, L_zero]
  rw [hz] at h
  exact sub_nonneg.mp h

theorem inner_le_A {s : ℝ} (hs : 3 ≤ s) :
    jurkatRichertInnerIntegral s ≤ A (s-3) := by
  rw [goldbachS3_inner_shift]
  have hf : IntervalIntegrable (fun t : ℝ => Real.log (t-2)/(t-1)) volume 3 s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs]
    exact goldbachS3_inner_kernel_continuousOn le_rfl
  have hc : Continuous (fun t : ℝ => dA (t-3)) := by unfold dA; fun_prop
  have hg := hc.intervalIntegrable (μ := volume) (3 : ℝ) s
  have h := intervalIntegral.integral_mono_on hs hf hg (fun t ht => by
    have hl := log_le_L (by linarith [ht.1] : 0 ≤ t-3)
    have ha := dA_dominates (by linarith [ht.1] : 0 ≤ t-3)
    rw [show (1:ℝ)+(t-3) = t-2 by ring] at hl
    rw [show (2:ℝ)+(t-3) = t-1 by ring] at ha
    exact (div_le_div_of_nonneg_right hl (show 0 ≤ t-1 by linarith [ht.1])).trans ha)
  have he : (∫ t in (3 : ℝ)..s, dA (t-3)) = A (s-3) := by
    have hd : ∀ t ∈ uIcc (3 : ℝ) s,
        HasDerivAt (fun t : ℝ => A (t-3)) (dA (t-3)) t := by
      intro t _
      convert (A_deriv (t-3)).comp t ((hasDerivAt_id t).sub_const 3) using 1 <;> first | rfl | (simp only [mul_one])
    simpa [A_zero] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hg
  exact he ▸ h

theorem nested_inner_le_B {t : ℝ} (ht : 5 ≤ t) :
    (∫ v in (3 : ℝ)..t-2, jurkatRichertInnerIntegral v / v) ≤ B (t-5) := by
  have ht3 : 3 ≤ t-2 := by linarith
  have hf : IntervalIntegrable (fun v : ℝ => jurkatRichertInnerIntegral v / v)
      volume 3 (t-2) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht3]
    exact (goldbachS3_inner_continuousOn ht3).div continuousOn_id
      (fun v hv => by dsimp; linarith [hv.1])
  have hc : Continuous (fun v : ℝ => dB (v-3)) := by unfold dB; fun_prop
  have hg := hc.intervalIntegrable (μ := volume) (3 : ℝ) (t-2)
  have h := intervalIntegral.integral_mono_on ht3 hf hg (fun v hv => by
    have hI := div_le_div_of_nonneg_right (inner_le_A hv.1)
      (show 0 ≤ v by linarith [hv.1])
    have hB := dB_dominates (by linarith [hv.1] : 0 ≤ v-3)
    have he : (3:ℝ)+(v-3) = v := by ring
    rw [he] at hB
    exact hI.trans hB)
  have he : (∫ v in (3 : ℝ)..t-2, dB (v-3)) = B (t-5) := by
    have hd : ∀ v ∈ uIcc (3 : ℝ) (t-2),
        HasDerivAt (fun v : ℝ => B (v-3)) (dB (v-3)) v := by
      intro v _
      convert (B_deriv (v-3)).comp v ((hasDerivAt_id v).sub_const 3) using 1 <;> first | rfl | (simp only [mul_one])
    simpa [B_zero, show t-2-3 = t-5 by ring] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd hg
  exact he ▸ h

theorem nested_le_D {s : ℝ} (hs : 5 ≤ s) :
    (∫ t in (5 : ℝ)..s, (∫ v in (3 : ℝ)..t-2,
      jurkatRichertInnerIntegral v / v) / (t-1)) ≤ D (s-5) := by
  have hf : IntervalIntegrable (fun t : ℝ => (∫ v in (3 : ℝ)..t-2,
      jurkatRichertInnerIntegral v / v) / (t-1)) volume 5 s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs]
    exact (goldbachS3_nested_inner_continuousOn hs).div
      (continuousOn_id.sub continuousOn_const) (fun t ht => by dsimp; linarith [ht.1])
  have hc : Continuous (fun t : ℝ => dD (t-5)) := by unfold dD; fun_prop
  have hg := hc.intervalIntegrable (μ := volume) (5 : ℝ) s
  have h := intervalIntegral.integral_mono_on hs hf hg (fun t ht => by
    have hB := div_le_div_of_nonneg_right (nested_inner_le_B ht.1)
      (show 0 ≤ t-1 by linarith [ht.1])
    have hD := dD_dominates (by linarith [ht.1] : 0 ≤ t-5)
    have he : (4:ℝ)+(t-5) = t-1 := by ring
    rw [he] at hD
    exact hB.trans hD)
  have he : (∫ t in (5 : ℝ)..s, dD (t-5)) = D (s-5) := by
    have hd : ∀ t ∈ uIcc (5 : ℝ) s,
        HasDerivAt (fun t : ℝ => D (t-5)) (dD (t-5)) t := by
      intro t _
      convert (D_deriv (t-5)).comp t ((hasDerivAt_id t).sub_const 5) using 1 <;> first | rfl | (simp only [mul_one])
    simpa [D_zero] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hg
  exact he ▸ h

theorem correction_continuousOn {b : ℝ} (hb : 5 ≤ b) :
    ContinuousOn (fun s : ℝ => ∫ t in (5 : ℝ)..s,
      (∫ v in (3 : ℝ)..t-2, jurkatRichertInnerIntegral v / v)/(t-1)) (Icc 5 b) := by
  have hi : IntervalIntegrable (fun t : ℝ => (∫ v in (3 : ℝ)..t-2,
      jurkatRichertInnerIntegral v / v)/(t-1)) volume 5 b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hb]
    exact (goldbachS3_nested_inner_continuousOn hb).div
      (continuousOn_id.sub continuousOn_const) (fun t ht => by dsimp; linarith [ht.1])
  have h := intervalIntegral.continuousOn_primitive_interval' hi
    (show (5:ℝ) ∈ uIcc 5 b by rw [uIcc_of_le hb]; exact ⟨le_rfl, hb⟩)
  rwa [uIcc_of_le hb] at h

/-- Actual third-branch correction, retaining the full exterior weight 53.
No certificate parameters or target-shaped assumptions. -/
theorem actual_correction_le_rational :
    53 * (∫ s in (5 : ℝ)..(45/8 : ℝ),
      (∫ t in (5 : ℝ)..s, (∫ v in (3 : ℝ)..t-2,
        jurkatRichertInnerIntegral v / v)/(t-1)) /
          (s*((53/8 : ℝ)-s))) ≤ (1972364 / 10^10 : ℝ) := by
  have hab : (5:ℝ) ≤ 45/8 := by norm_num
  have hf : IntervalIntegrable (fun s : ℝ =>
      (∫ t in (5 : ℝ)..s, (∫ v in (3 : ℝ)..t-2,
        jurkatRichertInnerIntegral v / v)/(t-1))/(s*((53/8 : ℝ)-s)))
      volume 5 (45/8) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact (correction_continuousOn hab).div
      (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
      (fun s hs => mul_ne_zero (by dsimp; linarith [hs.1])
        (by dsimp; linarith [hs.2]))
  have hc : Continuous (fun s : ℝ => K (s-5)) := by unfold K; fun_prop
  have hg := hc.intervalIntegrable (μ := volume) (5:ℝ) (45/8)
  have h := intervalIntegral.integral_mono_on hab hf hg (fun s hs => by
    have hp : 0 ≤ s*((53/8 : ℝ)-s) := by
      apply mul_nonneg <;> linarith [hs.1, hs.2]
    have hD := div_le_div_of_nonneg_right (nested_le_D hs.1) hp
    have hK := K_dominates (by linarith [hs.1] : 0 ≤ s-5)
      (by linarith [hs.2] : s-5 ≤ 5/8)
    have he : ((5:ℝ)+(s-5))*(13/8-(s-5)) = s*(53/8-s) := by ring
    rw [he] at hK
    exact hD.trans hK)
  have he : (∫ s in (5:ℝ)..(45/8:ℝ), K (s-5)) = T (5/8)-T 0 := by
    have hd : ∀ s ∈ uIcc (5:ℝ) (45/8:ℝ),
        HasDerivAt (fun s : ℝ => T (s-5)) (K (s-5)) s := by
      intro s _
      convert (T_deriv (s-5)).comp s ((hasDerivAt_id s).sub_const 5) using 1 <;> first | rfl | (simp only [mul_one])
    convert intervalIntegral.integral_eq_sub_of_hasDerivAt hd hg using 1; norm_num
  rw [he] at h
  exact (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 53)).trans
    final_rational_evaluation

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.S3Correction