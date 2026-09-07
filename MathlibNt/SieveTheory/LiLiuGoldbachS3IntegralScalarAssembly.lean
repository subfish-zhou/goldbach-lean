import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarEnvelopeBounds

open Set MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

local notation "S3Body" => (fun s : ℝ =>
  (ite (s ≤ 3) 1 (ite (s ≤ 5) (1 + jurkatRichertInnerIntegral s)
    (1 + jurkatRichertInnerIntegral 5 + ∫ t in (5 : ℝ)..s,
      (Real.log (t-2) + ∫ v in (3 : ℝ)..t-2, jurkatRichertInnerIntegral v/v)/(t-1)))) /
    (s*((53/8 : ℝ)-s)))

noncomputable def goldbachS3_scalarMainKernel (s : ℝ) : ℝ :=
  (1 + jurkatRichertInnerIntegral (max s 3))/(s*((53/8 : ℝ)-s))

noncomputable def goldbachS3_scalarCorrectionKernel (s : ℝ) : ℝ :=
  (∫ t in (5 : ℝ)..s, (∫ v in (3 : ℝ)..t-2,
    jurkatRichertInnerIntegral v/v)/(t-1))/(s*((53/8 : ℝ)-s))

theorem goldbachS3_scalarMain_continuous :
    ContinuousOn goldbachS3_scalarMainKernel (Icc (53/24 : ℝ) (45/8 : ℝ)) := by
  apply ContinuousOn.div
  · apply continuousOn_const.add
    exact (goldbachS3_inner_continuousOn (by norm_num : (3 : ℝ) ≤ 45/8)).comp
      (continuous_id.max continuous_const).continuousOn
      (fun s hs => ⟨le_max_right _ _, max_le hs.2 (by norm_num)⟩)
  · exact continuousOn_id.mul (continuousOn_const.sub continuousOn_id)
  · intro s hs
    exact mul_ne_zero (ne_of_gt (by linarith [hs.1])) (ne_of_gt (by linarith [hs.2]))

theorem goldbachS3_scalarBody_low {s : ℝ} (hs : s ≤ 5) :
    S3Body s = goldbachS3_scalarMainKernel s := by
  unfold goldbachS3_scalarMainKernel
  dsimp only
  by_cases h3 : s ≤ 3
  · rw [if_pos h3, max_eq_right h3]
    norm_num [jurkatRichertInnerIntegral]
  · rw [if_neg h3, if_pos hs, max_eq_left (by linarith : 3 ≤ s)]

theorem goldbachS3_scalarBody_high {s : ℝ} (hs : 5 ≤ s) :
    S3Body s = goldbachS3_scalarMainKernel s + goldbachS3_scalarCorrectionKernel s := by
  unfold goldbachS3_scalarMainKernel goldbachS3_scalarCorrectionKernel
  dsimp only
  rw [if_neg (by linarith : ¬s ≤ 3), max_eq_left (by linarith : 3 ≤ s)]
  by_cases h5 : s ≤ 5
  · have he : s = 5 := le_antisymm h5 hs
    subst s
    simp
  · rw [if_neg h5, goldbachS3_third_body_split hs, add_div]

theorem goldbachS3_scalarCorrection_continuous :
    ContinuousOn goldbachS3_scalarCorrectionKernel (Icc (5 : ℝ) (45/8 : ℝ)) := by
  have h := (goldbachS3_scalar_exp_free_continuousOn.sub goldbachS3_scalarMain_continuous).mono
    (Icc_subset_Icc (by norm_num : (53/24 : ℝ) ≤ 5) le_rfl)
  apply h.congr
  intro s hs
  change goldbachS3_scalarCorrectionKernel s = S3Body s - goldbachS3_scalarMainKernel s
  rw [goldbachS3_scalarBody_high hs.1]
  ring

/-- Exact separation of the common third-branch correction, with actual integrability. -/
theorem goldbachS3_scalar_integral_split {a : ℝ}
    (ha : (53/24 : ℝ) ≤ a) (ha5 : a ≤ 5) :
    (∫ s in a..(45/8 : ℝ), S3Body s) =
      (∫ s in a..(45/8 : ℝ), goldbachS3_scalarMainKernel s) +
      ∫ s in (5 : ℝ)..(45/8 : ℝ), goldbachS3_scalarCorrectionKernel s := by
  have haU : a ≤ (45/8 : ℝ) := ha5.trans (by norm_num)
  have ho : IntervalIntegrable S3Body volume a (45/8 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le haU]
    exact goldbachS3_scalar_exp_free_continuousOn.mono (Icc_subset_Icc ha le_rfl)
  have hm : IntervalIntegrable goldbachS3_scalarMainKernel volume a (45/8 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le haU]
    exact goldbachS3_scalarMain_continuous.mono (Icc_subset_Icc ha le_rfl)
  have hc : IntervalIntegrable goldbachS3_scalarCorrectionKernel volume 5 (45/8 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (5 : ℝ) ≤ 45/8)]
    exact goldbachS3_scalarCorrection_continuous
  have hol := ho.mono_set (show uIcc a 5 ⊆ uIcc a (45/8 : ℝ) by
    rw [uIcc_of_le ha5, uIcc_of_le haU]; exact Icc_subset_Icc le_rfl (by norm_num))
  have hor := ho.mono_set (show uIcc (5 : ℝ) (45/8 : ℝ) ⊆ uIcc a (45/8 : ℝ) by
    rw [uIcc_of_le (by norm_num : (5 : ℝ) ≤ 45/8), uIcc_of_le haU]; exact Icc_subset_Icc ha5 le_rfl)
  have hml := hm.mono_set (show uIcc a 5 ⊆ uIcc a (45/8 : ℝ) by
    rw [uIcc_of_le ha5, uIcc_of_le haU]; exact Icc_subset_Icc le_rfl (by norm_num))
  have hmr := hm.mono_set (show uIcc (5 : ℝ) (45/8 : ℝ) ⊆ uIcc a (45/8 : ℝ) by
    rw [uIcc_of_le (by norm_num : (5 : ℝ) ≤ 45/8), uIcc_of_le haU]; exact Icc_subset_Icc ha5 le_rfl)
  have hl : (∫ s in a..5, S3Body s) = ∫ s in a..5, goldbachS3_scalarMainKernel s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ha5] at hs
    exact goldbachS3_scalarBody_low hs.2
  have hr : (∫ s in (5 : ℝ)..(45/8 : ℝ), S3Body s) =
      (∫ s in (5 : ℝ)..(45/8 : ℝ), goldbachS3_scalarMainKernel s) +
      ∫ s in (5 : ℝ)..(45/8 : ℝ), goldbachS3_scalarCorrectionKernel s := by
    rw [← intervalIntegral.integral_add hmr hc]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (5 : ℝ) ≤ 45/8)] at hs
    exact goldbachS3_scalarBody_high hs.1
  rw [← intervalIntegral.integral_add_adjacent_intervals hol hor,
    ← intervalIntegral.integral_add_adjacent_intervals hml hmr, hl, hr]
  ring

theorem goldbachS3_oneThird_integral_split :
    goldbachS3_oneThirdExpFreeIntegral =
      (∫ s in (53/24 : ℝ)..(45/8 : ℝ), goldbachS3_scalarMainKernel s) +
      ∫ s in (5 : ℝ)..(45/8 : ℝ), goldbachS3_scalarCorrectionKernel s :=
  goldbachS3_scalar_integral_split le_rfl (by norm_num)

theorem goldbachS3_threeElevenths_integral_split :
    goldbachS3_threeEleventhsExpFreeIntegral =
      (∫ s in (265/88 : ℝ)..(45/8 : ℝ), goldbachS3_scalarMainKernel s) +
      ∫ s in (5 : ℝ)..(45/8 : ℝ), goldbachS3_scalarCorrectionKernel s :=
  goldbachS3_scalar_integral_split (by norm_num) (by norm_num)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig