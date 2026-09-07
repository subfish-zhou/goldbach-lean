import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarInnerBounds
import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarAssembly

open Set MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem s3base_integrable {a b : ℝ} (ha : (53/24 : ℝ) ≤ a)
    (hab : a ≤ b) (hb : b ≤ 45/8) :
    IntervalIntegrable (fun s : ℝ => 1/(s*((53/8 : ℝ)-s))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
  intro s hs
  change s*((53/8 : ℝ)-s) ≠ 0
  exact mul_ne_zero (ne_of_gt (by linarith [hs.1])) (ne_of_gt (by linarith [hs.2]))

theorem s3main_integrable {a b : ℝ} (ha : (53/24 : ℝ) ≤ a)
    (hab : a ≤ b) (hb : b ≤ 45/8) :
    IntervalIntegrable goldbachS3_scalarMainKernel volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact goldbachS3_scalarMain_continuous.mono (Icc_subset_Icc ha hb)

theorem s3main_high_bound {a : ℝ} (ha : 3 ≤ a) (haU : a ≤ 45/8) :
    53 * (∫ s in a..(45/8 : ℝ), goldbachS3_scalarMainKernel s) ≤
      53 * (∫ s in a..(45/8 : ℝ), 1/(s*((53/8 : ℝ)-s))) +
      ∫ s in a..(45/8 : ℝ), s3E s := by
  have hbase := s3base_integrable (a := a) (b := 45/8) (by linarith) haU le_rfl
  have hmain := s3main_integrable (a := a) (b := 45/8) (by linarith) haU le_rfl
  have hE := s3E_integrable ha haU le_rfl
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hbase.const_mul 53) hE]
  apply intervalIntegral.integral_mono_on haU (hmain.const_mul 53)
    ((hbase.const_mul 53).add hE)
  intro s hs
  have hi := goldbachS3_inner_le_envelope (s := s) ⟨ha.trans hs.1, hs.2⟩
  have hp : 0 ≤ s*((53/8 : ℝ)-s) := mul_nonneg (by linarith [hs.1]) (by linarith [hs.2])
  have h := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hi hp) (by norm_num : (0 : ℝ) ≤ 53)
  unfold goldbachS3_scalarMainKernel s3E
  rw [max_eq_left (ha.trans hs.1)]
  convert (add_le_add_left h (53/(s*((53/8 : ℝ)-s)))) using 1 <;> first | rfl | ring

theorem s3main4_bound :
    53 * (∫ s in (53/24 : ℝ)..(45/8 : ℝ), goldbachS3_scalarMainKernel s) ≤ (s3B4 : ℝ) := by
  have hm0 := s3main_integrable (a := 53/24) (b := 3) le_rfl (by norm_num) (by norm_num)
  have hm1 := s3main_integrable (a := 3) (b := 45/8) (by norm_num) (by norm_num) le_rfl
  have hb0 := s3base_integrable (a := 53/24) (b := 3) le_rfl (by norm_num) (by norm_num)
  have hb1 := s3base_integrable (a := 3) (b := 45/8) (by norm_num) (by norm_num) le_rfl
  have hl : (∫ s in (53/24 : ℝ)..3, goldbachS3_scalarMainKernel s) =
      ∫ s in (53/24 : ℝ)..3, 1/(s*((53/8 : ℝ)-s)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (53/24 : ℝ) ≤ 3)] at hs
    unfold goldbachS3_scalarMainKernel
    rw [max_eq_right hs.2]
    norm_num [jurkatRichertInnerIntegral]
  have hm := s3main_high_bound (a := 3) le_rfl (by norm_num)
  have hb := s3base4_bound
  rw [← intervalIntegral.integral_add_adjacent_intervals hb0 hb1] at hb
  rw [← intervalIntegral.integral_add_adjacent_intervals hm0 hm1, hl]
  linarith [s3I4_bound, s3B4_arithmetic]

theorem s3main5_bound :
    53 * (∫ s in (265/88 : ℝ)..(45/8 : ℝ), goldbachS3_scalarMainKernel s) ≤ (s3B5 : ℝ) := by
  have hm := s3main_high_bound (a := 265/88) (by norm_num) (by norm_num)
  linarith [s3base5_bound, s3I5_bound, s3B5_arithmetic]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig