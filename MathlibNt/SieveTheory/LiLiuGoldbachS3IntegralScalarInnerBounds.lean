import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarSegments
import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarBaseBounds

open Set MeasureTheory Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem s3segment0_domain {s : ℝ} (hs : s ∈ Icc (3 : ℝ) 4) :
    0 ≤ (s-3)/(s-1) ∧ 45*((s-3)/(s-1)-0)/(29-45*0) ≤ 3/5 := by
  have hp : 0 < s-1 := by linarith [hs.1]
  have hu : (s-3)/(s-1) ≤ 1/3 := (div_le_iff₀ hp).2 (by linarith [hs.2])
  constructor
  · exact div_nonneg (by linarith [hs.1]) hp.le
  · norm_num
    linarith

theorem s3segment1_domain {s : ℝ} (hs : s ∈ Icc (4 : ℝ) 5) :
    1/3 ≤ (s-3)/(s-1) ∧ 45*((s-3)/(s-1)-1/3)/(29-45*(1/3)) ≤ 3/5 := by
  have hp : 0 < s-1 := by linarith [hs.1]
  have hu : (s-3)/(s-1) ≤ 1/2 := (div_le_iff₀ hp).2 (by linarith [hs.2])
  constructor
  · exact (le_div_iff₀ hp).2 (by linarith [hs.1])
  · norm_num
    linarith

theorem s3segment2_domain {s : ℝ} (hs : s ∈ Icc (5 : ℝ) (45/8 : ℝ)) :
    1/2 ≤ (s-3)/(s-1) ∧ 45*((s-3)/(s-1)-1/2)/(29-45*(1/2)) ≤ 3/5 := by
  have hp : 0 < s-1 := by linarith [hs.1]
  have hu : (s-3)/(s-1) ≤ 21/37 := (div_le_iff₀ hp).2 (by linarith [hs.2])
  constructor
  · exact (le_div_iff₀ hp).2 (by linarith [hs.1])
  · norm_num
    linarith

theorem s3integral0_bound : (∫ s in (3 : ℝ)..4, s3E s) ≤ (s3j0 : ℝ) := by
  have h := s3segment_bound (l := 3) (r := 4) (a := 0) s3q0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ hs => s3segment0_domain hs)
    (fun y => by simpa only [s3pCoeffs_eq, s3K] using s3q0_eq y)
  norm_num only [sub_self, zero_div, sub_zero] at h
  exact s3j0_value ▸ h

theorem s3integral0b_bound : (∫ s in (265/88 : ℝ)..4, s3E s) ≤ (s3j0b : ℝ) := by
  have h := s3segment_bound (l := 265/88) (r := 4) (a := 0) s3q0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ hs => s3segment0_domain ⟨by linarith [hs.1], hs.2⟩)
    (fun y => by simpa only [s3pCoeffs_eq, s3K] using s3q0_eq y)
  norm_num at h
  exact s3j0b_value ▸ h

theorem s3integral1_bound : (∫ s in (4 : ℝ)..5, s3E s) ≤ (s3j1 : ℝ) := by
  have h := s3segment_bound (l := 4) (r := 5) (a := 1/3) s3q1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ hs => s3segment1_domain hs)
    (fun y => by simpa only [s3pCoeffs_eq, s3K] using s3q1_eq y)
  norm_num at h
  exact s3j1_value ▸ h

theorem s3integral2_bound : (∫ s in (5 : ℝ)..(45/8 : ℝ), s3E s) ≤ (s3j2 : ℝ) := by
  have h := s3segment_bound (l := 5) (r := 45/8) (a := 1/2) s3q2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ hs => s3segment2_domain hs)
    (fun y => by simpa only [s3pCoeffs_eq, s3K] using s3q2_eq y)
  norm_num at h
  exact s3j2_value ▸ h

theorem s3E_integrable {a b : ℝ} (ha : 3 ≤ a) (hab : a ≤ b) (hb : b ≤ 45/8) :
    IntervalIntegrable s3E volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact s3E_continuousOn ha hb

theorem s3I4_bound : (∫ s in (3 : ℝ)..(45/8 : ℝ), s3E s) ≤
    (s3j0 : ℝ) + s3j1 + s3j2 := by
  have h04 := s3E_integrable (a := 3) (b := 4) (by norm_num) (by norm_num) (by norm_num)
  have h45 := s3E_integrable (a := 4) (b := 5) (by norm_num) (by norm_num) (by norm_num)
  have h5u := s3E_integrable (a := 5) (b := 45/8) (by norm_num) (by norm_num) (by norm_num)
  rw [← intervalIntegral.integral_add_adjacent_intervals (h04.trans h45) h5u,
    ← intervalIntegral.integral_add_adjacent_intervals h04 h45]
  exact add_le_add (add_le_add s3integral0_bound s3integral1_bound) s3integral2_bound

theorem s3I5_bound : (∫ s in (265/88 : ℝ)..(45/8 : ℝ), s3E s) ≤
    (s3j0b : ℝ) + s3j1 + s3j2 := by
  have h04 := s3E_integrable (a := 265/88) (b := 4) (by norm_num) (by norm_num) (by norm_num)
  have h45 := s3E_integrable (a := 4) (b := 5) (by norm_num) (by norm_num) (by norm_num)
  have h5u := s3E_integrable (a := 5) (b := 45/8) (by norm_num) (by norm_num) (by norm_num)
  rw [← intervalIntegral.integral_add_adjacent_intervals (h04.trans h45) h5u,
    ← intervalIntegral.integral_add_adjacent_intervals h04 h45]
  exact add_le_add (add_le_add s3integral0b_bound s3integral1_bound) s3integral2_bound

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig