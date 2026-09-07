import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarReduction
import MathlibNt.SieveTheory.LiLiuGoldbachS3NormalizedUpper

open Set MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false

local notation "S3ScalarBody" => (fun s : ℝ =>
  (ite (s ≤ 3) 1 (ite (s ≤ 5) (1 + jurkatRichertInnerIntegral s)
    (1 + jurkatRichertInnerIntegral 5 +
      ∫ t in (5 : ℝ)..s,
        (Real.log (t - 2) + ∫ v in (3 : ℝ)..t - 2,
          jurkatRichertInnerIntegral v / v) / (t - 1)))) /
    (s * ((53 / 8 : ℝ) - s)))

/-- Exact exp-free integral for beta = 1 / 3; this is not a rational bound. -/
noncomputable def goldbachS3_oneThirdExpFreeIntegral : ℝ :=
  ∫ s in (53 / 24 : ℝ)..(45 / 8 : ℝ), S3ScalarBody s

/-- Integrability of the actual exp-free endpoint expression. -/
theorem goldbachS3_oneThirdExpFreeIntegral_integrable :
    IntervalIntegrable S3ScalarBody volume (53 / 24 : ℝ) (45 / 8 : ℝ) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (53 / 24 : ℝ) ≤ 45 / 8)]
  exact goldbachS3_scalar_exp_free_continuousOn.mono
    (Icc_subset_Icc (by norm_num) le_rfl)

/-- Exact identification with the unchanged production coefficient. -/
theorem goldbachS3_oneThird_coefficient_eq :
    (53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
      goldbachS3_primeKernelIntegral (1 / 3 : ℝ) = 53 * goldbachS3_oneThirdExpFreeIntegral := by
  have h := goldbachS3_scalar_exp_free (β := (1 / 3 : ℝ)) (by norm_num) (by norm_num)
  norm_num only at h
  exact h

/-- Actual normalized count at beta = 1 / 3, with the full strict mother
carrier, epsilon range, threshold, parity and (1-epsilon) retained.
The rational scalar bound is deliberately not claimed here. -/
theorem goldbachS3_normalized_upper_oneThird_exp_free (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS3Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
        ((1 - ε) * (53 * goldbachS3_oneThirdExpFreeIntegral) + δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  obtain ⟨N₀, hN₀, hN⟩ := goldbachS3_normalized_upper (1 / 3 : ℝ) δ ε
    (by norm_num) (by norm_num) hδ hε hεu
  refine ⟨N₀, hN₀, ?_⟩
  intro N hlarge hEven
  have h := hN N hlarge hEven
  have he : (1 - ε) * (53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
      goldbachS3_primeKernelIntegral (1 / 3 : ℝ) =
        (1 - ε) * (53 * goldbachS3_oneThirdExpFreeIntegral) := by
    rw [← goldbachS3_oneThird_coefficient_eq]
    ring
  simpa only [he] using h

/-- Exact exp-free integral for beta = 3 / 11; this is not a rational bound. -/
noncomputable def goldbachS3_threeEleventhsExpFreeIntegral : ℝ :=
  ∫ s in (265 / 88 : ℝ)..(45 / 8 : ℝ), S3ScalarBody s

/-- Integrability of the actual exp-free endpoint expression. -/
theorem goldbachS3_threeEleventhsExpFreeIntegral_integrable :
    IntervalIntegrable S3ScalarBody volume (265 / 88 : ℝ) (45 / 8 : ℝ) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (265 / 88 : ℝ) ≤ 45 / 8)]
  exact goldbachS3_scalar_exp_free_continuousOn.mono
    (Icc_subset_Icc (by norm_num) le_rfl)

/-- Exact identification with the unchanged production coefficient. -/
theorem goldbachS3_threeElevenths_coefficient_eq :
    (53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
      goldbachS3_primeKernelIntegral (3 / 11 : ℝ) = 53 * goldbachS3_threeEleventhsExpFreeIntegral := by
  have h := goldbachS3_scalar_exp_free (β := (3 / 11 : ℝ)) (by norm_num) (by norm_num)
  norm_num only at h
  exact h

/-- Actual normalized count at beta = 3 / 11, with the full strict mother
carrier, epsilon range, threshold, parity and (1-epsilon) retained.
The rational scalar bound is deliberately not claimed here. -/
theorem goldbachS3_normalized_upper_threeElevenths_exp_free (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS3Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) ≤
        ((1 - ε) * (53 * goldbachS3_threeEleventhsExpFreeIntegral) + δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  obtain ⟨N₀, hN₀, hN⟩ := goldbachS3_normalized_upper (3 / 11 : ℝ) δ ε
    (by norm_num) (by norm_num) hδ hε hεu
  refine ⟨N₀, hN₀, ?_⟩
  intro N hlarge hEven
  have h := hN N hlarge hEven
  have he : (1 - ε) * (53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
      goldbachS3_primeKernelIntegral (3 / 11 : ℝ) =
        (1 - ε) * (53 * goldbachS3_threeEleventhsExpFreeIntegral) := by
    rw [← goldbachS3_threeElevenths_coefficient_eq]
    ring
  simpa only [he] using h

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig