import MathlibNt.SieveTheory.LiLiuGoldbachSmallEpsilon
import MathlibNt.SieveTheory.LiLiuGoldbachS3PrimeKernel

open Filter
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The six literal signed terms after both S3 terms. No sign or main estimate
is assumed for this remaining integer-valued expression. -/
noncomputable def goldbachWeightRemainingSix
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ) : ℤ :=
  goldbachWeightG6 A N z b + goldbachWeightG7 A N z b c - 2 * goldbachS4 A N c -
    goldbachS5Closed A N z ((N : ℝ) ^ ((1 : ℝ) / 3)) -
    goldbachWeightG11 A N z b - goldbachWeightG12 A N z b c

theorem goldbachWeightRemainingEight_eq_remainingSix_sub_s3Pair
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ) :
    goldbachWeightRemainingEight A N z b c =
      goldbachWeightRemainingSix A N z b c -
        goldbachS3Closed A N z ((N : ℝ) ^ ((1 : ℝ) / 3)) - goldbachS3Closed A N z c := by
  unfold goldbachWeightRemainingEight goldbachWeightRemainingSix
  ring

/-- Each S3 term has external multiplicity one, not the S2 multiplicity four. -/
noncomputable def goldbachWeightSixCoefficient (ε : ℝ) : ℝ :=
  goldbachWeightKnownCoefficient ε -
    (1 - ε) * (53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
      (goldbachS3_primeKernelIntegral (1 / 3) + goldbachS3_primeKernelIntegral (3 / 11))

@[simp] theorem goldbachWeightSixCoefficient_zero :
    goldbachWeightSixCoefficient 0 = goldbachWeightKnownCoefficient 0 -
      (53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
        (goldbachS3_primeKernelIntegral (1 / 3) + goldbachS3_primeKernelIntegral (3 / 11)) := by
  simp only [goldbachWeightSixCoefficient, sub_zero, one_mul]

theorem goldbachWeightSixCoefficient_continuousAt_zero :
    ContinuousAt goldbachWeightSixCoefficient 0 := by
  unfold goldbachWeightSixCoefficient goldbachWeightKnownCoefficient goldbachS2LogCoefficient
  fun_prop (disch := norm_num)

/-- The scalar coefficient can be frozen at zero only after choosing epsilon;
this theorem itself makes no assertion about a count or its positivity. -/
theorem goldbachWeightSixCoefficient_small_epsilon (η : ℝ) (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2 / 15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        |goldbachWeightSixCoefficient ε - goldbachWeightSixCoefficient 0| < η := by
  obtain ⟨r, hr, hc⟩ := Metric.continuousAt_iff.mp
    goldbachWeightSixCoefficient_continuousAt_zero η hη
  refine ⟨min r (2 / 15), lt_min hr (by norm_num), min_le_right _ _, ?_⟩
  intro ε hε hεr
  have hd : dist ε 0 < r := by
    simpa [Real.dist_eq, abs_of_pos hε] using hεr.trans_le (min_le_left r (2 / 15))
  simpa only [Real.dist_eq] using hc hd

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig