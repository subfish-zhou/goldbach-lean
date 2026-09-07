import MathlibNt.SieveTheory.LiLiuGoldbachS3RetainedScalar
import MathlibNt.SieveTheory.LiLiuGoldbachG11UniformScalarCount
import MathlibNt.SieveTheory.LiLiuGoldbachWeightUniformRationalConsumed
import MathlibNt.SieveTheory.LiLiuGoldbachPositiveScalarClosed

open MathlibNt.SieveTheory.SwitchingPrinciple
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Retain the sharper proved S3 endpoints instead of weakening to the paper decimals. -/
theorem goldbachWeightThreeNegativeScalarCoefficient_ge_retained :
    (124337327/200000000 : ℝ) ≤ goldbachWeightThreeNegativeScalarCoefficient := by
  have hp := goldbachWeightFiveNegativeScalarCoefficient_ge_62033529
  have h4 := goldbachS3_oneThird_coefficient_le_retained236056871187
  have h5 := goldbachS3_threeElevenths_coefficient_le_retained195190815363
  unfold goldbachWeightFiveNegativeScalarCoefficient at hp
  unfold goldbachWeightThreeNegativeScalarCoefficient
  simp only [mul_add] at hp ⊢
  linarith only [hp, h4, h5]

/-- The improved constant is consumed in the actual remaining-five theorem. -/
theorem goldbachWeight_remainingFive_retained_small_epsilon
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachWeightRemainingFive (goldbachDifferenceCarrier N ε) N
            ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
            ((N : ℝ)^(3/11 : ℝ)) : ℝ) +
            ((124337327/200000000 : ℝ)-δ)*
              (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
            4*(D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, hε₀u, h⟩ := goldbachWeight_remainingFive_threeNegativeScalars_small_epsilon δ hδ
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨N₀, hN₀, hN⟩ := h ε hε hεlt
  refine ⟨N₀, hN₀, ?_⟩
  intro N hNN hEven
  have hs : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
    (sub_le_sub_right goldbachWeightThreeNegativeScalarCoefficient_ge_retained δ) hs)).trans
      (hN N hNN hEven)

/-- Fully connected retained-constant ledger; no estimate of the remaining signed counts. -/
theorem goldbachWeight_retainedUniform_consumed_small_epsilon
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ∀ Z : ℝ, 1 ≤ Z → Z ≤ Real.sqrt (N : ℝ) →
            (goldbachWeightG11PaidBase N ε : ℝ) -
              (goldbachB9LowPositivePrefixSiftedCount N ε Z : ℝ) +
              (-(682025197/200000000 : ℝ)-δ)*
                (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
              4*(D19 N : ℝ) := by
  obtain ⟨Ng, _hNg, hg⟩ := goldbachWeightG11_le_uniformScalar_numeric_fixed
  obtain ⟨ε₀, hε₀, hε₀u, h⟩ :=
    goldbachWeight_remainingFive_retained_small_epsilon (δ/3) (by positivity)
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨Nr, hNr, hr⟩ := h ε hε hεlt
  obtain ⟨Nh, _hNh, hh⟩ := goldbachS5HighFirstClosed_normalized_upper_392796161
    (δ/3) ε (by positivity) hε (hεlt.trans_le hε₀u)
  obtain ⟨Nl, _hNl, hl⟩ :=
    goldbachS5ClosedBelow_le_positivePrefix_sifted_normalized_of_pos ε (δ/3) hε (by positivity)
  refine ⟨max Nr (max Nh (max Nl Ng)), by omega, ?_⟩
  intro N hN hEven Z hZ hZu
  have hb := hr N (by omega) hEven
  have hhigh := hh N (by omega) hEven
  have hlow := hl N (by omega) Z hZ hZu
  have hg11 := hg N (by omega) hEven ε hε.le
  have hz : (N : ℝ)^(4/53 : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  rw [goldbachWeightRemainingFive_eq_lowFirstRemainder_sub_high _ _ _ _ _ hz] at hb
  unfold goldbachWeightLowFirstRemainder at hb
  push_cast at hb
  rw [goldbachWeightG11PaidBase_eq_actual]
  push_cast
  nlinarith [hb, hhigh, hlow, hg11]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig