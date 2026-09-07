import MathlibNt.SieveTheory.LiLiuGoldbachWeightRemainingEight

open Filter
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachS2LogCoefficient (ε : ℝ) : ℝ :=
  8 * Real.log ((1 - ((9 : ℝ) / 19 - ε)) / ((9 : ℝ) / 19 - ε))

noncomputable def goldbachWeightKnownCoefficient (ε : ℝ) : ℝ :=
  (1 - ε) * Real.exp (-Real.eulerMascheroniConstant) *
      ((159 / 2 : ℝ) * dimensionOneLowerLinearSieveFactor 6 +
        (33 / 2 : ℝ) * dimensionOneLowerLinearSieveFactor (33 / 8 : ℝ)) -
    4 * goldbachS2LogCoefficient ε - 8 * (1 - ε) * goldbachB10I10

@[simp] theorem goldbachS2LogCoefficient_zero :
    goldbachS2LogCoefficient 0 = 8 * Real.log (10 / 9 : ℝ) := by
  norm_num [goldbachS2LogCoefficient]

@[simp] theorem goldbachWeightKnownCoefficient_zero :
    goldbachWeightKnownCoefficient 0 =
      Real.exp (-Real.eulerMascheroniConstant) *
        ((159 / 2 : ℝ) * dimensionOneLowerLinearSieveFactor 6 +
          (33 / 2 : ℝ) * dimensionOneLowerLinearSieveFactor (33 / 8 : ℝ)) -
        32 * Real.log (10 / 9 : ℝ) - 8 * goldbachB10I10 := by
  simp only [goldbachWeightKnownCoefficient, goldbachS2LogCoefficient_zero]
  ring

private theorem SmallEpsilon_s2_continuous : ContinuousAt goldbachS2LogCoefficient 0 := by
  unfold goldbachS2LogCoefficient
  fun_prop (disch := norm_num)

private theorem SmallEpsilon_known_continuous : ContinuousAt goldbachWeightKnownCoefficient 0 := by
  unfold goldbachWeightKnownCoefficient goldbachS2LogCoefficient
  fun_prop (disch := norm_num)

private theorem SmallEpsilon_close {f : ℝ → ℝ} (hf : ContinuousAt f 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2 / 15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → |f ε - f 0| < η := by
  obtain ⟨r, hr, hclose⟩ := Metric.continuousAt_iff.mp hf η hη
  refine ⟨min r (2 / 15), lt_min hr (by norm_num), min_le_right _ _, ?_⟩
  intro ε hε hεr
  have hdist : dist ε 0 < r := by
    simpa [Real.dist_eq, abs_of_pos hε] using hεr.trans_le (min_le_left r (2 / 15))
  simpa [Real.dist_eq] using hclose hdist

/-- The small epsilon is selected before the large-N threshold. No uniform
threshold over all small epsilon is asserted. -/
theorem goldbachS2_g3_upper_small_epsilon (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2 / 15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachS2 (goldbachDifferenceCarrier N ε) N
            ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) : ℝ) ≤
            (8 * Real.log (10 / 9 : ℝ) + δ) *
              (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  obtain ⟨ε₀, hε₀, hε₀u, hc⟩ := SmallEpsilon_close SmallEpsilon_s2_continuous
    (δ / 2) (by positivity)
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨N₀, hN₀, hN⟩ := goldbachS2_normalized_upper_nine_nineteen_sub
    (δ / 2) ε (by positivity) hε (hεlt.trans_le hε₀u)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hNN hEven
  let M : ℝ := SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2
  have hM : 0 ≤ M := by
    exact div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  have hbound : (goldbachS2 (goldbachDifferenceCarrier N ε) N
      ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) : ℝ) ≤
      (goldbachS2LogCoefficient ε + δ / 2) * M := by
    simpa [goldbachS2LogCoefficient, M, Real.rpow_natCast, div_eq_mul_inv, mul_assoc]
      using hN N hNN hEven
  have hcoef : goldbachS2LogCoefficient ε + δ / 2 ≤ 8 * Real.log (10 / 9 : ℝ) + δ := by
    have hh := (abs_lt.mp (hc ε hε hεlt)).2
    rw [goldbachS2LogCoefficient_zero] at hh
    linarith
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoef hM)

/-- A single epsilon restriction controls all already-consumed coefficients.
The remaining eight signed counts retain their actual epsilon-dependent carrier. -/
theorem goldbachWeight_remainingEight_small_epsilon (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2 / 15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachWeightRemainingEight (goldbachDifferenceCarrier N ε) N
            ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ))
            ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) +
            (goldbachWeightKnownCoefficient 0 - δ) *
              (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) ≤
              4 * (D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, hε₀u, hc⟩ := SmallEpsilon_close SmallEpsilon_known_continuous
    (δ / 2) (by positivity)
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨N₀, hN₀, hN⟩ := goldbachWeight_remainingEight_S1_S2_I10_consumed_eventually
    (δ / 2) ε (by positivity) hε (hεlt.trans_le hε₀u)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hNN hEven
  let M : ℝ := SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2
  let R : ℝ := goldbachWeightRemainingEight (goldbachDifferenceCarrier N ε) N
    ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)) ((N : ℝ) ^ (3 / 11 : ℝ))
  have hM : 0 ≤ M := by
    exact div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  have hbound : R + (goldbachWeightKnownCoefficient ε - δ / 2) * M ≤ 4 * (D19 N : ℝ) := by
    have hh := hN N hNN hEven
    dsimp only [goldbachWeightKnownCoefficient, goldbachS2LogCoefficient, M, R]
    convert hh using 1; ring
  have hcoef : goldbachWeightKnownCoefficient 0 - δ ≤ goldbachWeightKnownCoefficient ε - δ / 2 := by
    have hh := (abs_lt.mp (hc ε hε hεlt)).1
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef hM
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig