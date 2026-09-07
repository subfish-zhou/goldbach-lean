import MathlibNt.SieveTheory.LiLiuGoldbachS5IntegralUpper
import MathlibNt.SieveTheory.LiLiuGoldbachWeightRemainingFive

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The four literal signed terms; no analytic estimate is part of their definition. -/
noncomputable def goldbachWeightRemainingFour
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ) : ℤ :=
  goldbachWeightG6 A N z b + goldbachWeightG7 A N z b c -
    goldbachWeightG11 A N z b - goldbachWeightG12 A N z b c

theorem goldbachWeightRemainingFive_eq_remainingFour_sub_s5
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ) :
    goldbachWeightRemainingFive A N z b c =
      goldbachWeightRemainingFour A N z b c - goldbachS5Closed A N z ((N : ℝ) ^ ((1 : ℝ) / 3)) := by
  unfold goldbachWeightRemainingFive goldbachWeightRemainingFour
  ring

/-- Coarse coefficient using the proved uniform-eight S5 bound; not the optimized G9 coefficient. -/
noncomputable def goldbachWeightFourCoarseCoefficient (ε : ℝ) : ℝ :=
  goldbachWeightFiveCoefficient ε - 8 * goldbachB9MainIntegral

/-- The actual coarse S5 integral bound is consumed, without sign assumptions on the remaining four terms. -/
theorem goldbachWeight_remainingFour_coarse_S1_S2_S3_S4_S5_I10_consumed_eventually
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachWeightRemainingFour (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ))
        ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) +
        (goldbachWeightFourCoarseCoefficient ε - δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) ≤
        4 * (D19 N : ℝ) := by
  obtain ⟨Nr, hNr, hr⟩ := goldbachWeight_remainingFive_S1_S2_S3_S4_I10_consumed_eventually
    (δ / 2) ε (by positivity) hε hεu
  obtain ⟨Ns, _hNs, hs⟩ := goldbachS5Closed_normalized_upper_integral
    (δ / 2) ε (by positivity) hε hεu
  refine ⟨max Nr Ns, hNr.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hbase := hr N ((le_max_left _ _).trans hN) hEven
  have hupper := hs N ((le_max_right _ _).trans hN) hEven
  rw [goldbachWeightRemainingFive_eq_remainingFour_sub_s5] at hbase
  push_cast at hbase
  unfold goldbachWeightFourCoarseCoefficient
  nlinarith [hbase, hupper]

/-- The small-epsilon quantifiers remain epsilon0 first, then a threshold for each epsilon. -/
theorem goldbachWeight_remainingFour_coarse_small_epsilon (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2 / 15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachWeightRemainingFour (goldbachDifferenceCarrier N ε) N
            ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ))
            ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) +
            (goldbachWeightFourCoarseCoefficient 0 - δ) *
              (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) ≤
            4 * (D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, hε₀u, hr⟩ := goldbachWeight_remainingFive_small_epsilon
    (δ / 2) (by positivity)
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨Nr, hNr, hrN⟩ := hr ε hε hεlt
  obtain ⟨Ns, _hNs, hs⟩ := goldbachS5Closed_normalized_upper_integral
    (δ / 2) ε (by positivity) hε (hεlt.trans_le hε₀u)
  refine ⟨max Nr Ns, hNr.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hbase := hrN N ((le_max_left _ _).trans hN) hEven
  have hupper := hs N ((le_max_right _ _).trans hN) hEven
  rw [goldbachWeightRemainingFive_eq_remainingFour_sub_s5] at hbase
  push_cast at hbase
  unfold goldbachWeightFourCoarseCoefficient
  nlinarith [hbase, hupper]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig