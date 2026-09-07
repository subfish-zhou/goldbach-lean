import MathlibNt.SieveTheory.LiLiuGoldbachS4IntegralUpper
import MathlibNt.SieveTheory.LiLiuGoldbachWeightRemainingSixConsumer

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The five literal signed terms, after consumption of the externally doubled S4. -/
noncomputable def goldbachWeightRemainingFive
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ) : ℤ :=
  goldbachWeightG6 A N z b + goldbachWeightG7 A N z b c -
    goldbachS5Closed A N z ((N : ℝ) ^ ((1 : ℝ) / 3)) -
    goldbachWeightG11 A N z b - goldbachWeightG12 A N z b c

theorem goldbachWeightRemainingSix_eq_remainingFive_sub_two_s4
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ) :
    goldbachWeightRemainingSix A N z b c =
      goldbachWeightRemainingFive A N z b c - 2 * goldbachS4 A N c := by
  unfold goldbachWeightRemainingSix goldbachWeightRemainingFive
  ring

/-- The coefficient includes the external factor two: 2*(8*I8)=16*I8. -/
noncomputable def goldbachWeightFiveCoefficient (ε : ℝ) : ℝ :=
  goldbachWeightSixCoefficient ε - 16 * goldbachB8MainIntegral

/-- The actual S4 integral bound is consumed, without a sign assumption on the five remaining terms. -/
theorem goldbachWeight_remainingFive_S1_S2_S3_S4_I10_consumed_eventually
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachWeightRemainingFive (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ))
        ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) +
        (goldbachWeightFiveCoefficient ε - δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) ≤
        4 * (D19 N : ℝ) := by
  obtain ⟨Nr, hNr, hr⟩ := goldbachWeight_remainingSix_S1_S2_S3_I10_consumed_eventually
    (δ / 2) ε (by positivity) hε hεu
  obtain ⟨Ns, _hNs, hs⟩ := goldbachS4_normalized_upper_integral
    (δ / 4) ε (by positivity) hε hεu
  refine ⟨max Nr Ns, hNr.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hbase := hr N ((le_max_left _ _).trans hN) hEven
  have hupper := hs N ((le_max_right _ _).trans hN) hEven
  rw [goldbachWeightRemainingSix_eq_remainingFive_sub_two_s4] at hbase
  push_cast at hbase
  unfold goldbachWeightFiveCoefficient
  nlinarith [hbase, hupper]

/-- The small-epsilon quantifiers remain epsilon0 first, then a threshold for each epsilon. -/
theorem goldbachWeight_remainingFive_small_epsilon (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2 / 15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachWeightRemainingFive (goldbachDifferenceCarrier N ε) N
            ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ))
            ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) +
            (goldbachWeightFiveCoefficient 0 - δ) *
              (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) ≤
            4 * (D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, hε₀u, hr⟩ := goldbachWeight_remainingSix_small_epsilon
    (δ / 2) (by positivity)
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨Nr, hNr, hrN⟩ := hr ε hε hεlt
  obtain ⟨Ns, _hNs, hs⟩ := goldbachS4_normalized_upper_integral
    (δ / 4) ε (by positivity) hε (hεlt.trans_le hε₀u)
  refine ⟨max Nr Ns, hNr.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hbase := hrN N ((le_max_left _ _).trans hN) hEven
  have hupper := hs N ((le_max_right _ _).trans hN) hEven
  rw [goldbachWeightRemainingSix_eq_remainingFive_sub_two_s4] at hbase
  push_cast at hbase
  unfold goldbachWeightFiveCoefficient
  nlinarith [hbase, hupper]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig