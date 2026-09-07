import MathlibNt.SieveTheory.LiLiuGoldbachB9HighFirstIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachB9SplitIntegralReduction
import MathlibNt.SieveTheory.LiLiuGoldbachWeightRemainingFourCoarse
import MathlibNt.SieveTheory.LiLiuGoldbachS5FirstPrimeSplit

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The four signed terms minus the literal strict-low S5 sum. No low estimate is assumed. -/
noncomputable def goldbachWeightLowFirstRemainder
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ) : ℤ :=
  goldbachWeightRemainingFour A N z b c -
    goldbachS5ClosedBelow A N z ((N : ℝ) ^ (1 / 3 : ℝ)) ((N : ℝ) ^ (1 / 10 : ℝ))

theorem goldbachWeightRemainingFive_eq_lowFirstRemainder_sub_high
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ) (hz : z ≤ (N : ℝ) ^ (1 / 10 : ℝ)) :
    goldbachWeightRemainingFive A N z b c =
      goldbachWeightLowFirstRemainder A N z b c -
        goldbachS5Closed A N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  rw [goldbachWeightRemainingFive_eq_remainingFour_sub_s5,
    goldbachS5Closed_eq_below_add_raisedCutoff A N z _ _ hz]
  unfold goldbachWeightLowFirstRemainder
  ring

noncomputable def goldbachWeightHighFirstCoefficient (ε : ℝ) : ℝ :=
  goldbachWeightFiveCoefficient ε - 8 * goldbachB9HighMainIntegral

theorem goldbachB9HighMainIntegral_eq_singleIntegral :
    goldbachB9HighMainIntegral =
      ∫ u in (1 / 10 : ℝ)..(1 / 3), Real.log (2 - 3 * u) / (u * (1 - u)) := by
  exact goldbachB9SubintervalIntegral_eq_single (by norm_num) (by norm_num) le_rfl

/-- Only the proved high estimate is consumed; the low count remains visible in the left side. -/
theorem goldbachWeight_highFirst_consumed_eventually
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachWeightLowFirstRemainder (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ))
        ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) +
        (goldbachWeightHighFirstCoefficient ε - δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) ≤
        4 * (D19 N : ℝ) := by
  obtain ⟨Nr, hNr, hr⟩ := goldbachWeight_remainingFive_S1_S2_S3_S4_I10_consumed_eventually
    (δ / 2) ε (by positivity) hε hεu
  obtain ⟨Ns, _hNs, hs⟩ := goldbachS5HighFirstClosed_normalized_upper_integral
    (δ / 2) ε (by positivity) hε hεu
  refine ⟨max Nr Ns, hNr.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hbase := hr N ((le_max_left _ _).trans hN) hEven
  have hupper := hs N ((le_max_right _ _).trans hN) hEven
  have hN4 : 4 ≤ N := hNr.trans ((le_max_left _ _).trans hN)
  have hz : (N : ℝ) ^ (4 / 53 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  rw [goldbachWeightRemainingFive_eq_lowFirstRemainder_sub_high _ _ _ _ _ hz] at hbase
  push_cast at hbase
  unfold goldbachWeightHighFirstCoefficient
  nlinarith [hbase, hupper]

/-- epsilon0 is chosen first; the prime-size threshold may depend on the fixed epsilon. -/
theorem goldbachWeight_highFirst_consumed_small_epsilon (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2 / 15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachWeightLowFirstRemainder (goldbachDifferenceCarrier N ε) N
            ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ))
            ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) +
            (goldbachWeightHighFirstCoefficient 0 - δ) *
              (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) ≤
            4 * (D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, hε₀u, hr⟩ := goldbachWeight_remainingFive_small_epsilon
    (δ / 2) (by positivity)
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨Nr, hNr, hrN⟩ := hr ε hε hεlt
  obtain ⟨Ns, _hNs, hs⟩ := goldbachS5HighFirstClosed_normalized_upper_integral
    (δ / 2) ε (by positivity) hε (hεlt.trans_le hε₀u)
  refine ⟨max Nr Ns, hNr.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hbase := hrN N ((le_max_left _ _).trans hN) hEven
  have hupper := hs N ((le_max_right _ _).trans hN) hEven
  have hN4 : 4 ≤ N := hNr.trans ((le_max_left _ _).trans hN)
  have hz : (N : ℝ) ^ (4 / 53 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  rw [goldbachWeightRemainingFive_eq_lowFirstRemainder_sub_high _ _ _ _ _ hz] at hbase
  push_cast at hbase
  unfold goldbachWeightHighFirstCoefficient
  nlinarith [hbase, hupper]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig