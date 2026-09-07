import MathlibNt.SieveTheory.LiLiuGoldbachB9LowPositivePrefixTransport
import MathlibNt.SieveTheory.LiLiuGoldbachWeightHighFirstConsumed

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The low term is replaced by its actual positive-prefix sifted mother, not an analytic estimate.
The prime-size threshold is uniform in the subsequently chosen sieve cutoff. -/
theorem goldbachWeight_lowPositivePrefix_consumed_eventually
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      ∀ Z : ℝ, 1 ≤ Z → Z ≤ Real.sqrt (N : ℝ) →
        (goldbachWeightRemainingFour (goldbachDifferenceCarrier N ε) N
          ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ))
          ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) -
          (goldbachB9LowPositivePrefixSiftedCount N ε Z : ℝ) +
          (goldbachWeightHighFirstCoefficient ε - δ) *
            (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) ≤
          4 * (D19 N : ℝ) := by
  obtain ⟨Nr, hNr, hr⟩ := goldbachWeight_highFirst_consumed_eventually
    (δ / 2) ε (by positivity) hε hεu
  obtain ⟨Nl, _hNl, hl⟩ := goldbachS5ClosedBelow_le_positivePrefix_sifted_normalized_of_pos
    ε (δ / 2) hε (by positivity)
  refine ⟨max Nr Nl, hNr.trans (le_max_left _ _), ?_⟩
  intro N hN hEven Z hZ hZu
  have hbase := hr N ((le_max_left _ _).trans hN) hEven
  have hlow := hl N ((le_max_right _ _).trans hN) Z hZ hZu
  unfold goldbachWeightLowFirstRemainder at hbase
  push_cast at hbase
  nlinarith [hbase, hlow]

/-- The small-epsilon order is unchanged, and Z remains after the prime-size threshold. -/
theorem goldbachWeight_lowPositivePrefix_consumed_small_epsilon (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2 / 15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ∀ Z : ℝ, 1 ≤ Z → Z ≤ Real.sqrt (N : ℝ) →
            (goldbachWeightRemainingFour (goldbachDifferenceCarrier N ε) N
              ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ))
              ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) -
              (goldbachB9LowPositivePrefixSiftedCount N ε Z : ℝ) +
              (goldbachWeightHighFirstCoefficient 0 - δ) *
                (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) ≤
              4 * (D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, hε₀u, hr⟩ := goldbachWeight_highFirst_consumed_small_epsilon
    (δ / 2) (by positivity)
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨Nr, hNr, hrN⟩ := hr ε hε hεlt
  obtain ⟨Nl, _hNl, hl⟩ := goldbachS5ClosedBelow_le_positivePrefix_sifted_normalized_of_pos
    ε (δ / 2) hε (by positivity)
  refine ⟨max Nr Nl, hNr.trans (le_max_left _ _), ?_⟩
  intro N hN hEven Z hZ hZu
  have hbase := hrN N ((le_max_left _ _).trans hN) hEven
  have hlow := hl N ((le_max_right _ _).trans hN) Z hZ hZu
  unfold goldbachWeightLowFirstRemainder at hbase
  push_cast at hbase
  nlinarith [hbase, hlow]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig