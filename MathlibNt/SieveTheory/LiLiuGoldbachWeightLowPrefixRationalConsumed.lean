import MathlibNt.SieveTheory.LiLiuGoldbachWeightHighFirstRationalConsumed
import MathlibNt.SieveTheory.LiLiuGoldbachB9LowPositivePrefixTransport

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual low mother is retained; its analytic estimate is not assumed. -/
theorem goldbachWeight_lowPrefix_rational_consumed_small_epsilon
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ∀ Z : ℝ, 1 ≤ Z → Z ≤ Real.sqrt (N : ℝ) →
            (goldbachWeightRemainingFour (goldbachDifferenceCarrier N ε) N
              ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
              ((N : ℝ)^(3/11 : ℝ)) : ℝ) -
              (goldbachB9LowPositivePrefixSiftedCount N ε Z : ℝ) +
              ((62033529/100000000 : ℝ)-392796161/100000000-δ)*
                (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
              4*(D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, hε₀u, h⟩ :=
    goldbachWeight_highFirst_rational_consumed_small_epsilon (δ/2) (by positivity)
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨Nr, hNr, hr⟩ := h ε hε hεlt
  obtain ⟨Nl, _hNl, hl⟩ :=
    goldbachS5ClosedBelow_le_positivePrefix_sifted_normalized_of_pos ε (δ/2) hε (by positivity)
  refine ⟨max Nr Nl, hNr.trans (le_max_left _ _), ?_⟩
  intro N hN hEven Z hZ hZu
  have hbase := hr N ((le_max_left _ _).trans hN) hEven
  have hlow := hl N ((le_max_right _ _).trans hN) Z hZ hZu
  unfold goldbachWeightLowFirstRemainder at hbase
  push_cast at hbase
  nlinarith [hbase, hlow]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig