import MathlibNt.SieveTheory.LiLiuGoldbachPaperSplitAllRetainedConsumed
import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughPaid

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The two G12 exceptional classes are actually absorbed in the strongest
weight ledger. The remaining negative sum uses exactly the G12 cross labels. -/
theorem goldbachWeight_G12Rough_allRetained_small_epsilon (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ((goldbachWeightG6 (goldbachDifferenceCarrier N ε) N
              ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) +
            goldbachWeightG7 (goldbachDifferenceCarrier N ε) N
              ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
              ((N : ℝ)^(3/11 : ℝ)) : ℤ) : ℝ) -
          ((∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ))
              ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)),
            goldbachG11RoughCount N ε v : ℤ) : ℝ) +
          ((124341093/200000000 : ℝ) - goldbachB9PaperSplitIntegral -
            10385101/100000000 - δ) *
            (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) ≤
          4 * (D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, hε₀u, hbase⟩ :=
    goldbachWeight_paperSplit_allRetainedG11_consumed_small_epsilon (δ/2) (by positivity)
  obtain ⟨Ne, _, he⟩ := goldbachWeightG12_le_roughSum_add_normalized (δ/2) (by positivity)
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨Nb, hNb, hb⟩ := hbase ε hε hεlt
  refine ⟨max Nb Ne, by omega, ?_⟩
  intro N hN hEven
  have hmain := hb N (by omega) hEven
  have hrough := he N (by omega) ε hε.le
    ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ))
  push_cast at hmain hrough ⊢
  nlinarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
