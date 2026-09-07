import MathlibNt.SieveTheory.LiLiuGoldbachS5PaperSplitUpper
import MathlibNt.SieveTheory.LiLiuGoldbachWeightAllRetainedEndpointsConsumed
import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorActualProducer

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The already proved sharper S3, S4 and B10 constants are retained without recomputation.
The full paper-split S5 bound and the certified actual G11 bound are consumed
in the same original weight inequality. The author bound consumes its own third
of the error budget; no constant is added back to an already weakened ledger.
Only the literal G6 + G7 - G12 remains.
This is a signed counting bound, not an assertion of final positivity. -/
theorem goldbachWeight_paperSplit_authorG11_consumed_small_epsilon
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ((goldbachWeightG6 (goldbachDifferenceCarrier N ε) N
              ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) +
            goldbachWeightG7 (goldbachDifferenceCarrier N ε) N
              ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) -
            goldbachWeightG12 (goldbachDifferenceCarrier N ε) N
              ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) : ℤ) : ℝ) +
            ((124341093/200000000 : ℝ)-goldbachB9PaperSplitIntegral-
              10191/100000-δ)*
              (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
            4*(D19 N : ℝ) := by
  obtain ⟨ε₀,hε₀,hε₀u,hr⟩ := goldbachWeight_remainingFive_allRetained_small_epsilon
    (δ/3) (by positivity)
  refine ⟨ε₀,hε₀,hε₀u,?_⟩
  intro ε hε hεlt
  obtain ⟨Nr,hNr,hrN⟩ := hr ε hε hεlt
  obtain ⟨Ns,_,hs⟩ := goldbachS5Closed_normalized_upper_paperSplit
    (δ/3) ε (by positivity) hε (hεlt.trans_le hε₀u)
  obtain ⟨Ng,_,hg⟩ := goldbachWeightG11_le_authorScalar_direct (δ/3) ε
    (by positivity) hε (by linarith [hεlt.trans_le hε₀u])
  refine ⟨max Nr (max Ns Ng),by omega,?_⟩
  intro N hN hEven
  have hbase := hrN N (by omega) hEven
  have hs5 := hs N (by omega) hEven
  have hg11 := hg N (by omega) hEven
  rw [goldbachWeightRemainingFive_eq_remainingFour_sub_s5] at hbase
  unfold goldbachWeightRemainingFour at hbase
  push_cast at hbase
  push_cast
  nlinarith [hbase,hs5,hg11]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig