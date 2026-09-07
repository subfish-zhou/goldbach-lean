import MathlibNt.SieveTheory.LiLiuGoldbachS5PaperSplitUpper
import MathlibNt.SieveTheory.LiLiuGoldbachPositiveScalarClosed
import MathlibNt.SieveTheory.LiLiuGoldbachG11UniformScalarCount

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The full paper-split S5 bound and the certified actual G11 bound are consumed
in the same original weight inequality. Only the literal G6 + G7 - G12 remains.
This is a signed counting bound, not an assertion of final positivity. -/
theorem goldbachWeight_paperSplit_uniformG11_consumed_small_epsilon
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
            ((62033529/100000000 : ℝ)-goldbachB9PaperSplitIntegral-
              10385101/100000000-δ)*
              (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
            4*(D19 N : ℝ) := by
  obtain ⟨Ng,_,hg⟩ := goldbachWeightG11_le_uniformScalar_numeric_fixed
  obtain ⟨ε₀,hε₀,hε₀u,hr⟩ := goldbachWeight_remainingFive_rationalPositiveScalar_small_epsilon
    (δ/2) (by positivity)
  refine ⟨ε₀,hε₀,hε₀u,?_⟩
  intro ε hε hεlt
  obtain ⟨Nr,hNr,hrN⟩ := hr ε hε hεlt
  obtain ⟨Ns,_,hs⟩ := goldbachS5Closed_normalized_upper_paperSplit
    (δ/2) ε (by positivity) hε (hεlt.trans_le hε₀u)
  refine ⟨max Nr (max Ns Ng),by omega,?_⟩
  intro N hN hEven
  have hbase := hrN N (by omega) hEven
  have hs5 := hs N (by omega) hEven
  have hg11 := hg N (by omega) hEven ε hε.le
  rw [goldbachWeightRemainingFive_eq_remainingFour_sub_s5] at hbase
  unfold goldbachWeightRemainingFour at hbase
  push_cast at hbase
  push_cast
  nlinarith [hbase,hs5,hg11]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
