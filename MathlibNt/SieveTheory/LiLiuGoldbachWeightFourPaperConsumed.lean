import MathlibNt.SieveTheory.LiLiuGoldbachS5PaperSplitUpper
import MathlibNt.SieveTheory.LiLiuGoldbachWeightHighFirstConsumed

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The remaining-four coefficient after consuming the actual paper-split S5 bound. -/
def goldbachWeightFourPaperCoefficient (ε : ℝ) : ℝ :=
  goldbachWeightFiveCoefficient ε - goldbachB9PaperSplitIntegral

/-- Agreement with the previously consumed high term and the new low term. -/
theorem goldbachWeightFourPaperCoefficient_eq_high_sub_low (ε : ℝ) :
    goldbachWeightFourPaperCoefficient ε =
      goldbachWeightHighFirstCoefficient ε - (36/5 : ℝ)*fouvryG9RelaxedIntegralLow := by
  unfold goldbachWeightFourPaperCoefficient goldbachWeightHighFirstCoefficient
  rw [goldbachB9PaperSplitIntegral_eq_low_high]
  ring

/-- The new full S5 producer is actually applied to the signed weight inequality.
No analytic premise or sign assumption on the remaining four terms is introduced. -/
theorem goldbachWeight_remainingFour_paperSplit_consumed_eventually
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ)/15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachWeightRemainingFour (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) : ℝ) +
        (goldbachWeightFourPaperCoefficient ε-δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
        4*(D19 N : ℝ) := by
  obtain ⟨Nr,hNr,hr⟩ := goldbachWeight_remainingFive_S1_S2_S3_S4_I10_consumed_eventually
    (δ/2) ε (by positivity) hε hεu
  obtain ⟨Ns,_,hs⟩ := goldbachS5Closed_normalized_upper_paperSplit
    (δ/2) ε (by positivity) hε hεu
  refine ⟨max Nr Ns,hNr.trans (le_max_left _ _),?_⟩
  intro N hN hEven
  have hbase := hr N ((le_max_left _ _).trans hN) hEven
  have hupper := hs N ((le_max_right _ _).trans hN) hEven
  rw [goldbachWeightRemainingFive_eq_remainingFour_sub_s5] at hbase
  push_cast at hbase
  unfold goldbachWeightFourPaperCoefficient
  nlinarith

/-- The small-epsilon threshold is chosen first; each fixed epsilon then has
one common natural-number threshold for the true counting inequality. -/
theorem goldbachWeight_remainingFour_paperSplit_consumed_small_epsilon
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachWeightRemainingFour (goldbachDifferenceCarrier N ε) N
            ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) : ℝ) +
            (goldbachWeightFourPaperCoefficient 0-δ)*
              (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
            4*(D19 N : ℝ) := by
  obtain ⟨ε₀,hε₀,hε₀u,hr⟩ := goldbachWeight_remainingFive_small_epsilon
    (δ/2) (by positivity)
  refine ⟨ε₀,hε₀,hε₀u,?_⟩
  intro ε hε hεlt
  obtain ⟨Nr,hNr,hrN⟩ := hr ε hε hεlt
  obtain ⟨Ns,_,hs⟩ := goldbachS5Closed_normalized_upper_paperSplit
    (δ/2) ε (by positivity) hε (hεlt.trans_le hε₀u)
  refine ⟨max Nr Ns,hNr.trans (le_max_left _ _),?_⟩
  intro N hN hEven
  have hbase := hrN N ((le_max_left _ _).trans hN) hEven
  have hupper := hs N ((le_max_right _ _).trans hN) hEven
  rw [goldbachWeightRemainingFive_eq_remainingFour_sub_s5] at hbase
  push_cast at hbase
  unfold goldbachWeightFourPaperCoefficient
  nlinarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
