import MathlibNt.SieveTheory.LiLiuGoldbachWeightLowPrefixRationalConsumed
import MathlibNt.SieveTheory.LiLiuGoldbachG11UniformScalarCount

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Exact cancellation of the intermediate rough and switched bookkeeping counts. -/
theorem goldbachWeightG11PaidBase_eq_actual (N : ℕ) (ε : ℝ) :
    goldbachWeightG11PaidBase N ε =
      goldbachWeightRemainingFour (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) +
      goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) := by
  unfold goldbachWeightG11PaidBase goldbachWeightG11GoodRemainder
    goldbachWeightG11RoughRemainder
  ring

/-- All coefficients evaluated here come from accepted actual producers.
The signed paid base and the strict-low positive-prefix count remain unestimated. -/
theorem goldbachWeight_uniformRational_consumed_small_epsilon
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ∀ Z : ℝ, 1 ≤ Z → Z ≤ Real.sqrt (N : ℝ) →
            (goldbachWeightG11PaidBase N ε : ℝ) -
              (goldbachB9LowPositivePrefixSiftedCount N ε Z : ℝ) +
              ((62033529/100000000 : ℝ)-392796161/100000000-10385101/100000000-δ)*
                (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
              4*(D19 N : ℝ) := by
  obtain ⟨Ng, _hNg, hg⟩ := goldbachWeightG11_le_uniformScalar_numeric_fixed
  obtain ⟨ε₀, hε₀, hε₀u, h⟩ := goldbachWeight_lowPrefix_rational_consumed_small_epsilon δ hδ
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨Nr, hNr, hr⟩ := h ε hε hεlt
  refine ⟨max Nr Ng, hNr.trans (le_max_left _ _), ?_⟩
  intro N hN hEven Z hZ hZu
  have hbase := hr N ((le_max_left _ _).trans hN) hEven Z hZ hZu
  have hupper := hg N ((le_max_right _ _).trans hN) hEven ε hε.le
  rw [goldbachWeightG11PaidBase_eq_actual]
  push_cast
  nlinarith [hbase, hupper]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig