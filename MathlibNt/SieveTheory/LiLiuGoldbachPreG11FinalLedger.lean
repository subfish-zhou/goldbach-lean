import MathlibNt.SieveTheory.LiLiuGoldbachWeightAllRetainedEndpointsConsumed

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Unconditional ledger BEFORE estimating G11 or the remaining signed counts. -/
theorem goldbachWeight_preG11_allRetained_small_epsilon
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ∀ Z : ℝ, 1 ≤ Z → Z ≤ Real.sqrt (N : ℝ) →
            (goldbachWeightG11PaidBase N ε : ℝ) -
              (goldbachB9LowPositivePrefixSiftedCount N ε Z : ℝ) -
              (goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
                ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) : ℝ) +
              (-(661251229/200000000 : ℝ)-δ)*
                (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
              4*(D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, hε₀u, h⟩ :=
    goldbachWeight_remainingFive_allRetained_small_epsilon (δ/3) (by positivity)
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨Nr, hNr, hr⟩ := h ε hε hεlt
  obtain ⟨Nh, _hNh, hh⟩ := goldbachS5HighFirstClosed_normalized_upper_392796161
    (δ/3) ε (by positivity) hε (hεlt.trans_le hε₀u)
  obtain ⟨Nl, _hNl, hl⟩ :=
    goldbachS5ClosedBelow_le_positivePrefix_sifted_normalized_of_pos ε (δ/3) hε (by positivity)
  refine ⟨max Nr (max Nh Nl), by omega, ?_⟩
  intro N hN hEven Z hZ hZu
  have hb := hr N (by omega) hEven
  have hhigh := hh N (by omega) hEven
  have hlow := hl N (by omega) Z hZ hZu
  have hz : (N : ℝ)^(4/53 : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  rw [goldbachWeightRemainingFive_eq_lowFirstRemainder_sub_high _ _ _ _ _ hz] at hb
  unfold goldbachWeightLowFirstRemainder at hb
  push_cast at hb
  rw [goldbachWeightG11PaidBase_eq_actual]
  push_cast
  nlinarith [hb, hhigh, hlow]


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig