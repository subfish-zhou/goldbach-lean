import MathlibNt.SieveTheory.LiLiuGoldbachS2NormalizedUpper
import MathlibNt.SieveTheory.LiLiuGoldbachS1PositivePair
import MathlibNt.SieveTheory.LiLiuGoldbachWeightI10Consumer

open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The eight literal signed terms left after consuming both S1 terms and S2.
No analytic estimate or positivity is built into this finite expression. -/
noncomputable def goldbachWeightRemainingEight
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ) : ℤ :=
  -goldbachS3Closed A N z ((N : ℝ) ^ ((1 : ℝ) / 3)) - goldbachS3Closed A N z c +
    goldbachWeightG6 A N z b + goldbachWeightG7 A N z b c - 2 * goldbachS4 A N c -
    goldbachS5Closed A N z ((N : ℝ) ^ ((1 : ℝ) / 3)) -
    goldbachWeightG11 A N z b - goldbachWeightG12 A N z b c

theorem goldbachWeightTwelveBase_eq_positivePair_sub_s2_add_remainingEight
    (A : Finset ℕ) (N : ℕ) (z b c T : ℝ) :
    goldbachWeightTwelveBase A N z b c T =
      (3 * goldbachS1 A N z + goldbachS1 A N b) - 4 * goldbachS2 A N T +
        goldbachWeightRemainingEight A N z b c := by
  unfold goldbachWeightTwelveBase goldbachWeightRemainingEight
  ring

/-- Actual D19 consumer: both S1 lower bounds, the S2 upper bound (with its
external multiplicity four), and I10 are consumed. Eight signed terms remain. -/
theorem goldbachWeight_remainingEight_S1_S2_I10_consumed_eventually
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachWeightRemainingEight (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ))
        ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) +
      ((1 - ε) * Real.exp (-Real.eulerMascheroniConstant) *
          ((159 / 2 : ℝ) * dimensionOneLowerLinearSieveFactor 6 +
            (33 / 2 : ℝ) * dimensionOneLowerLinearSieveFactor (33 / 8 : ℝ)) -
        32 * Real.log ((1 - ((9 : ℝ) / 19 - ε)) / ((9 : ℝ) / 19 - ε)) -
        8 * (1 - ε) * goldbachB10I10 - δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) ≤
        4 * (D19 N : ℝ) := by
  have hε1 : ε < 1 := by linarith
  obtain ⟨Np, hNp, hp⟩ := goldbachS1_positivePair_normalized_lower
    (δ / 3) ε (by positivity) hε hε1
  obtain ⟨Ns, _hNs, hs⟩ := goldbachS2_normalized_upper_nine_nineteen_sub
    (δ / 12) ε (by positivity) hε hεu
  obtain ⟨Nb, _hNb, hb⟩ := goldbachWeight_twelve_base_I10_consumed_eventually
    (δ / 3) (by positivity) ε hε hεu
  refine ⟨max Np (max Ns Nb), hNp.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hNp' : Np ≤ N := (le_max_left _ _).trans hN
  have hNs' : Ns ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNb' : Nb ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let A := goldbachDifferenceCarrier N ε
  let z : ℝ := (N : ℝ) ^ (4 / 53 : ℝ)
  let b : ℝ := (N : ℝ) ^ (4 / 33 : ℝ)
  let c : ℝ := (N : ℝ) ^ (3 / 11 : ℝ)
  let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
  let M : ℝ := SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2
  let L : ℝ := (1 - ε) * Real.exp (-Real.eulerMascheroniConstant) *
    ((159 / 2 : ℝ) * dimensionOneLowerLinearSieveFactor 6 +
      (33 / 2 : ℝ) * dimensionOneLowerLinearSieveFactor (33 / 8 : ℝ))
  let K : ℝ := Real.log ((1 - ((9 : ℝ) / 19 - ε)) / ((9 : ℝ) / 19 - ε))
  let J : ℝ := 8 * (1 - ε) * goldbachB10I10
  have hpos : (L - δ / 3) * M ≤ ((3 * goldbachS1 A N z + goldbachS1 A N b : ℤ) : ℝ) :=
    hp N hNp' hEven
  have hneg : (goldbachS2 A N T : ℝ) ≤ (8 * K + δ / 12) * M := by
    simpa [A, T, K, M, div_eq_mul_inv, mul_assoc, Real.rpow_natCast] using hs N hNs' hEven
  have hbase := hb N hNb' hEven (4 / 53 : ℝ) (by norm_num)
    (by norm_num [goldbachB10Beta])
  change (goldbachWeightTwelveBase A N z b c T : ℝ) - (J + δ / 3) * M ≤
    4 * (D19 N : ℝ) at hbase
  rw [goldbachWeightTwelveBase_eq_positivePair_sub_s2_add_remainingEight] at hbase
  push_cast at hbase hpos
  change (goldbachWeightRemainingEight A N z b c : ℝ) +
    (L - 32 * K - J - δ) * M ≤ 4 * (D19 N : ℝ)
  nlinarith [hbase, hpos, hneg]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig