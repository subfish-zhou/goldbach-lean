import MathlibNt.SieveTheory.LiLiuGoldbachWeightRemainingSix
import MathlibNt.SieveTheory.LiLiuGoldbachS3NormalizedUpper

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Both actual S3 upper bounds are consumed in the actual D19 inequality.
The six remaining signed counts are kept literally, with no positivity premise. -/
theorem goldbachWeight_remainingSix_S1_S2_S3_I10_consumed_eventually
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachWeightRemainingSix (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ))
        ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) +
        (goldbachWeightSixCoefficient ε - δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) ≤
        4 * (D19 N : ℝ) := by
  obtain ⟨N8, hN8, h8⟩ := goldbachWeight_remainingEight_S1_S2_I10_consumed_eventually
    (δ / 3) ε (by positivity) hε hεu
  obtain ⟨Na, _hNa, ha⟩ := goldbachS3_normalized_upper (1 / 3) (δ / 3) ε
    (by norm_num) le_rfl (by positivity) hε hεu
  obtain ⟨Nb, _hNb, hb⟩ := goldbachS3_normalized_upper (3 / 11) (δ / 3) ε
    (by norm_num) (by norm_num) (by positivity) hε hεu
  refine ⟨max N8 (max Na Nb), hN8.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hN8' : N8 ≤ N := (le_max_left _ _).trans hN
  have hNa' : Na ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNb' : Nb ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let A := goldbachDifferenceCarrier N ε
  let z : ℝ := (N : ℝ) ^ (4 / 53 : ℝ)
  let b : ℝ := (N : ℝ) ^ (4 / 33 : ℝ)
  let c : ℝ := (N : ℝ) ^ (3 / 11 : ℝ)
  let M : ℝ := SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2
  have hbase : (goldbachWeightRemainingEight A N z b c : ℝ) +
      (goldbachWeightKnownCoefficient ε - δ / 3) * M ≤ 4 * (D19 N : ℝ) := by
    have hh := h8 N hN8' hEven
    dsimp only [goldbachWeightKnownCoefficient, goldbachS2LogCoefficient, A, z, b, c, M]
    convert hh using 1
    ring
  rw [goldbachWeightRemainingEight_eq_remainingSix_sub_s3Pair] at hbase
  push_cast at hbase
  have hfirst := ha N hNa' hEven
  have hsecond := hb N hNb' hEven
  dsimp only [A, z, b, c, M] at hbase
  unfold goldbachWeightSixCoefficient
  nlinarith [hbase, hfirst, hsecond]

/-- A single small-epsilon choice freezes the complete consumed coefficient,
while retaining the actual epsilon-dependent remaining six counts. -/
theorem goldbachWeight_remainingSix_small_epsilon (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2 / 15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachWeightRemainingSix (goldbachDifferenceCarrier N ε) N
            ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ))
            ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) +
            (goldbachWeightSixCoefficient 0 - δ) *
              (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) ≤
            4 * (D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, hε₀u, hc⟩ :=
    goldbachWeightSixCoefficient_small_epsilon (δ / 2) (by positivity)
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨N₀, hN₀, hn⟩ := goldbachWeight_remainingSix_S1_S2_S3_I10_consumed_eventually
    (δ / 2) ε (by positivity) hε (hεlt.trans_le hε₀u)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven
  have hcoef : goldbachWeightSixCoefficient 0 - δ ≤
      goldbachWeightSixCoefficient ε - δ / 2 := by
    have hh := (abs_lt.mp (hc ε hε hεlt)).1
    linarith
  have hM : 0 ≤ SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hcoef hM
  have hbound := hn N hN hEven
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig