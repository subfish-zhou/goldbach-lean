import MathlibNt.SieveTheory.LiLiuGoldbachS1BetaFixedNormalizedLower
import MathlibNt.SieveTheory.LiLiuGoldbachS1BetaFactorContinuity

noncomputable section

open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false

private theorem S1BetaNormalizedLower_mainConst_pos :
    0 < (33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) := by
  positivity

/-- The beta lower bound at the true endpoint `33 / 8` is obtained by first
choosing a fixed admissible `s < 33 / 8` from continuity of the genuine lower
sieve factor and then invoking the fixed-`s` normalized lower bound. -/
theorem goldbachS1_beta_normalized_lower
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        (((33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) * (1 - ε) *
              dimensionOneLowerLinearSieveFactor (33 / 8 : ℝ) - δ) *
            SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) ≤
          (goldbachS1 (goldbachDifferenceCarrier N ε) N
            ((N : ℝ) ^ (4 / 33 : ℝ)) : ℝ)) := by
  let A : ℝ := (33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant)
  let η : ℝ := δ / (2 * A)
  have hA : 0 < A := by
    dsimp [A]
    exact S1BetaNormalizedLower_mainConst_pos
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨s, hs4, hslt, hs⟩ := goldbachS1_exists_betaRatio_below η hη
  intro ε hε hεu
  obtain ⟨N₀, hN₀, hmain⟩ :=
    goldbachS1_beta_fixed_normalized_lower s (δ / 2) hs4 hslt hδ2 ε hε hεu
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven
  let T : ℝ := SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ)
  let RHS : ℝ :=
    (goldbachS1 (goldbachDifferenceCarrier N ε) N
      ((N : ℝ) ^ (4 / 33 : ℝ)) : ℝ)
  have hTnonneg : 0 ≤ T := by
    dsimp [T]
    have hlogN : 0 < Real.log (N : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hlogSq : 0 < Real.log (N : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos hlogN 2
    exact div_nonneg
      (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg N))
      hlogSq.le
  have hcoef :
      A * (1 - ε) * dimensionOneLowerLinearSieveFactor (33 / 8 : ℝ) - δ ≤
        A * (1 - ε) * dimensionOneLowerLinearSieveFactor s - δ / 2 := by
    have hscaleNonneg : 0 ≤ A * (1 - ε) := by positivity
    have hscaled :
        A * (1 - ε) *
            (dimensionOneLowerLinearSieveFactor (33 / 8 : ℝ) - η) ≤
          A * (1 - ε) * dimensionOneLowerLinearSieveFactor s :=
      mul_le_mul_of_nonneg_left hs hscaleNonneg
    have hηbound : A * (1 - ε) * η ≤ δ / 2 := by
      dsimp [η, A]
      have hεle : 1 - ε ≤ 1 := by linarith
      have htmp : (1 - ε) * (δ / 2) ≤ δ / 2 := by
        nlinarith
      have hEq : ((33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant)) *
            (1 - ε) *
            (δ /
              (2 * ((33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant)))) =
          (1 - ε) * (δ / 2) := by
        field_simp [S1BetaNormalizedLower_mainConst_pos.ne']
      rw [hEq]
      exact htmp
    nlinarith
  have hfixed :
      (A * (1 - ε) * dimensionOneLowerLinearSieveFactor s - δ / 2) * T ≤ RHS := by
    simpa [A, T, RHS, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
      hmain N hN hEven
  have hgoal :
      (A * (1 - ε) * dimensionOneLowerLinearSieveFactor (33 / 8 : ℝ) - δ) * T ≤ RHS := by
    exact (mul_le_mul_of_nonneg_right hcoef hTnonneg).trans hfixed
  convert hgoal using 1
  ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig