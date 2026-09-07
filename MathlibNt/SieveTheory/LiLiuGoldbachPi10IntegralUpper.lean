import MathlibNt.SieveTheory.LiLiuGoldbachPi10NormalizedUpper
import MathlibNt.SieveTheory.LiLiuGoldbachB10IntegralUpper

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual integer Pi10 count is bounded by the printed integral; the
auxiliary sieve cutoff and all finite small-output losses have been paid. -/
theorem goldbachPi10_I10_upper (δ : ℝ) (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        (goldbachPi10 N ε ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma) : ℝ) ≤
          (8 * (1 - ε) * goldbachB10I10 + δ) *
            (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log (N : ℝ) ^ 2) := by
  let e : ℝ := min 1 (δ / (goldbachB10I10 + 10))
  have hi := goldbachB10I10_nonneg
  have he : 0 < e := lt_min zero_lt_one (by positivity)
  have he1 : e ≤ 1 := min_le_left _ _
  have heδ : e * (goldbachB10I10 + 10) ≤ δ :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  intro ε hε hεlt
  obtain ⟨Np, hNp, hp⟩ := goldbachPi10_normalized_upper e he ε goldbachB10Gamma
    hε hεlt (by norm_num [goldbachB10Gamma])
  obtain ⟨Nm, _hNm, hm⟩ := goldbachB10MainMass_le_I10_eventually ε e hε hεlt he
  refine ⟨max Np Nm, hNp.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hNp' : Np ≤ N := (le_max_left _ _).trans hN
  have hN4 : 4 ≤ N := hNp.trans hNp'
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let C := MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N
  let X := goldbachB10MainMass N ε ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma)
  let A := C * (N : ℝ) / Real.log (N : ℝ) ^ 2
  have hC : 0 ≤ C := (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N).le
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpN := hp N hNp' hEven goldbachB10Beta (by norm_num [goldbachB10Beta])
  have hmN := hm N ((le_max_right _ _).trans hN)
  have hesq : e ^ 2 ≤ e := by nlinarith [mul_le_mul_of_nonneg_left he1 he.le]
  have hc : (8 + e) * ((1 - ε) * goldbachB10I10 + e) + e ≤
      8 * (1 - ε) * goldbachB10I10 + δ := by
    have hneg : 0 ≤ e * ε * goldbachB10I10 := by positivity
    nlinarith
  have hmain : (8 + e) * C * X / Real.log (N : ℝ) ≤
      ((8 + e) * ((1 - ε) * goldbachB10I10 + e)) * A := by
    calc
      _ ≤ (8 + e) * C * (((1 - ε) * goldbachB10I10 + e) * ((N : ℝ) / Real.log (N : ℝ))) /
          Real.log (N : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmN (by positivity)) hlog.le
      _ = _ := by dsimp [A]; ring
  change _ ≤ (8 * (1 - ε) * goldbachB10I10 + δ) * A
  calc
    _ ≤ (8 + e) * C * X / Real.log (N : ℝ) + e * A := by
      simpa only [C, X, A, Real.rpow_two, mul_div_assoc, mul_assoc] using hpN
    _ ≤ ((8 + e) * ((1 - ε) * goldbachB10I10 + e)) * A + e * A := add_le_add hmain le_rfl
    _ = ((8 + e) * ((1 - ε) * goldbachB10I10 + e) + e) * A := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hA

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig