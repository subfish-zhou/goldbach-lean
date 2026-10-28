import MathlibNt.SieveTheory.LiLiuGoldbachG67PaidLower
import MathlibNt.SieveTheory.LiuSingularSeries

open Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- One extra logarithm absorbs a fixed BV constant into the actual
singular-series-normalized error, uniformly in the ambient integer. -/
theorem goldbachBV_logCube_normalized (C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) / Real.log (N : ℝ)^3 ≤
        δ * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
  have hc := SingularSeries.liuUniversalProduct_pos
  have hl : ∀ᶠ N : ℕ in atTop,
      C / (δ * SingularSeries.liuUniversalProduct) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (4 : ℕ), hl] with N hN hl
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hb : C ≤ δ * SingularSeries.liuSingularSeries N * Real.log (N : ℝ) := by
    calc
      C ≤ δ * SingularSeries.liuUniversalProduct * Real.log (N : ℝ) :=
        (div_le_iff₀ (mul_pos hδ hc)).mp hl |>.trans_eq (mul_comm _ _)
      _ ≤ δ * SingularSeries.liuSingularSeries N * Real.log (N : ℝ) := by
        gcongr
        exact SingularSeries.liuUniversalProduct_le_liuSingularSeries N
  calc
    C * (N : ℝ) / Real.log (N : ℝ)^3 ≤
        (δ * SingularSeries.liuSingularSeries N * Real.log (N : ℝ)) *
          (N : ℝ) / Real.log (N : ℝ)^3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb hn0) (by positivity)
    _ = δ * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
      field_simp


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
