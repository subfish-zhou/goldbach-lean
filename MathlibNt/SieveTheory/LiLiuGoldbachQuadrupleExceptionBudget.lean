import MathlibNt.SieveTheory.LiLiuGoldbachQuadrupleExceptionFibers
import MathlibNt.SieveTheory.LiLiuGoldbachS5CountTransport

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachQuadruple_exceptions_normalized (delta : ℝ) (hdelta : 0 < delta) :
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ eps : ℝ, 0 ≤ eps → ∀ b : ℝ,
      (((∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
          b,
          goldbachG11RSquareCount (goldbachDifferenceCarrier N eps) v) +
        (∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
          b,
          goldbachG11NCount (goldbachDifferenceCarrier N eps) N v) : ℤ) : ℝ) ≤
        delta * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  obtain ⟨Ns, hNs, hs⟩ := goldbachS5SquareCount_normalized (delta / 800) (by positivity)
  obtain ⟨Nb, _hNb, hb⟩ := goldbachS4_finiteLoss_normalized (delta / 800) (by positivity)
  refine ⟨max Ns Nb, hNs.trans (le_max_left _ _), ?_⟩
  intro N hN eps heps b
  have hsquare := hs N ((le_max_left _ _).trans hN)
  have hbad := hb N ((le_max_right _ _).trans hN) eps 0
    le_rfl (Real.sqrt_nonneg _)
  simp only [Nat.floor_zero, Nat.cast_zero, mul_zero, add_zero] at hbad
  have hr :
      ((∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
        b,
        goldbachG11RSquareCount (goldbachDifferenceCarrier N eps) v) : ℝ) ≤
          160000 * (goldbachS5SquareCount N : ℝ) := by
    exact_mod_cast goldbachQuadrupleRSquareCount_sum_le N eps b heps
  have hn :
      ((∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
        b,
        goldbachG11NCount (goldbachDifferenceCarrier N eps) N v) : ℝ) ≤
          160000 * (goldbachBadCount (goldbachDifferenceCarrier N eps) N : ℝ) := by
    exact_mod_cast goldbachQuadrupleNCount_sum_le N eps b heps
  have hscaledSquare := mul_le_mul_of_nonneg_left hsquare
    (by norm_num : (0 : ℝ) ≤ 400)
  have hscaledBad := mul_le_mul_of_nonneg_left hbad
    (by norm_num : (0 : ℝ) ≤ 400)
  push_cast
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig