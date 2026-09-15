import MathlibNt.Wu2008DoubleSieve.TruncatedSixth
import MathlibNt.Wu2008DoubleSieve.BoxMassUniform
import MathlibNt.Wu2008DoubleSieve.Omega3XNormalization

/-!
# Arbitrarily small relative error for the truncated-sixth variant

Only the proved finite power error is paid. This does not identify the
variant with the original expression or supply a numerical lower bound
for its truncated positive term.
-/

namespace Wu2008DoubleSieve

open Real Filter
open scoped Topology

theorem truncatedSixth_error_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧ 2 ≤ (N : ℝ) ^ (100 / 1327 : ℝ) ∧
      truncatedSixthErrorConstant * (N : ℝ) ^ (1 - (100 / 1327 : ℝ)) ≤
        ε * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  have hκ : (0 : ℝ) < 100 / 1327 := by norm_num
  have hK := truncatedSixthErrorConstant_pos
  have hC1 : 0 < wuSingularSeries 1 := wuSingularSeries_pos 1 (by norm_num)
  have hbudget := box_eventually_log_power_budget 2
    (show 0 < truncatedSixthErrorConstant / (ε * wuSingularSeries 1) by positivity) hκ
  have hz := ((tendsto_rpow_atTop hκ).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (2 : ℝ))
  filter_upwards [eventually_ge_atTop (4 : ℕ), hz, hbudget] with N hN hcut hpay
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC := wuSingularSeries_le_of_dvd (by norm_num : 0 < (1 : ℕ))
    (by omega : 0 < N) (one_dvd N)
  refine ⟨hN, hcut, ?_⟩
  calc
    truncatedSixthErrorConstant * (N : ℝ) ^ (1 - (100 / 1327 : ℝ)) =
        (truncatedSixthErrorConstant * N) / (N : ℝ) ^ (100 / 1327 : ℝ) := by
      rw [rpow_sub hN0, rpow_one]
      ring
    _ ≤ (truncatedSixthErrorConstant * N) /
        ((truncatedSixthErrorConstant / (ε * wuSingularSeries 1)) *
          log (N : ℝ) ^ (2 : ℕ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hpay
    _ = ε * wuSingularSeries 1 * N / log N ^ (2 : ℕ) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hε.le) hN0.le)
      (sq_nonneg _)

/-- An actual upper bound for Esharp at the fixed source parameters,
with epsilon chosen before the common threshold and every even N. -/
theorem truncatedSixth_fixed_relative {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (truncatedSixthFixedExpression N : ℝ) ≤
        4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
          ε * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (truncatedSixth_error_eventually hε)
  refine ⟨max T 4, le_max_right _ _, ?_⟩
  intro N hN he
  obtain ⟨hN4, hz, hpay⟩ := hT N ((le_max_left _ _).trans hN)
  exact (truncatedSixth_fixed_le_count hN4 he hz).trans (add_le_add le_rfl hpay)

end Wu2008DoubleSieve
