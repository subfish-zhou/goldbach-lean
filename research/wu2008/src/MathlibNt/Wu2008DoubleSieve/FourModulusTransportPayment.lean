import MathlibNt.Wu2008DoubleSieve.FourModulusTransport
import MathlibNt.Wu2008DoubleSieve.BoxMassUniform
import MathlibNt.Wu2008DoubleSieve.Omega3XNormalization

/-!
# Payment of the on-domain modulus difference

For fixed kappa and epsilon, one threshold precedes every remaining
cutoff. Only the joint modulus difference is paid, not moving-domain
excess or an eleven-term upper bound.
-/

namespace Wu2008DoubleSieve

open Real Filter
open scoped Topology

theorem fourModulus_power_budget {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧ 2 ≤ (N : ℝ) ^ κ ∧
      2 / κ ^ 4 * (N : ℝ) ^ (1 - κ) ≤
        ε * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  have hC1 : 0 < wuSingularSeries 1 := wuSingularSeries_pos 1 (by norm_num)
  have hbudget := box_eventually_log_power_budget 2
    (show 0 < 2 / (κ ^ 4 * ε * wuSingularSeries 1) by positivity) hκ
  have hz := ((tendsto_rpow_atTop hκ).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (2 : ℝ))
  filter_upwards [eventually_ge_atTop (4 : ℕ), hz, hbudget] with N hN hcut hpay
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC := wuSingularSeries_le_of_dvd (by norm_num : 0 < (1 : ℕ))
    (by omega : 0 < N) (one_dvd N)
  refine ⟨hN, hcut, ?_⟩
  calc
    2 / κ ^ 4 * (N : ℝ) ^ (1 - κ) =
        (2 / κ ^ 4 * N) / (N : ℝ) ^ κ := by rw [rpow_sub hN0, rpow_one]; ring
    _ ≤ (2 / κ ^ 4 * N) /
        ((2 / (κ ^ 4 * ε * wuSingularSeries 1)) * log (N : ℝ) ^ (2 : ℕ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hpay
    _ = ε * wuSingularSeries 1 * N / log N ^ (2 : ℕ) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hε.le) hN0.le)
      (sq_nonneg _)

theorem fourModulus_eleven_relative {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ w u v V : ℝ,
      0 ≤ (fourModulusQuotientEleven N ((N : ℝ) ^ κ) w u v V : ℝ) -
        (finiteElevenMixed N ((N : ℝ) ^ κ) w u v V : ℝ) ∧
      (fourModulusQuotientEleven N ((N : ℝ) ^ κ) w u v V : ℝ) -
        (finiteElevenMixed N ((N : ℝ) ^ κ) w u v V : ℝ) ≤
          ε * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (fourModulus_power_budget hκ hε)
  refine ⟨max T 4, le_max_right _ _, ?_⟩
  intro N hN he w u v V
  obtain ⟨hN4, hz, hpay⟩ := hT N ((le_max_left _ _).trans hN)
  have h := fourModulus_eleven_bounds (w := w) (u := u) (v := v) (V := V)
    hN4 he hκ hz
  exact ⟨h.1, h.2.trans hpay⟩

/-- The actual fixed Section 5 cutoffs, including the moving product
cutoff V. The threshold depends on epsilon, not on N. -/
theorem fourModulus_eleven_fixed_relative {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      let κ₁ : ℝ := 100 / 1327
      let κ₂ : ℝ := 25 / 206
      let z := (N : ℝ) ^ κ₁
      let w := (N : ℝ) ^ κ₂
      let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
      let v := (N : ℝ) ^ (1 / 3 : ℝ)
      let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁)
      0 ≤ (fourModulusQuotientEleven N z w u v V : ℝ) -
        (finiteElevenMixed N z w u v V : ℝ) ∧
      (fourModulusQuotientEleven N z w u v V : ℝ) -
        (finiteElevenMixed N z w u v V : ℝ) ≤
          ε * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  obtain ⟨T, hT, h⟩ := fourModulus_eleven_relative
    (by norm_num : (0 : ℝ) < 100 / 1327) hε
  exact ⟨T, hT, fun N hN he => h N hN he _ _ _ _⟩

end Wu2008DoubleSieve
