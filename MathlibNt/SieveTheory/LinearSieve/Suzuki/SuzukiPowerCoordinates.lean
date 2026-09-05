import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set

namespace MathlibNt.SieveTheory.SuzukiPowerCoordinates

/-- Logarithm of the upper power-coordinate endpoint. -/
theorem log_upper_endpoint
    {D s z : ℝ} (hD : 1 < D) (_hs : 0 < s)
    (hz : z = D ^ (1 / s)) :
    Real.log z = Real.log D / s := by
  have hD0 : 0 < D := zero_lt_one.trans hD
  rw [hz, Real.log_rpow hD0]
  ring

/-- Logarithm of the lower power-coordinate endpoint. -/
theorem log_lower_endpoint
    {D σ w : ℝ} (hD : 1 < D) (_hσ : 0 < σ)
    (hw : w = D ^ (1 / σ)) :
    Real.log w = Real.log D / σ := by
  have hD0 : 0 < D := zero_lt_one.trans hD
  rw [hw, Real.log_rpow hD0]
  ring

/-- The power-coordinate endpoints satisfy `1 < w ≤ z`. -/
theorem endpoints_order
    {D s σ w z : ℝ} (hD : 1 < D) (hs : 0 < s) (hsσ : s ≤ σ)
    (hz : z = D ^ (1 / s)) (hw : w = D ^ (1 / σ)) :
    1 < w ∧ w ≤ z := by
  have hσ : 0 < σ := hs.trans_le hsσ
  constructor
  · rw [hw]
    exact Real.one_lt_rpow hD (by positivity)
  · rw [hw, hz]
    exact Real.rpow_le_rpow_of_exponent_le hD.le
      (one_div_le_one_div_of_le hs hsσ)

/-- Every point between the power-coordinate endpoints maps back into `[s, σ]`
under Suzuki's coordinate `x ↦ log D / log x`. -/
theorem log_div_log_mem_Icc
    {D s σ w z x : ℝ} (hD : 1 < D) (hs : 0 < s) (hsσ : s ≤ σ)
    (hz : z = D ^ (1 / s)) (hw : w = D ^ (1 / σ))
    (hx : x ∈ Set.Icc w z) :
    Real.log D / Real.log x ∈ Set.Icc s σ := by
  have hσ : 0 < σ := hs.trans_le hsσ
  have hord := endpoints_order hD hs hsσ hz hw
  have hx1 : 1 < x := hord.1.trans_le hx.1
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hlogw : Real.log w = Real.log D / σ :=
    log_lower_endpoint hD hσ hw
  have hlogz : Real.log z = Real.log D / s :=
    log_upper_endpoint hD hs hz
  have hlogwx : Real.log w ≤ Real.log x :=
    Real.strictMonoOn_log.monotoneOn
      (zero_lt_one.trans hord.1) (zero_lt_one.trans hx1) hx.1
  have hlogxz : Real.log x ≤ Real.log z :=
    Real.strictMonoOn_log.monotoneOn
      (zero_lt_one.trans hx1)
      (zero_lt_one.trans (lt_of_lt_of_le hord.1 hord.2)) hx.2
  constructor
  · rw [le_div_iff₀ hlogx]
    rw [hlogz] at hlogxz
    have hs0 : s ≠ 0 := ne_of_gt hs
    field_simp [hs0] at hlogxz
    simpa [mul_comm] using hlogxz
  · rw [div_le_iff₀ hlogx]
    rw [hlogw] at hlogwx
    have hσ0 : σ ≠ 0 := ne_of_gt hσ
    field_simp [hσ0] at hlogwx
    exact hlogwx

/-- Suzuki's coordinate takes the upper endpoint `z` to `s`. -/
theorem coordinate_at_upper
    {D s z : ℝ} (hD : 1 < D) (hs : 0 < s)
    (hz : z = D ^ (1 / s)) :
    Real.log D / Real.log z = s := by
  rw [log_upper_endpoint hD hs hz]
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hlogD0 : Real.log D ≠ 0 := ne_of_gt (Real.log_pos hD)
  field_simp

/-- Suzuki's coordinate takes the lower endpoint `w` to `σ`. -/
theorem coordinate_at_lower
    {D σ w : ℝ} (hD : 1 < D) (hσ : 0 < σ)
    (hw : w = D ^ (1 / σ)) :
    Real.log D / Real.log w = σ := by
  rw [log_lower_endpoint hD hσ hw]
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hlogD0 : Real.log D ≠ 0 := ne_of_gt (Real.log_pos hD)
  field_simp

/-- Applying `H` at the upper endpoint gives exactly `H s`. -/
theorem apply_coordinate_at_upper
    {D s z : ℝ} (H : ℝ → ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z = D ^ (1 / s)) :
    H (Real.log D / Real.log z) = H s := by
  rw [coordinate_at_upper hD hs hz]

/-- Applying `H` at the lower endpoint gives exactly `H σ`. -/
theorem apply_coordinate_at_lower
    {D σ w : ℝ} (H : ℝ → ℝ) (hD : 1 < D) (hσ : 0 < σ)
    (hw : w = D ^ (1 / σ)) :
    H (Real.log D / Real.log w) = H σ := by
  rw [coordinate_at_lower hD hσ hw]

/-- Endpoint normalization after applying an arbitrary function `H`. -/
theorem apply_coordinate_endpoints
    {D s σ w z : ℝ} (H : ℝ → ℝ)
    (hD : 1 < D) (hs : 0 < s) (hsσ : s ≤ σ)
    (hz : z = D ^ (1 / s)) (hw : w = D ^ (1 / σ)) :
    H (Real.log D / Real.log z) = H s ∧
      H (Real.log D / Real.log w) = H σ := by
  have hσ : 0 < σ := hs.trans_le hsσ
  constructor
  · exact apply_coordinate_at_upper H hD hs hz
  · exact apply_coordinate_at_lower H hD hσ hw

/-- The endpoint logarithms give the exact normalization factor used in
Suzuki's main term. -/
theorem reciprocal_log_endpoint_normalization
    {D s σ w z : ℝ} (hD : 1 < D) (hs : 0 < s) (hsσ : s ≤ σ)
    (hz : z = D ^ (1 / s)) (hw : w = D ^ (1 / σ)) :
    1 / Real.log z * (σ / s) = 1 / Real.log w := by
  have hσ : 0 < σ := hs.trans_le hsσ
  rw [log_upper_endpoint hD hs hz, log_lower_endpoint hD hσ hw]
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hlogD0 : Real.log D ≠ 0 := ne_of_gt (Real.log_pos hD)
  field_simp


end MathlibNt.SieveTheory.SuzukiPowerCoordinates
