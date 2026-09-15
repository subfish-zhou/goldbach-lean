import MathlibNt.SieveTheory.LiLiuPrereqWFParameters

/-!
# A single internal level for a prescribed external level

The internal level is chosen before every factorization and every sieve
datum. The logarithmic error is transported without changing the original K.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

noncomputable def externalInternalLevel (Q ε : ℝ) : ℝ :=
  Q ^ (1 + ε + ε ^ 9)⁻¹

theorem external_dilation_bounds {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1 / 8) :
    1 < 1 + ε + ε ^ 9 ∧ 1 + ε + ε ^ 9 ≤ 1 + 2 * ε ∧
      1 + ε + ε ^ 9 < 3 / 2 := by
  have hp : ε ^ 9 ≤ ε := by
    have h8 : ε ^ 8 ≤ 1 := pow_le_one₀ hε.le (by linarith)
    calc
      ε ^ 9 = ε ^ 8 * ε := by ring
      _ ≤ 1 * ε := mul_le_mul_of_nonneg_right h8 hε.le
      _ = ε := one_mul _
  have hp0 : 0 ≤ ε ^ 9 := pow_nonneg hε.le _
  constructor
  · linarith
  constructor <;> linarith

theorem externalInternalLevel_pos {Q ε : ℝ} (hQ : 0 < Q) :
    0 < externalInternalLevel Q ε :=
  Real.rpow_pos_of_pos hQ _

theorem externalInternalLevel_level {Q ε : ℝ} (hQ : 0 ≤ Q)
    (hε : 0 < ε) (hεsmall : ε < 1 / 8) :
    externalInternalLevel Q ε ^ (1 + ε + ε ^ 9) = Q := by
  have hc : 1 + ε + ε ^ 9 ≠ 0 := by
    linarith [(external_dilation_bounds hε hεsmall).1]
  rw [externalInternalLevel, ← Real.rpow_mul hQ, inv_mul_cancel₀ hc, Real.rpow_one]

theorem externalInternalLevel_log {Q ε : ℝ} (hQ : 0 < Q) :
    Real.log (externalInternalLevel Q ε) = Real.log Q / (1 + ε + ε ^ 9) := by
  rw [externalInternalLevel, Real.log_rpow hQ]
  ring

theorem externalInternalLevel_ge_threshold {D₀ Q ε : ℝ} (hD₀ : 0 ≤ D₀)
    (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hQ : D₀ ^ (1 + ε + ε ^ 9) ≤ Q) :
    D₀ ≤ externalInternalLevel Q ε := by
  have hc : 0 < 1 + ε + ε ^ 9 := by
    linarith [(external_dilation_bounds hε hεsmall).1]
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hD₀ _) hQ (inv_nonneg.mpr hc.le)
  rw [← Real.rpow_mul hD₀, mul_inv_cancel₀ hc.ne', Real.rpow_one] at hp
  exact hp

theorem externalInternalLevel_coordinate {Q ε z : ℝ} (hQ : 0 < Q)
    (hε : 0 < ε) (hεsmall : ε < 1 / 8) :
    Real.log Q / Real.log z =
      (1 + ε + ε ^ 9) * (Real.log (externalInternalLevel Q ε) / Real.log z) := by
  have hc : 1 + ε + ε ^ 9 ≠ 0 := by
    linarith [(external_dilation_bounds hε hεsmall).1]
  rw [externalInternalLevel_log hQ]
  field_simp

theorem sieve_coordinate_ge_two {Q z : ℝ} (hQ : 0 < Q)
    (hz : 2 ≤ z) (hzQ : z ≤ Real.sqrt Q) :
    2 ≤ Real.log Q / Real.log z := by
  have hzlog : 0 < Real.log z := Real.log_pos (by linarith)
  have hzsq : z ^ 2 ≤ Q := by nlinarith [Real.sq_sqrt hQ.le]
  have hlogs := Real.log_le_log (pow_pos (by linarith : 0 < z) 2) hzsq
  rw [Real.log_pow] at hlogs
  exact (le_div_iff₀ hzlog).mpr (by norm_num at hlogs ⊢; linarith)

theorem external_edge_coordinate {Q ε z : ℝ} (hQ : 1 < Q)
    (hε : 0 < ε) (hεsmall : ε < 1 / 8) (hz : 2 ≤ z)
    (hzQ : z ≤ Real.sqrt Q) (hedge : Real.sqrt (externalInternalLevel Q ε) < z) :
    2 ≤ Real.log Q / Real.log z ∧
      Real.log Q / Real.log z < 2 * (1 + ε + ε ^ 9) := by
  have hDpos := externalInternalLevel_pos (ε := ε) (by linarith : 0 < Q)
  have hzlog : 0 < Real.log z := Real.log_pos (by linarith)
  have hlog := Real.log_lt_log (Real.sqrt_pos.mpr hDpos) hedge
  rw [Real.log_sqrt hDpos.le, externalInternalLevel_log (by linarith : 0 < Q)] at hlog
  have hc : 0 < 1 + ε + ε ^ 9 := by
    linarith [(external_dilation_bounds hε hεsmall).1]
  refine ⟨sieve_coordinate_ge_two (by linarith) hz hzQ, ?_⟩
  apply (div_lt_iff₀ hzlog).mpr
  have hh := (div_lt_iff₀ hc).mp (show Real.log Q / (1 + ε + ε ^ 9) <
    2 * Real.log z by linarith)
  nlinarith

/-- The factor two is absolute and the exponential keeps the SAME K. -/
theorem externalInternalLevel_error {Q ε K : ℝ} (hQ : 1 < Q)
    (hε : 0 < ε) (hεsmall : ε < 1 / 8) :
    ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
        Real.log (externalInternalLevel Q ε) ^ (-(1 / 3 : ℝ)) ≤
      2 * (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
        Real.log Q ^ (-(1 / 3 : ℝ))) := by
  have hc1 : 1 ≤ 1 + ε + ε ^ 9 := (external_dilation_bounds hε hεsmall).1.le
  have hc0 : 0 ≤ 1 + ε + ε ^ 9 := by linarith
  have hc2 : 1 + ε + ε ^ 9 ≤ 2 := by
    linarith [(external_dilation_bounds hε hεsmall).2.2]
  have hcp : (1 + ε + ε ^ 9) ^ (1 / 3 : ℝ) ≤ 2 := by
    calc
      _ ≤ (1 + ε + ε ^ 9) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      _ ≤ 2 := by simpa only [Real.rpow_one] using hc2
  have hlog : 0 ≤ Real.log Q := (Real.log_pos hQ).le
  have hpow : Real.log (externalInternalLevel Q ε) ^ (-(1 / 3 : ℝ)) ≤
      2 * Real.log Q ^ (-(1 / 3 : ℝ)) := by
    rw [externalInternalLevel_log (by linarith : 0 < Q), Real.div_rpow hlog hc0,
      Real.rpow_neg hc0, div_inv_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hcp
      (Real.rpow_nonneg hlog (-(1 / 3 : ℝ)))]
  have hh := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) by positivity)
  nlinarith

#check externalInternalLevel_ge_threshold
#print axioms externalInternalLevel_ge_threshold
#check externalInternalLevel_error
#print axioms externalInternalLevel_error

end MathlibNt.SieveTheory.LiLiuPrereqWF
