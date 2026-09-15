import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SourceParameters

open scoped Classical BigOperators

namespace MathlibNt.SieveTheory

set_option autoImplicit false

/-!
# Paying source-fixed pointwise thresholds

This is the common no-eventual bridge used by the strict Case-I moving producer.
A cutoff selected from the source data before `K` is absorbed into the separator
`C1 * K ^ Θ < log D`; no cutoff is selected after `K`.
-/

/-- A positive fixed real cutoff can be paid by an earlier source-separator
constant.  The conclusion is strict, matching the strict source separator. -/
theorem exists_sourceLargeLog_fixedThreshold
    {Θ : ℝ} (hΘ : 0 < Θ) (D0 : ℝ) (hD0 : 0 < D0) :
    ∃ C1min : ℝ, 1 ≤ C1min ∧
      ∀ (C1 K D : ℝ), C1min ≤ C1 → 2 ≤ K → 0 < D →
        C1 * K ^ Θ < Real.log D → D0 < D := by
  let C1min : ℝ := max 1 (Real.log D0)
  refine ⟨C1min, le_max_left _ _, ?_⟩
  intro C1 K D hC1 hK hD hlarge
  have hC10 : 0 ≤ C1 := by
    exact (show (0 : ℝ) ≤ 1 by norm_num).trans ((le_max_left _ _).trans hC1)
  have hKpow : 1 ≤ K ^ Θ :=
    Real.one_le_rpow (by linarith) hΘ.le
  have hlog : Real.log D0 < Real.log D := by
    calc
      Real.log D0 ≤ C1min := le_max_right _ _
      _ ≤ C1 := hC1
      _ = C1 * 1 := by ring
      _ ≤ C1 * K ^ Θ := mul_le_mul_of_nonneg_left hKpow hC10
      _ < Real.log D := hlarge
  have hexp := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_log hD0, Real.exp_log hD] at hexp
  exact hexp

/-- Source-packet specialization.  This is the form consumed by strict Case I;
its only exponent premise is the literal source packet. -/
theorem exists_sourceLargeLog_fixedThreshold_of_source
    {d Δ Θ : ℝ} (hsrc : SuzukiClaim145SourceParameters d Δ Θ)
    (D0 : ℝ) (hD0 : 0 < D0) :
    ∃ C1min : ℝ, 1 ≤ C1min ∧
      ∀ (C1 K D : ℝ), C1min ≤ C1 → 2 ≤ K → 0 < D →
        C1 * K ^ Θ < Real.log D → D0 < D :=
  exists_sourceLargeLog_fixedThreshold hsrc.hTheta_pos D0 hD0


end MathlibNt.SieveTheory
