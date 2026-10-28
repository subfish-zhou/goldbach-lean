import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseISourceRecurrence

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

/-- For Case I, the finite-`D` correction in `τ` is inactive once its
reciprocal denominator is at least `1/β`. -/
theorem caseITau_eq_s_of_beta_le
    {β D s : ℝ} (hβ : 1 < β) (hβs : β ≤ s)
    (hDcorr : 1 / β ≤ 1 - Real.log 2 / Real.log D) :
    caseITau D s = s := by
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hden : 0 < 1 - Real.log 2 / Real.log D :=
    (div_pos (by norm_num) hβ0).trans_le hDcorr
  rw [caseITau, max_eq_left]
  exact ((inv_le_comm₀ hden hβ0).2 (by simpa [one_div] using hDcorr)).trans hβs

/-- A logarithmic threshold stated directly in `D` implies the correction
condition above.  This is the source-relevant explicit large-`D` form. -/
theorem caseITau_eq_s_of_log_threshold
    {β D s : ℝ} (hβ : 1 < β) (hβs : β ≤ s) (hD : 1 < D)
    (hDlarge : β * Real.log 2 ≤ (β - 1) * Real.log D) :
    caseITau D s = s := by
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hlog2 : Real.log 2 ≤ ((β - 1) * Real.log D) / β := by
    rw [le_div_iff₀ hβ0]
    simpa [mul_comm] using hDlarge
  have hratio : Real.log 2 / Real.log D ≤ (β - 1) / β := by
    rw [div_le_iff₀ hlogD]
    calc
      Real.log 2 ≤ ((β - 1) * Real.log D) / β := hlog2
      _ = ((β - 1) / β) * Real.log D := by ring
  apply caseITau_eq_s_of_beta_le hβ hβs
  have hid : (β - 1) / β = 1 - 1 / β := by
    field_simp [ne_of_gt hβ0]
  rw [hid] at hratio
  linarith


/-- The endpoint parameter `s'=σ` lies in Claim 14.5's already-closed regime
by the second alternative `σ ≤ s'`; no induction hypothesis is involved. -/
theorem claim14_5_sigma_endpoint_regime
    {β D σ C1 K ΘK : ℝ} (hβσ : β ≤ σ) :
    Claim14_5Regime β D σ C1 K ΘK σ :=
  ⟨hβσ, Or.inr le_rfl⟩


end MathlibNt.SieveTheory
