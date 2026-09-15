import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseISourceRecurrence
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseAssembly

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

/-- Exact Case-I wrapper: `β + ε_N ≤ s` supplies `β ≤ s`, so the explicit
logarithmic threshold forces `τ=s`. -/
theorem caseITau_eq_s_of_claim14_5CaseI
    {β D s σ : ℝ} {N : ℕ} (hβ : 1 < β)
    (hcaseI : Claim14_5CaseI β N s σ) (hD : 1 < D)
    (hDlarge : β * Real.log 2 ≤ (β - 1) * Real.log D) :
    caseITau D s = s := by
  have hβs : β ≤ s := by
    have heps : 0 ≤ ((N % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    exact (le_add_of_nonneg_right heps).trans hcaseI.1
  exact caseITau_eq_s_of_log_threshold hβ hβs hD hDlarge

/-- Once `τ=s`, the Case-I power coordinate identifies the upper split cutoff
with the source cutoff `z`. -/
theorem caseI_tauCut_eq_z_of_power_coordinate
    {D z : ℕ} {s : ℝ} (hτ : caseITau (D : ℝ) s = s)
    (hz : (D : ℝ) ^ (1 / s) = (z : ℝ)) :
    (D : ℝ) ^ (1 / caseITau (D : ℝ) s) = (z : ℝ) := by
  rw [hτ]
  exact hz

/-- The `Σ₂` carrier in the exact three-range decomposition is empty in Case I. -/
theorem caseI_sigma2_filter_eq_empty
    (S : BoundingSieve) {D z : ℕ} {s : ℝ}
    (hτ : caseITau (D : ℝ) s = s)
    (hz : (D : ℝ) ^ (1 / s) = (z : ℝ)) :
    (suzukiSupportedBelow S z).filter
        (fun p : ℕ => (D : ℝ) ^ (1 / caseITau (D : ℝ) s) ≤ (p : ℝ)) = ∅ := by
  classical
  have hcut := caseI_tauCut_eq_z_of_power_coordinate hτ hz
  apply Finset.filter_eq_empty_iff.mpr
  intro p hp hzp
  have hpz : p < z := (mem_filter.mp hp).2
  have hpzR : (p : ℝ) < (z : ℝ) := by exact_mod_cast hpz
  rw [hcut] at hzp
  exact (not_le_of_gt hpzR) hzp

/-- Consequently every `Σ₂` sum in the source recurrence vanishes. -/
theorem caseI_sigma2_sum_eq_zero
    (S : BoundingSieve) {D z : ℕ} {s : ℝ}
    (hτ : caseITau (D : ℝ) s = s)
    (hz : (D : ℝ) ^ (1 / s) = (z : ℝ)) (f : ℕ → ℝ) :
    (∑ p ∈ (suzukiSupportedBelow S z).filter
        (fun p : ℕ => (D : ℝ) ^ (1 / caseITau (D : ℝ) s) ≤ (p : ℝ)), f p) = 0 := by
  rw [caseI_sigma2_filter_eq_empty S hτ hz]
  simp

/-- In a `CaseIThreeRangeDomain`, `Σ₀` is literally the endpoint sum whose
strict cutoff is `D^(1/σ)`. -/
theorem caseI_sigma0_eq_sigma_endpoint
    (S : BoundingSieve) {D z : ℕ} {σ s : ℝ}
    (hdom : CaseIThreeRangeDomain D z σ s)
    (hτ : caseITau (D : ℝ) s = s)
    (hz : (D : ℝ) ^ (1 / s) = (z : ℝ)) (f : ℕ → ℝ) :
    (∑ p ∈ (suzukiSupportedBelow S z).filter
          (fun p : ℕ => (p : ℝ) < (D : ℝ) ^ (1 / σ)), f p) =
      ∑ p ∈ suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / σ)⌉₊, f p := by
  classical
  have hcut : (D : ℝ) ^ (1 / caseITau (D : ℝ) s) = (z : ℝ) :=
    caseI_tauCut_eq_z_of_power_coordinate hτ hz
  have hσz : (D : ℝ) ^ (1 / σ) ≤ (z : ℝ) := by
    rw [← hcut]
    exact hdom.sigmaCut_le_tauCut
  apply Finset.sum_congr
  · rw [suzukiSupportedBelow_ceil_real]
    ext p
    simp only [suzukiSupportedBelow, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hpP, _hpz⟩, hpσ⟩
      exact ⟨hpP, hpσ⟩
    · rintro ⟨hpP, hpσ⟩
      have hpzR : (p : ℝ) < (z : ℝ) := hpσ.trans_le hσz
      have hpz : p < z := by exact_mod_cast hpzR
      exact ⟨⟨hpP, hpz⟩, hpσ⟩
  · intro p hp
    rfl

/-- The endpoint parameter `s'=σ` lies in Claim 14.5's already-closed regime
by the second alternative `σ ≤ s'`; no induction hypothesis is involved. -/
theorem claim14_5_sigma_endpoint_regime
    {β D σ C1 K ΘK : ℝ} (hβσ : β ≤ σ) :
    Claim14_5Regime β D σ C1 K ΘK σ :=
  ⟨hβσ, Or.inr le_rfl⟩

/-- Case I itself supplies the lower endpoint condition needed at `s'=σ`. -/
theorem claim14_5_sigma_endpoint_regime_of_caseI
    {β D s σ C1 K ΘK : ℝ} {N : ℕ}
    (hcaseI : Claim14_5CaseI β N s σ) :
    Claim14_5Regime β D σ C1 K ΘK σ := by
  apply claim14_5_sigma_endpoint_regime
  have heps : 0 ≤ ((N % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  exact (le_add_of_nonneg_right heps).trans (hcaseI.1.trans hcaseI.2)

/-- Package the `Σ₀` transport through the already-closed `s'=σ` regime of
Claim 14.5.  The endpoint provider is explicitly keyed by `Claim14_5Regime`,
rather than by an induction hypothesis at the current `s`. -/
theorem caseI_sigma0_le_of_claim14_5_sigma_endpoint
    (S : BoundingSieve) {D z N : ℕ} {σ s β C1 K ΘK B : ℝ}
    (hdom : CaseIThreeRangeDomain D z σ s)
    (hτ : caseITau (D : ℝ) s = s)
    (hz : (D : ℝ) ^ (1 / s) = (z : ℝ))
    (hcaseI : Claim14_5CaseI β N s σ) (f : ℕ → ℝ)
    (hendpoint : Claim14_5Regime β (D : ℝ) σ C1 K ΘK σ →
      (∑ p ∈ suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / σ)⌉₊, f p) ≤ B) :
    (∑ p ∈ (suzukiSupportedBelow S z).filter
        (fun p : ℕ => (p : ℝ) < (D : ℝ) ^ (1 / σ)), f p) ≤ B := by
  rw [caseI_sigma0_eq_sigma_endpoint S hdom hτ hz f]
  exact hendpoint (claim14_5_sigma_endpoint_regime_of_caseI hcaseI)

/-- The current source-faithful recurrence with Case-I `Σ₂` deleted. -/
theorem suzukiSourceParitySum_recurrence_caseI_two_ranges
    (S : BoundingSieve) {N D z : ℕ} {σ s : ℝ} (hN2 : 2 ≤ N)
    (hbase : Odd N → suzukiSourceV S 1 D z = 0)
    (hcube : ∀ n ∈ sourceParityIndices N, 2 ≤ n → Odd n →
      ∀ p ∈ suzukiSupportedBelow S z, p ^ 3 < D)
    (hdom : CaseIThreeRangeDomain D z σ s)
    (hτ : caseITau (D : ℝ) s = s)
    (hz : (D : ℝ) ^ (1 / s) = (z : ℝ)) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) =
      (∑ p ∈ (suzukiSupportedBelow S z).filter
          (fun p : ℕ => (p : ℝ) < (D : ℝ) ^ (1 / σ)),
        S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p)) +
      (∑ p ∈ (suzukiSupportedBelow S z).filter
          (fun p : ℕ => (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) ∧
            (p : ℝ) < (D : ℝ) ^ (1 / caseITau (D : ℝ) s)),
        S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p)) := by
  rw [suzukiSourceParitySum_recurrence_three_ranges S hN2 hbase hcube hdom]
  rw [caseI_sigma2_sum_eq_zero S hτ hz]
  simp

end MathlibNt.SieveTheory
