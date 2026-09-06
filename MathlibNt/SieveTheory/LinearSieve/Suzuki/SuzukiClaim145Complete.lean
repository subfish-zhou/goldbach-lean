import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseBUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SourceParameters
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SourceFinal

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

/-- Fully inhabited Suzuki Claim 14.5 with its final constants chosen before a
varying bounding sieve, as required by the source dependence in Lemma 14.4. -/
theorem exists_claim145_source_complete_uniform_in_S
    (H : Section13HatLayers)
    {Δ₀ Δ d Θ : ℝ}
    (hparam : Claim145SourceParameterPacket Δ₀ Δ d Θ)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d)
    (hH : Section13HatSourceContract H) :
    ∃ C1min CB : ℝ, 0 < C1min ∧ 0 < CB ∧
      ∀ C1 : ℝ, C1min ≤ C1 →
        ∃ C145 : ℝ, 0 < C145 ∧
          ∀ (S : BoundingSieve) (K : ℝ) (N D : ℕ) (s : ℝ),
            2 ≤ K → HasDimensionOneLocalProductBound S K →
            2 ≤ D → 2 ≤ s →
            (Real.log (D : ℝ) ≤ C1 * K ^ Θ ∨
              sourceSigma (D : ℝ) d ≤ s) →
            ActualClaim145BoundAt S H N D d Δ K s C145 := by
  obtain ⟨C1min, CB, hC1min, hCB, hB⟩ :=
    claim145_caseB_uniform_in_S H hΔ0 hΔ1 hd hparam.one_le_theta hH
  refine ⟨C1min, CB, hC1min, hCB, ?_⟩
  intro C1 hC1
  have hC1pos : 0 < C1 := hC1min.trans_le hC1
  have hd2 : 2 < d := by
    have hden : 0 < 1 - Δ := sub_pos.mpr hΔ1
    have hseven : 7 ≤ 7 / (1 - Δ) := by
      rw [le_div_iff₀ hden]
      nlinarith
    linarith
  exact claim145_source_actual_of_uniform_caseB_uniform_in_S H hH hd2 hC1pos
    hparam.theta_pos hparam.equation14_3 hΔ0 hΔ1 hparam.highS_gap hC1 hB


/-- Fully inhabited Suzuki Claim 14.5 with the source order of constants.
`C1min` and the Case-B constant are chosen before the varying `C1`; after a
legal `C1` is fixed, the common Claim-14.5 constant is chosen before
`K,N,D,s`. -/
theorem exists_claim145_source_complete
    (S : BoundingSieve) (H : Section13HatLayers)
    {Δ₀ Δ d Θ : ℝ}
    (hparam : Claim145SourceParameterPacket Δ₀ Δ d Θ)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d)
    (hH : Section13HatSourceContract H) :
    ∃ C1min CB : ℝ, 0 < C1min ∧ 0 < CB ∧
      ∀ C1 : ℝ, C1min ≤ C1 →
        ∃ C145 : ℝ, 0 < C145 ∧
          ∀ (K : ℝ) (N D : ℕ) (s : ℝ),
            2 ≤ K → HasDimensionOneLocalProductBound S K →
            2 ≤ D → 2 ≤ s →
            (Real.log (D : ℝ) ≤ C1 * K ^ Θ ∨
              sourceSigma (D : ℝ) d ≤ s) →
            ActualClaim145BoundAt S H N D d Δ K s C145 := by
  obtain ⟨C1min, CB, hC1min, hCB, hcomplete⟩ :=
    exists_claim145_source_complete_uniform_in_S H hparam hΔ0 hΔ1 hd hH
  refine ⟨C1min, CB, hC1min, hCB, ?_⟩
  intro C1 hC1
  obtain ⟨C145, hC145, hbound⟩ := hcomplete C1 hC1
  exact ⟨C145, hC145, hbound S⟩


end MathlibNt.SieveTheory
