import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIIntegralTransportRelative
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointCommonThreshold
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceContractionGap
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISharpPositiveEndpointCoefficients

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- The complete source Case-II relative bracket is eventually strictly
contractive.  The integral transport excess, all four positive endpoint terms,
and the source contraction gap are paid at one common explicit (finite `max`)
threshold; no `D`-dependent decay premise remains. -/
theorem exists_caseII_source_relative_bracket_lt_one_threshold
    (N : ℕ) (K C d Δ : ℝ)
    (hF0 : 0 ≤ finiteSourceLayer 1 2 N 3)
    (hF1 : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D →
      (1 + 3 * K / Real.log D) *
          (1 - 1 / sourceSigma D d) ^ (1 - Δ) *
          perturbation D d 0 3 +
        caseIISharpPositiveEndpointRelativeCoeff
          N D d Δ (sourceSigma D d) C K < 1 := by
  obtain ⟨Dint, hDint, hint⟩ :=
    exists_integral_transport_relative_excess_threshold
      Δ d K hΔ0 hΔ1 hd hK
  obtain ⟨Dep, hDep, hep⟩ :=
    exists_caseII_endpoint_common_threshold
      N K C d Δ hF0 hF1 hK hC hΔ0 hΔ1 hd
  obtain ⟨Dgap, hDgap, hgap⟩ :=
    exists_sourceSigma_contraction_gap_threshold
      Δ d hΔ0 hΔ1 hd
  obtain ⟨Dsig, hDsig, hsig⟩ :=
    exists_sourceSigma_gt_one_threshold hΔ1 hd
  let D0 : ℝ := max (max Dint Dep) (max Dgap Dsig)
  have hD0 : 1 < D0 :=
    hDint.trans_le ((le_max_left Dint Dep).trans (le_max_left _ _))
  refine ⟨D0, hD0, ?_⟩
  intro D hD
  have hDintD : Dint ≤ D :=
    (le_max_left Dint Dep).trans ((le_max_left (max Dint Dep) _).trans hD)
  have hDepD : Dep ≤ D :=
    (le_max_right Dint Dep).trans ((le_max_left (max Dint Dep) _).trans hD)
  have hDgapD : Dgap ≤ D :=
    (le_max_left Dgap Dsig).trans ((le_max_right (max Dint Dep) _).trans hD)
  have hDsigD : Dsig ≤ D :=
    (le_max_right Dgap Dsig).trans ((le_max_right (max Dint Dep) _).trans hD)
  let σ : ℝ := sourceSigma D d
  let c : ℝ := (1 - 1 / σ) ^ (1 - Δ)
  let T : ℝ := (1 - Δ) / (32 * σ)
  let G : ℝ := (1 - Δ) / σ
  let R : ℝ :=
    (1 + 3 * K / Real.log D) * c * perturbation D d 0 3
  let E : ℝ :=
    caseIISharpPositiveEndpointRelativeCoeff N D d Δ σ C K
  have hσ : 1 < σ := by
    simpa [σ] using
      hsig D hDsigD
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have hG : 0 < G := by
    dsimp [G]
    exact div_pos (sub_pos.mpr hΔ1) hσ0
  have hT : T = G / 32 := by
    dsimp [T, G]
    field_simp [ne_of_gt hσ0]
  have hInt : R - c ≤ T := by
    simpa [R, c, T, σ] using hint D hDintD
  have hEndpoint : E ≤ 4 * T := by
    have h := hep D hDepD
    simpa [E, T, σ] using h
  have hGap : G ≤ 1 - c := by
    have h := hgap D hDgapD
    simpa [G, c, σ] using h
  change R + E < 1
  rw [hT] at hInt hEndpoint
  linarith


end MathlibNt.SieveTheory
