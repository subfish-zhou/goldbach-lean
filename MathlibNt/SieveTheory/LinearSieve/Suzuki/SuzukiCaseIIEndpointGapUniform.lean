import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointCoefficientUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIBracketGapQuantitative

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- The four positive Case-II endpoint terms admit one large-`D` threshold
uniformly for every odd depth `N ≥ 3`. -/
theorem exists_caseII_endpoint_common_threshold_uniform
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (K C d Δ : ℝ)
    (hK : 0 ≤ K) (_hC : 0 ≤ C)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ (N : ℕ) (D : ℝ),
      Odd N → 3 ≤ N → D0 ≤ D →
      caseIISharpPositiveEndpointRelativeCoeff
          N D d Δ (sourceSigma D d) C K ≤
        4 * ((1 - Δ) / (32 * sourceSigma D d)) := by
  have hd0 : 0 < d := by
    have : 0 < 7 / (1 - Δ) := by positivity
    linarith
  obtain ⟨A0, A1, hA0, hA1, hcoeff⟩ :=
    caseII_algebraic_endpoint_coefficients_uniform hH hK
  have haq0 : 0 ≤ caseIIQDRelativeEndpointCoeffA0 d Δ C K := by
    unfold caseIIQDRelativeEndpointCoeffA0
    positivity
  have hbase : 0 ≤ 27 * K := by positivity
  obtain ⟨Dσ, hDσ, hsigma⟩ := exists_sourceSigma_one_threshold d hd0
  obtain ⟨D0a, hD0a, ha⟩ :=
    exists_sourceSigma_sq_positive_delta_decay_threshold
      Δ d A0 hΔ0 hΔ1 hd hA0
  obtain ⟨D1a, hD1a, h1⟩ :=
    exists_sourceSigma_sq_positive_delta_decay_threshold
      Δ d A1 hΔ0 hΔ1 hd hA1
  obtain ⟨Dqa, hDqa, hq⟩ :=
    exists_sourceSigma_sq_one_div_log_decay_threshold
      Δ d (caseIIQDRelativeEndpointCoeffA0 d Δ C K) hΔ0 hΔ1 hd haq0
  obtain ⟨Dba, hDba, hb⟩ :=
    exists_sourceSigma_sq_positive_delta_decay_threshold
      Δ d (27 * K) hΔ0 hΔ1 hd hbase
  let D0 : ℝ := max (max Dσ D0a) (max D1a (max Dqa Dba))
  have hD0 : 1 < D0 := hDσ.trans_le <|
    (le_max_left Dσ D0a).trans (le_max_left (max Dσ D0a) _)
  refine ⟨D0, hD0, ?_⟩
  intro N D hN hN3 hD
  obtain ⟨hcoeff0, hcoeff1⟩ := hcoeff N hN hN3
  have hDσD : Dσ ≤ D :=
    (le_max_left Dσ D0a).trans ((le_max_left (max Dσ D0a) _).trans hD)
  have hD0aD : D0a ≤ D :=
    (le_max_right Dσ D0a).trans ((le_max_left (max Dσ D0a) _).trans hD)
  have hD1aD : D1a ≤ D :=
    (le_max_left D1a (max Dqa Dba)).trans
      ((le_max_right (max Dσ D0a) _).trans hD)
  have hDqaD : Dqa ≤ D :=
    (le_max_left Dqa Dba).trans
      ((le_max_right D1a (max Dqa Dba)).trans
        ((le_max_right (max Dσ D0a) _).trans hD))
  have hDbaD : Dba ≤ D :=
    (le_max_right Dqa Dba).trans
      ((le_max_right D1a (max Dqa Dba)).trans
        ((le_max_right (max Dσ D0a) _).trans hD))
  let σ : ℝ := sourceSigma D d
  let T : ℝ := (1 - Δ) / (32 * σ)
  have hσone : 1 ≤ σ := by
    simpa [σ, sourceSigma, sourceSigma] using hsigma D hDσD
  have hσ0 : 0 ≤ σ := zero_le_one.trans hσone
  have hDone : 1 < D := hDσ.trans_le hDσD
  have hlogD : 0 < Real.log D := Real.log_pos hDone
  have hp : 0 ≤ (Real.log D) ^ (Δ - 1) := Real.rpow_nonneg hlogD.le _
  have ha0raw :
      caseIIAlgebraicEndpointCoeffA0 N K * (Real.log D) ^ (Δ - 1) ≤ T := by
    calc
      caseIIAlgebraicEndpointCoeffA0 N K * (Real.log D) ^ (Δ - 1) ≤
          A0 * (Real.log D) ^ (Δ - 1) := by gcongr
      _ ≤ A0 * σ * (Real.log D) ^ (Δ - 1) := by
        have := mul_le_mul_of_nonneg_left hσone hA0
        nlinarith [mul_nonneg hA0 hp]
      _ ≤ T := by
        simpa [σ, T, sourceSigma, sourceSigma] using
          ha D hD0aD
  have ha1raw :
      σ * caseIIAlgebraicEndpointCoeffA1 N K * (Real.log D) ^ (Δ - 1) ≤ T := by
    calc
      σ * caseIIAlgebraicEndpointCoeffA1 N K * (Real.log D) ^ (Δ - 1) ≤
          σ * A1 * (Real.log D) ^ (Δ - 1) := by gcongr
      _ ≤ T := by
        simpa [σ, T, mul_comm, sourceSigma, sourceSigma] using
          h1 D hD1aD
  have hqraw :
      σ * caseIIQDRelativeEndpointCoeffA0 d Δ C K / Real.log D ≤ T := by
    have := hq D hDqaD
    simpa [σ, T, mul_comm, sourceSigma, sourceSigma] using this
  have hbraw : 27 * K * (Real.log D) ^ (Δ - 1) ≤ T := by
    have hscale :
        27 * K * (Real.log D) ^ (Δ - 1) ≤
          (27 * K) * σ * (Real.log D) ^ (Δ - 1) := by
      have := mul_le_mul_of_nonneg_left hσone hbase
      nlinarith [mul_nonneg hbase hp]
    exact hscale.trans (by
      simpa [σ, T, sourceSigma, sourceSigma] using hb D hDbaD)
  rw [caseIISharpPositiveEndpointRelativeCoeff_eq]
  change _ ≤ 4 * T
  linarith

/-- One cutoff, independent of the odd depth, preserves the quantitative
`27/32` Case-II rounded-bracket gap. -/
theorem exists_caseIIConcreteRoundedRelativeBracket_gap_threshold_uniform
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (K C d Δ : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ (N : ℕ) (D : ℝ),
      Odd N → 3 ≤ N → D0 ≤ D →
      27 * (1 - Δ) / (32 * sourceSigma D d) ≤
        1 - caseIIConcreteRoundedRelativeBracket
          N D d Δ (sourceSigma D d) C K := by
  obtain ⟨Dint, hDint, hint⟩ :=
    exists_integral_transport_relative_excess_threshold
      Δ d K hΔ0 hΔ1 hd hK
  obtain ⟨Dep, hDep, hep⟩ :=
    exists_caseII_endpoint_common_threshold_uniform
      hH K C d Δ hK hC hΔ0 hΔ1 hd
  obtain ⟨Dgap, hDgap, hgap⟩ :=
    exists_sourceSigma_contraction_gap_threshold
      Δ d hΔ0 hΔ1 hd
  obtain ⟨Dsig, hDsig, hsig⟩ :=
    exists_sourceSigma_gt_one_threshold hΔ1 hd
  let D0 : ℝ := max (max Dint Dep) (max Dgap Dsig)
  refine ⟨D0, hDint.trans_le ((le_max_left Dint Dep).trans (le_max_left _ _)), ?_⟩
  intro N D hN hN3 hD
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
  let E : ℝ := caseIISharpPositiveEndpointRelativeCoeff N D d Δ σ C K
  have hσ : 1 < σ := by
    simpa [σ, sourceSigma, sourceSigma] using hsig D hDsigD
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have hT : T = G / 32 := by
    dsimp [T, G]
    field_simp [ne_of_gt hσ0]
  have hInt : R - c ≤ T := by
    simpa [R, c, T, σ] using hint D hDintD
  have hEndpoint : E ≤ 4 * T := by
    have h := hep N D hN hN3 hDepD
    simpa [E, T, σ, sourceSigma, sourceSigma] using h
  have hGap : G ≤ 1 - c := by
    have h := hgap D hDgapD
    simpa [G, c, σ, sourceSigma, sourceSigma] using h
  have hscale : 27 * (1 - Δ) / (32 * sourceSigma D d) = 27 * G / 32 := by
    dsimp [G, σ]
    field_simp [ne_of_gt hσ0]
  rw [hscale]
  change 27 * G / 32 ≤ 1 - (R + E)
  rw [hT] at hInt hEndpoint
  linarith


end MathlibNt.SieveTheory
