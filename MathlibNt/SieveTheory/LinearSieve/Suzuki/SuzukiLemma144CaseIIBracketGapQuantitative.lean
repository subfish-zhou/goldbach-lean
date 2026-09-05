import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedConcreteRelativeAssembly
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIFinalRelativeContraction

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Quantitative Case-II rounded-bracket gap

The existing contraction proof spends only `5/32` of the source tangent gap:
the integral-transport excess costs `1/32` and the four endpoint terms cost
`4/32`.  Thus the rounded bracket retains `27/32` of
`(1-Δ)/sourceSigma D d`.  In particular the true proved scale is `1/σ`, stronger
than the requested `1/(loglog D * σ)` scale.
-/

/-- Quantitative strengthening of
`exists_caseIIConcreteRoundedRelativeBracket_lt_one_threshold`. -/
theorem exists_caseIIConcreteRoundedRelativeBracket_gap_threshold
    (N : ℕ) (K C d Δ : ℝ)
    (hF0 : 0 ≤ finiteSourceLayer 1 2 N 3)
    (hF1 : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D →
      27 * (1 - Δ) / (32 * sourceSigma D d) ≤
        1 - caseIIConcreteRoundedRelativeBracket
          N D d Δ (sourceSigma D d) C K := by
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
  refine ⟨D0, hDint.trans_le ((le_max_left Dint Dep).trans (le_max_left _ _)), ?_⟩
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
  let E : ℝ := caseIISharpPositiveEndpointRelativeCoeff N D d Δ σ C K
  have hσ : 1 < σ := by
    simpa [σ, sourceSigma] using hsig D hDsigD
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have hT : T = G / 32 := by
    dsimp [T, G]
    field_simp [ne_of_gt hσ0]
  have hInt : R - c ≤ T := by
    simpa [R, c, T, σ] using hint D hDintD
  have hEndpoint : E ≤ 4 * T := by
    have h := hep D hDepD
    simpa [E, T, σ, sourceSigma] using h
  have hGap : G ≤ 1 - c := by
    have h := hgap D hDgapD
    simpa [G, c, σ, sourceSigma] using h
  have hscale : 27 * (1 - Δ) / (32 * sourceSigma D d) = 27 * G / 32 := by
    dsimp [G, σ]
    field_simp [ne_of_gt hσ0]
  rw [hscale]
  change 27 * G / 32 ≤ 1 - (R + E)
  rw [hT] at hInt hEndpoint
  linarith

/-- Scale-free form of the quantitative gap: one threshold works for every
choice of the outer constant `C`. -/
theorem exists_caseIIConcreteRoundedRelativeBracket_gap_threshold_scaleFree
    (N : ℕ) (K d Δ : ℝ)
    (hF0 : 0 ≤ finiteSourceLayer 1 2 N 3)
    (hF1 : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2)
    (hK : 0 ≤ K)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ (D C : ℝ), D0 ≤ D →
      27 * (1 - Δ) / (32 * sourceSigma D d) ≤
        1 - caseIIConcreteRoundedRelativeBracket
          N D d Δ (sourceSigma D d) C K := by
  obtain ⟨D0, hD0, hgap⟩ :=
    exists_caseIIConcreteRoundedRelativeBracket_gap_threshold
      N K 0 d Δ hF0 hF1 hK (by norm_num) hΔ0 hΔ1 hd
  refine ⟨D0, hD0, ?_⟩
  intro D C hD
  rw [caseIIConcreteRoundedRelativeBracket_C_independent
    N D d Δ (sourceSigma D d) C 0 K]
  exact hgap D hD

/-- Pure algebraic endpoint absorption.  After `V(D) ≤ V(z)` and Claim 14.6(i)
provide `E(D,σ) ≤ E(D,s)`, the quantitative gap cancels the source `1/σ`;
the remaining Claim-14.5 factor `1/log D` is absorbed by `hconstant`. -/
theorem claim145_endpoint_absorbed_by_caseII_gap
    {VD Vz expK Eσ Es L logD σ C C145 Δ gap : ℝ}
    (hVD : 0 ≤ VD) (hV : VD ≤ Vz)
    (hexp : 0 ≤ expK) (hEσ : 0 ≤ Eσ) (hE : Eσ ≤ Es)
    (hL : 0 ≤ L) (hlog : 0 < logD) (hσ : 0 < σ)
    (hΔ1 : Δ ≤ 1) (hC145 : 0 ≤ C145) (hC : 0 ≤ C)
    (hgap : 27 * (1 - Δ) / (32 * σ) ≤ gap)
    (hconstant : C145 ≤ 27 * C * (1 - Δ) * logD / 32) :
    C145 * (VD * (expK / (logD * σ)) * Eσ * L) ≤
      Vz * (C * expK * Es * L) * gap := by
  have hVz : 0 ≤ Vz := hVD.trans hV
  have hEs : 0 ≤ Es := hEσ.trans hE
  have hβ : 0 ≤ 1 - Δ := sub_nonneg.mpr hΔ1
  calc
    C145 * (VD * (expK / (logD * σ)) * Eσ * L) ≤
        C145 * (Vz * (expK / (logD * σ)) * Es * L) := by gcongr
    _ ≤ (27 * C * (1 - Δ) * logD / 32) *
        (Vz * (expK / (logD * σ)) * Es * L) := by gcongr
    _ = Vz * (C * expK * Es * L) *
        (27 * (1 - Δ) / (32 * σ)) := by
          field_simp [ne_of_gt hlog, ne_of_gt hσ]
    _ ≤ Vz * (C * expK * Es * L) * gap := by gcongr

/-- The sole remaining scalar requirement in endpoint absorption is eventual and
independent of `s`; positivity of the target constant `C` is essential. -/
theorem exists_claim145_gap_constant_threshold
    {C C145 Δ : ℝ} (hC : 0 < C) (hΔ1 : Δ < 1) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D →
      C145 ≤ 27 * C * (1 - Δ) * Real.log D / 32 := by
  let a : ℝ := 32 * C145 / (27 * C * (1 - Δ))
  let X : ℝ := max 1 a
  refine ⟨Real.exp X, Real.one_lt_exp_iff.mpr (zero_lt_one.trans_le (le_max_left _ _)), ?_⟩
  intro D hD
  have hDpos : 0 < D := (Real.exp_pos X).trans_le hD
  have hlog : X ≤ Real.log D := (Real.le_log_iff_exp_le hDpos).2 hD
  have ha : a ≤ Real.log D := (le_max_right 1 a).trans hlog
  have hcoef : 0 < 27 * C * (1 - Δ) := by positivity
  apply (le_div_iff₀ (show (0 : ℝ) < 32 by norm_num)).2
  have hmul : 32 * C145 ≤ Real.log D * (27 * C * (1 - Δ)) :=
    (div_le_iff₀ hcoef).mp (by simpa [a] using ha)
  nlinarith [hmul]


end MathlibNt.SieveTheory
