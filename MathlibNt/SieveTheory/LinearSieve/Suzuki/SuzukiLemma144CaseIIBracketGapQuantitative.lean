import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedEndpointTransport
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceContractionGap

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
