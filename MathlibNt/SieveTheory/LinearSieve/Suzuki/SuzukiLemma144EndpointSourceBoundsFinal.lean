import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma132SlackFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition131iiiReverseFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Remainder1423
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma12QDEnvelopePointwise
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ExplicitRemaindersSourceOrder
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEndpointScalarBounds

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Case I, (14.23): endpoint source bounds

The published predicate `CaseI1423EndpointSourceBounds` omits the source
hypotheses (and even quantifies over `C = 0`), so it is not a valid unconditional
statement.  This file proves the source-faithful version used in Case I.  The source bounds are imported from their proved production producers.  In
particular, neither endpoint inequality is assumed in this module.
-/

private lemma endpoint_sigma11_front_rearrange
    (V K F logD σ : ℝ) (hlogD : 0 < logD) (hσ : 0 < σ) :
    V * (6 * K ^ 2 * F / (logD / σ)) =
      6 * V * (K ^ 2 * σ / logD) * F := by
  field_simp [ne_of_gt hlogD, ne_of_gt hσ]

private lemma endpoint_sigma11_collect
    (V K L R σ logσ E0 logD : ℝ) :
    6 * V * (K ^ 2 * σ / logD) *
        (L * R * (σ * logσ) * E0) =
      6 * L * R * V * E0 * (K ^ 2 * σ ^ 2 * logσ / logD) := by
  ring

private lemma endpoint_sigma11_budget_identity
    (L R C E V E0 logPow logLog σ : ℝ)
    (hC : 0 < C) (hE : 0 < E) (hLogLog : 0 < logLog)
    (hσ : 0 < σ) :
    6 * L * R * V * E0 * (logPow / (logLog * σ)) =
      (6 * L * R / (C * E)) *
        (C * E * V * logPow * E0 / (logLog * σ)) := by
  field_simp [ne_of_gt hC, ne_of_gt hE, ne_of_gt hLogLog, ne_of_gt hσ]

private lemma endpoint_sigma11_normalization
    (K σ logσ logD logLog Δ : ℝ)
    (hlog : 0 < logD) (hll : 0 < logLog) (hσ : 0 < σ)
    (hscalar : K ^ 2 * σ ^ 3 * logσ * logLog ≤ logD ^ (1 - Δ))
    (hpowe : logD ^ (-Δ) * logD = logD ^ (1 - Δ)) :
    K ^ 2 * σ ^ 2 * logσ / logD ≤
      logD ^ (-Δ) / (logLog * σ) := by
  exact MathlibNt.SieveTheory.caseI_endpoint_sigma11_normalization
    K σ logσ logD logLog Δ hlog hll hσ hscalar hpowe

/-- Transport and normalize the sigma-eleven scalar estimate into its budget. -/
lemma endpoint_sigma11_core
    (V K F logD σ L R logσ E0 logPow logLog C E : ℝ)
    (hlog : 0 < logD) (hσ : 0 < σ) (hC : 0 < C)
    (hE : 0 < E) (hll : 0 < logLog)
    (hV : 0 ≤ V) (hL : 0 ≤ L) (hR : 0 ≤ R) (hE0 : 0 ≤ E0)
    (htransport : F ≤ L * R * (σ * logσ) * E0)
    (hnorm : K ^ 2 * σ ^ 2 * logσ / logD ≤
      logPow / (logLog * σ)) :
    V * (6 * K ^ 2 * F / (logD / σ)) ≤
      (6 * L * R / (C * E)) *
        (C * E * V * logPow * E0 / (logLog * σ)) := by
  calc
    V * (6 * K ^ 2 * F / (logD / σ)) =
      6 * V * (K ^ 2 * σ / logD) * F :=
        endpoint_sigma11_front_rearrange _ _ _ _ _ hlog hσ
    _ ≤ 6 * V * (K ^ 2 * σ / logD) *
        (L * R * (σ * logσ) * E0) := by gcongr
    _ = 6 * L * R * V * E0 *
        (K ^ 2 * σ ^ 2 * logσ / logD) :=
          endpoint_sigma11_collect _ _ _ _ _ _ _ _
    _ ≤ 6 * L * R * V * E0 * (logPow / (logLog * σ)) := by gcongr
    _ = (6 * L * R / (C * E)) *
        (C * E * V * logPow * E0 / (logLog * σ)) :=
          endpoint_sigma11_budget_identity _ _ _ _ _ _ _ _ _ hC hE hll hσ

/-- Pointwise sigma-eleven endpoint bound from transport and scalar estimates. -/
theorem caseI1423_endpoint_sigma11_bound
    (S : BoundingSieve) (H : Section13HatLayers) (C K d Δ L R : ℝ)
    (N D : ℕ) (s : ℝ)
    (hC : 0 < C) (hD : 0 < (D : ℝ))
    (hlog : 0 < Real.log (D : ℝ))
    (hll : 0 < Real.log (Real.log (D : ℝ)))
    (hσ0 : 0 < sourceSigma (D : ℝ) d)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hE0 : 0 ≤ errorEnvelope H N (D : ℝ) d s)
    (htransport : finiteSourceLayer 1 2 (N - 1) (s - 1) ≤
      L * R * (sourceSigma (D : ℝ) d *
        Real.log (Real.exp 1 * sourceSigma (D : ℝ) d)) *
          errorEnvelope H N (D : ℝ) d s)
    (hscalarMul : K ^ 2 * sourceSigma (D : ℝ) d ^ 3 *
      Real.log (Real.exp 1 * sourceSigma (D : ℝ) d) *
        Real.log (Real.log (D : ℝ)) ≤ (Real.log (D : ℝ)) ^ (1 - Δ))
    (hpowe : (Real.log (D : ℝ)) ^ (-Δ) * Real.log (D : ℝ) =
      (Real.log (D : ℝ)) ^ (1 - Δ)) :
    caseI1423Sigma11Endpoint S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ K s
        (sourceSigma (D : ℝ) d) ≤
      (6 * L * R / (C * Real.exp √K)) *
        caseI1423RemainderUnit
          (sigma12InheritedBudget S H N D ⌈(D : ℝ) ^ (1 / s)⌉₊ C K d Δ s)
          (D : ℝ) (sourceSigma (D : ℝ) d) := by
  unfold caseI1423Sigma11Endpoint caseI1423RemainderUnit sigma12InheritedBudget
  rw [log_rpow_one_div_sourceSigma (D := (D : ℝ)) (d := d) hD]
  have hnorm : K ^ 2 * sourceSigma (D : ℝ) d ^ 2 *
      Real.log (Real.exp 1 * sourceSigma (D : ℝ) d) / Real.log (D : ℝ) ≤
      (Real.log (D : ℝ)) ^ (-Δ) /
        (Real.log (Real.log (D : ℝ)) * sourceSigma (D : ℝ) d) := by
    exact endpoint_sigma11_normalization _ _ _ _ _ _ hlog hll hσ0
      hscalarMul hpowe
  exact endpoint_sigma11_core _ _ _ _ _ _ _ _ _ _ _ _ _
    hlog hσ0 hC (Real.exp_pos _) hll
    (suzukiVProduct_pos S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ)).le
    hL hR hE0 htransport hnorm

/-- Convert the sigma-twelve front estimate and scalar bound into the final budget. -/
lemma caseI1423_endpoint_sigma12_final_algebra
    (q V K R σ logσ E0 logLog logD : ℝ)
    (hR : 0 ≤ R) (hσ : 0 < σ) (hE0 : 0 ≤ E0)
    (hV : 0 ≤ V) (hLogLog : 0 ≤ logLog)
    (hfront : V * q ≤ V * 2 * R * σ * logσ * E0)
    (hscalar : K ^ 2 * σ ^ 3 * logσ * logLog ≤ logD) :
    q * σ * V * 6 * K ^ 2 * logLog ≤
      R * E0 * V * logD * 12 / σ := by
  have hfactor : 0 ≤ 6 * K ^ 2 * logLog * σ := by positivity
  have hbudgetFactor : 0 ≤ 12 * R * E0 * V / σ := by positivity
  calc
    q * σ * V * 6 * K ^ 2 * logLog =
        (6 * K ^ 2 * logLog * σ) * (V * q) := by ring
    _ ≤ (6 * K ^ 2 * logLog * σ) *
        (V * 2 * R * σ * logσ * E0) :=
          mul_le_mul_of_nonneg_left hfront hfactor
    _ = (12 * R * E0 * V / σ) *
        (K ^ 2 * σ ^ 3 * logσ * logLog) := by
          field_simp [ne_of_gt hσ]
          ring
    _ ≤ (12 * R * E0 * V / σ) * logD :=
      mul_le_mul_of_nonneg_left hscalar hbudgetFactor
    _ = R * E0 * V * logD * 12 / σ := by ring


end MathlibNt.SieveTheory
