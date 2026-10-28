import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIPositiveEndpointPacket
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceSigmaDecay

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000
/-- At the exact source point `y = D^(1/3)`, the integral contribution pays
both the cubic lambda comparison and the product-ratio excess. -/
theorem caseIIPositiveDeltaIntegralPart_source_exact_relative
    (H : Section13HatLayers) {N : ℕ} {D d Δ σ C K s : ℝ}
    (hD : 1 < D) (hs : 0 < s) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hcut : 0 ≤ (1 - 1 / σ) ^ (1 - Δ))
    (hiii : (∫ t in (3 : ℝ)..σ,
        qD H (ErrorSign.ofDepth N).opposite D d Δ t) ≤
      (1 - 1 / σ) ^ (1 - Δ) *
        lambda H (ErrorSign.ofDepth N) D d 0 3)
    (hcubic : lambda H (ErrorSign.ofDepth N) D d 0 3 ≤
      perturbation D d 0 3 *
        lambda H (ErrorSign.ofDepth N) D d 0 s) :
    caseIIPositiveDeltaIntegralPart H N D (D ^ (1 / (3 : ℝ)))
        d Δ σ C K s ≤
      C * Real.exp (Real.sqrt K) * errorEnvelope H N D d s *
        (Real.log D) ^ (-Δ) *
        ((1 + 3 * K / Real.log D) *
          (1 - 1 / σ) ^ (1 - Δ) * perturbation D d 0 3) := by
  let c : ℝ := (1 - 1 / σ) ^ (1 - Δ)
  let R : ℝ := perturbation D d 0 3
  let E : ℝ := errorEnvelope H N D d s
  let L : ℝ := (Real.log D) ^ (-Δ)
  let P : ℝ := C * Real.exp (Real.sqrt K)
  let I : ℝ := ∫ t in (3 : ℝ)..σ,
    qD H (ErrorSign.ofDepth N).opposite D d Δ t
  have hlog : 0 < Real.log D := Real.log_pos hD
  have hlogy : Real.log (D ^ (1 / (3 : ℝ))) = (1 / 3 : ℝ) * Real.log D := by
    rw [Real.log_rpow (zero_lt_one.trans hD)]
  have hratio : 1 + K / Real.log (D ^ (1 / (3 : ℝ))) =
      1 + 3 * K / Real.log D := by
    rw [hlogy]
    field_simp [ne_of_gt hlog]

  have hlambda : lambda H (ErrorSign.ofDepth N) D d 0 s = s * E := by
    dsimp [E]
    unfold lambda errorEnvelope
    norm_num [Real.rpow_add hs]
    ring
  have hI : (1 / s) * I ≤ (c * R) * E := by
    have hchain : I ≤ c * (R * lambda H (ErrorSign.ofDepth N) D d 0 s) := by
      calc
        I ≤ c * lambda H (ErrorSign.ofDepth N) D d 0 3 := by
          simpa [I, c] using hiii
        _ ≤ c * (R * lambda H (ErrorSign.ofDepth N) D d 0 s) :=
          mul_le_mul_of_nonneg_left (by simpa [R] using hcubic)
            (by simpa [c] using hcut)
    have hscaled := mul_le_mul_of_nonneg_left hchain (one_div_nonneg.mpr hs.le)
    calc
      (1 / s) * I ≤ (1 / s) *
          (c * (R * lambda H (ErrorSign.ofDepth N) D d 0 s)) := hscaled
      _ = (c * R) * E := by
        rw [hlambda]
        field_simp [ne_of_gt hs]

  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hL : 0 ≤ L := by dsimp [L]; exact Real.rpow_nonneg hlog.le _
  have hr : 0 ≤ 1 + 3 * K / Real.log D := by positivity
  have hscale : 0 ≤ (1 + 3 * K / Real.log D) * P * L := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hI hscale
  rw [caseIIPositiveDeltaIntegralPart, hratio]
  change (3 / s) * (1 + 3 * K / Real.log D) *
      (P * L * ((1 / 3) * I)) ≤
    P * E * L * ((1 + 3 * K / Real.log D) * c * R)
  calc
    _ = ((1 + 3 * K / Real.log D) * P * L) * ((1 / s) * I) := by ring
    _ ≤ ((1 + 3 * K / Real.log D) * P * L) * ((c * R) * E) := hscaled
    _ = _ := by ring
/-- The cubic perturbation has linear excess when `3^d` is at most `log D`. -/
lemma perturbation_three_le_one_add_seven_ratio
    {D d : ℝ} (hlog : 0 < Real.log D) (_hd : 0 ≤ d)
    (hsmall : 3 ^ d ≤ Real.log D) :
    perturbation D d 0 3 ≤ 1 + 7 * (3 ^ d / Real.log D) := by
  let x : ℝ := 3 ^ d / Real.log D
  have hx0 : 0 ≤ x := div_nonneg (Real.rpow_nonneg (by norm_num) _) hlog.le
  have hx1 : x ≤ 1 := (div_le_one hlog).2 hsmall
  have hx2 : x ^ 2 ≤ x := by nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  have hx3 : x ^ 3 ≤ x := by
    calc
      x ^ 3 = x ^ 2 * x := by ring
      _ ≤ x * x := mul_le_mul_of_nonneg_right hx2 hx0
      _ ≤ x := by nlinarith
  rw [perturbation]
  norm_num [Real.rpow_natCast]
  dsimp [x] at *
  nlinarith


end MathlibNt.SieveTheory
