import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedTransportErrorBridge
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIExactRatioCoefficients

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- Exact-ratio, scale-free rounded transport packet for the source-large branch. -/
theorem caseII_rounded_transportErr_le_positiveDelta_relative_packet_sourceLarge_coefficients
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D z : ℕ} {yr zr d Δ σ C K B0 s : ℝ}
    (hH : Section13HatContract H 2) (hN : Odd N)
    (hD : Real.exp 1 ≤ (D : ℝ))
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hσ : 3 ≤ σ) (hs1 : 1 < s)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hsmall : (3 : ℝ) ^ d ≤ Real.log (D : ℝ))
    (hE : (1 / 3 : ℝ) ≤ errorEnvelope H N (D : ℝ) d s)
    (hP : 3 ≤ C * Real.exp (Real.sqrt K))
    (hyr : yr = (D : ℝ) ^ (1 / (3 : ℝ)))
    (hzr : zr = (D : ℝ) ^ (1 / s))
    (hz : z = ⌈zr⌉₊) :
    caseIIRoundedTransportErr S H N (D : ℝ) yr zr d Δ σ C K B0 s +
        suzukiVProduct S (z : ℝ) *
          (K * 3 ^ 2 / (s * Real.log (D : ℝ))) ≤
      B0 + suzukiVProduct S (z : ℝ) *
        (caseIIPositiveDeltaIntegralPart H N (D : ℝ) yr d Δ σ C K s +
          (C * Real.exp (Real.sqrt K)) * errorEnvelope H N (D : ℝ) d s *
            (Real.log (D : ℝ)) ^ (-Δ) *
            caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K) := by
  have hD1 : 1 < (D : ℝ) := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hD
  have hD0 : 0 < (D : ℝ) := zero_lt_one.trans hD1
  have hlog1 : 1 ≤ Real.log (D : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hD0 hD
  have hlog : 0 < Real.log (D : ℝ) := zero_lt_one.trans_le hlog1
  have hs : 0 < s := zero_lt_one.trans hs1
  have hσ0 : 0 < σ := by linarith
  have hF : 0 ≤ finiteSourceLayer 1 2 N 3 := caseII_finiteSourceLayer_three_nonneg hN
  have hNm : (N - 1) % 2 = 0 := by
    have hnmod : N % 2 = 1 := Nat.odd_iff.mp hN
    omega
  have hFp : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2 := by
    apply finiteSourceLayer_nonneg_on_parityDomain (by norm_num) (N - 1)
    simp [KappaOneModel.parityDomain, hNm]
  have hL : 0 ≤ (Real.log (D : ℝ)) ^ (-Δ) := Real.rpow_nonneg hlog.le _
  have hlogyr : Real.log yr = (1 / 3 : ℝ) * Real.log (D : ℝ) := by
    rw [hyr, Real.log_rpow hD0]
  have hlogw : Real.log ((D : ℝ) ^ (1 / σ)) = (1 / σ) * Real.log (D : ℝ) := by
    rw [Real.log_rpow hD0]
  have hratio : 1 + K / Real.log yr = 1 + 3 * K / Real.log (D : ℝ) := by
    rw [hlogyr]; field_simp [ne_of_gt hlog]
  have hthree : 3 / s ≤ (3 : ℝ) := by
    simpa using div_le_self (by norm_num : (0 : ℝ) ≤ 3) hs1.le
  have hSigma : caseIIEndpointSigma11 K N (D : ℝ) σ =
      6 * K ^ 2 * finiteSourceLayer 1 2 (N - 1) 2 * σ / Real.log (D : ℝ) := by
    unfold caseIIEndpointSigma11; rw [hlogw]; field_simp [ne_of_gt hσ0, ne_of_gt hlog]
  let P : ℝ := C * Real.exp (Real.sqrt K)
  let E : ℝ := errorEnvelope H N (D : ℝ) d s
  have hP0 : 0 ≤ P := by positivity
  have hE0 : 0 ≤ E := by linarith
  have hPE : 1 ≤ P * E := by
    have hP3 : 3 ≤ P := by simpa [P] using hP
    calc 1 = 3 * (1 / 3 : ℝ) := by norm_num
      _ ≤ P * E := mul_le_mul hP3 hE (by norm_num) hP0
  have hmain :
      (3 / s) * (K / Real.log yr) * finiteSourceLayer 1 2 N 3 ≤
        P * E * (9 * K * finiteSourceLayer 1 2 N 3 / Real.log (D : ℝ)) := by
    rw [hlogyr]
    have hbase : 0 ≤ 9 * K * finiteSourceLayer 1 2 N 3 / Real.log (D : ℝ) := by positivity
    calc
      (3 / s) * (K / ((1 / 3 : ℝ) * Real.log (D : ℝ))) * finiteSourceLayer 1 2 N 3 =
          (9 * K * finiteSourceLayer 1 2 N 3 / Real.log (D : ℝ)) / s := by ring
      _ ≤ 9 * K * finiteSourceLayer 1 2 N 3 / Real.log (D : ℝ) := div_le_self hbase hs1.le
      _ = 1 * (9 * K * finiteSourceLayer 1 2 N 3 / Real.log (D : ℝ)) := by ring
      _ ≤ P * E * (9 * K * finiteSourceLayer 1 2 N 3 / Real.log (D : ℝ)) := mul_le_mul_of_nonneg_right hPE hbase
  have h11 :
      (3 / s) * (1 + K / Real.log yr) * caseIIEndpointSigma11 K N (D : ℝ) σ ≤
        P * E * (σ * (18 * K ^ 2 * (1 + 3 * K / Real.log (D : ℝ)) * finiteSourceLayer 1 2 (N - 1) 2) / Real.log (D : ℝ)) := by
    rw [hratio, hSigma]
    let X : ℝ := 6 * K ^ 2 * finiteSourceLayer 1 2 (N - 1) 2 * σ / Real.log (D : ℝ)
    have hX : 0 ≤ X := by dsimp [X]; positivity
    have hratio_pos : 0 ≤ 1 + 3 * K / Real.log (D : ℝ) := by positivity
    have hbase : 0 ≤ σ * (18 * K ^ 2 * (1 + 3 * K / Real.log (D : ℝ)) * finiteSourceLayer 1 2 (N - 1) 2) / Real.log (D : ℝ) := by positivity
    calc
      (3 / s) * (1 + 3 * K / Real.log (D : ℝ)) * X ≤ 3 * (1 + 3 * K / Real.log (D : ℝ)) * X := by gcongr
      _ = σ * (18 * K ^ 2 * (1 + 3 * K / Real.log (D : ℝ)) * finiteSourceLayer 1 2 (N - 1) 2) / Real.log (D : ℝ) := by dsimp [X]; ring
      _ = 1 * (σ * (18 * K ^ 2 * (1 + 3 * K / Real.log (D : ℝ)) * finiteSourceLayer 1 2 (N - 1) 2) / Real.log (D : ℝ)) := by ring
      _ ≤ P * E * (σ * (18 * K ^ 2 * (1 + 3 * K / Real.log (D : ℝ)) * finiteSourceLayer 1 2 (N - 1) 2) / Real.log (D : ℝ)) := mul_le_mul_of_nonneg_right hPE hbase
  have hq3eq : qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ 3 =
      (1 + (3 : ℝ) ^ d / Real.log (D : ℝ)) ^ 2 * ((3 : ℝ) / 2) ^ Δ := qD_opposite_three_eq_of_odd hH hN
  have hx0 : 0 ≤ (3 : ℝ) ^ d / Real.log (D : ℝ) := by positivity
  have hx1 : (3 : ℝ) ^ d / Real.log (D : ℝ) ≤ 1 := (div_le_one hlog).2 hsmall
  have hq3 : qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ 3 ≤ 4 * ((3 : ℝ) / 2) ^ Δ := by
    rw [hq3eq]
    have hp : 0 ≤ ((3 : ℝ) / 2) ^ Δ := Real.rpow_nonneg (by norm_num) _
    apply mul_le_mul_of_nonneg_right _ hp
    nlinarith [sq_nonneg ((3 : ℝ) ^ d / Real.log (D : ℝ))]
  have hq3nonneg : 0 ≤ qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ 3 := by rw [hq3eq]; positivity
  have hqend :
      (3 / s) * (1 + K / Real.log yr) *
          (P * (Real.log (D : ℝ)) ^ (-Δ) *
            (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ 3 /
                Real.log ((D : ℝ) ^ (1 / σ)) * (3 / 3))) ≤
        P * E * ((σ * caseIIQDRelativeEndpointCoeffSourceLarge (D : ℝ) Δ K / Real.log (D : ℝ)) * (Real.log (D : ℝ)) ^ (-Δ)) := by
    rw [hratio, hlogw]
    unfold caseIIQDRelativeEndpointCoeffSourceLarge
    let X : ℝ := P * (Real.log (D : ℝ)) ^ (-Δ)
    have hX : 0 ≤ X := by dsimp [X, P]; positivity
    have htail : 0 ≤ 6 * K ^ 2 * σ / Real.log (D : ℝ) := by positivity
    calc
      (3 / s) * (1 + 3 * K / Real.log (D : ℝ)) *
          (X * (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ 3 /
              ((1 / σ) * Real.log (D : ℝ)) * (3 / 3))) =
          (3 / s) * (1 + 3 * K / Real.log (D : ℝ)) * X *
            (6 * K ^ 2 * σ / Real.log (D : ℝ)) * qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ 3 := by field_simp [ne_of_gt hσ0, ne_of_gt hlog]
      _ ≤ 3 * (1 + 3 * K / Real.log (D : ℝ)) * X *
            (6 * K ^ 2 * σ / Real.log (D : ℝ)) * (4 * ((3 : ℝ) / 2) ^ Δ) := by gcongr
      _ = (σ * (72 * K ^ 2 * (1 + 3 * K / Real.log (D : ℝ)) * P * ((3 : ℝ) / 2) ^ Δ) / Real.log (D : ℝ)) * (Real.log (D : ℝ)) ^ (-Δ) := by dsimp [X]; ring
      _ = P * 1 * (σ * (72 * K ^ 2 * (1 + 3 * K / Real.log (D : ℝ)) * ((3 : ℝ) / 2) ^ Δ) / Real.log (D : ℝ)) * (Real.log (D : ℝ)) ^ (-Δ) := by ring
      _ ≤ P * (3 * E) * (σ * (72 * K ^ 2 * (1 + 3 * K / Real.log (D : ℝ)) * ((3 : ℝ) / 2) ^ Δ) / Real.log (D : ℝ)) * (Real.log (D : ℝ)) ^ (-Δ) := by
        have hbase2 : 0 ≤ P * (σ * (72 * K ^ 2 * (1 + 3 * K / Real.log (D : ℝ)) * ((3 : ℝ) / 2) ^ Δ) / Real.log (D : ℝ)) * (Real.log (D : ℝ)) ^ (-Δ) := by positivity
        have h13 : (1 : ℝ) ≤ 3 * E := by
          calc (1 : ℝ) = 3 * (1 / 3 : ℝ) := by norm_num
            _ ≤ 3 * E := mul_le_mul_of_nonneg_left hE (by norm_num)
        nlinarith
      _ = P * E * ((σ * (216 * K ^ 2 * (1 + 3 * K / Real.log (D : ℝ)) * ((3 : ℝ) / 2) ^ Δ) / Real.log (D : ℝ)) * (Real.log (D : ℝ)) ^ (-Δ)) := by ring
  have hlog_cancel :
      (Real.log (D : ℝ)) ^ (Δ - 1) * (Real.log (D : ℝ)) ^ (-Δ) =
        (Real.log (D : ℝ))⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hlog]
    congr 1
    ring
  have hbracket :
      (3 / s) * (K / Real.log yr) * finiteSourceLayer 1 2 N 3 +
          (3 / s) * (1 + K / Real.log yr) * caseIIEndpointSigma11 K N (D : ℝ) σ +
        (3 / s) * (1 + K / Real.log yr) * caseIIEndpointQD H N (D : ℝ) d Δ σ C K ≤
      caseIIPositiveDeltaIntegralPart H N (D : ℝ) yr d Δ σ C K s +
          P * E * (Real.log (D : ℝ)) ^ (-Δ) *
            caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K -
        P * E * (Real.log (D : ℝ)) ^ (-Δ) *
          (27 * K * (Real.log (D : ℝ)) ^ (Δ - 1)) := by
    have hqsplit :
        (3 / s) * (1 + K / Real.log yr) * caseIIEndpointQD H N (D : ℝ) d Δ σ C K =
          caseIIPositiveDeltaIntegralPart H N (D : ℝ) yr d Δ σ C K s +
            (3 / s) * (1 + K / Real.log yr) *
              (P * (Real.log (D : ℝ)) ^ (-Δ) *
                (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ 3 /
                    Real.log ((D : ℝ) ^ (1 / σ)) * (3 / 3))) := by
      unfold caseIIEndpointQD caseIIPositiveDeltaIntegralPart P
      ring
    rw [hqsplit]
    have ht :
        P * E * (9 * K * finiteSourceLayer 1 2 N 3 / Real.log (D : ℝ)) +
        P * E * (σ * (18 * K ^ 2 * (1 + 3 * K / Real.log (D : ℝ)) * finiteSourceLayer 1 2 (N - 1) 2) / Real.log (D : ℝ)) +
        P * E * ((σ * caseIIQDRelativeEndpointCoeffSourceLarge (D : ℝ) Δ K / Real.log (D : ℝ)) * (Real.log (D : ℝ)) ^ (-Δ)) =
        P * E * (Real.log (D : ℝ)) ^ (-Δ) * caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K -
        P * E * (Real.log (D : ℝ)) ^ (-Δ) * (27 * K * (Real.log (D : ℝ)) ^ (Δ - 1)) := by
      unfold caseIIEndpointRelativeCoeffSourceLarge caseIIAlgebraicEndpointCoeffSourceLarge
      simp only [div_eq_mul_inv]
      rw [← hlog_cancel]
      ring
    linarith [hmain, h11, hqend, ht]
  have hsource :
      K * 3 ^ 2 / (s * Real.log (D : ℝ)) ≤
        P * E * (Real.log (D : ℝ)) ^ (-Δ) *
          (27 * K * (Real.log (D : ℝ)) ^ (Δ - 1)) := by
    have hbase : 0 ≤ 9 * K / Real.log (D : ℝ) := by positivity
    calc
      K * 3 ^ 2 / (s * Real.log (D : ℝ)) =
          (9 * K / Real.log (D : ℝ)) / s := by ring
      _ ≤ 9 * K / Real.log (D : ℝ) := div_le_self hbase hs1.le
      _ ≤ P * E * (9 * K / Real.log (D : ℝ)) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hPE hbase
      _ ≤ P * E * (27 * K / Real.log (D : ℝ)) := by
        have hPE0 : 0 ≤ P * E := hPE.trans' zero_le_one
        apply mul_le_mul_of_nonneg_left _ hPE0
        have : 9 * K / Real.log (D : ℝ) ≤ 27 * K / Real.log (D : ℝ) := by
          apply (div_le_div_iff_of_pos_right hlog).2
          nlinarith
        exact this
      _ = P * E * (Real.log (D : ℝ)) ^ (-Δ) *
          (27 * K * (Real.log (D : ℝ)) ^ (Δ - 1)) := by
        calc
          P * E * (27 * K / Real.log (D : ℝ)) =
              P * E * (27 * K) * (Real.log (D : ℝ))⁻¹ := by
                simp only [div_eq_mul_inv]
                ring
          _ = P * E * (27 * K) *
              ((Real.log (D : ℝ)) ^ (Δ - 1) *
                (Real.log (D : ℝ)) ^ (-Δ)) := by rw [hlog_cancel]
          _ = P * E * (Real.log (D : ℝ)) ^ (-Δ) *
              (27 * K * (Real.log (D : ℝ)) ^ (Δ - 1)) := by ring
  have hbracket_source :
      (3 / s) * (K / Real.log yr) * finiteSourceLayer 1 2 N 3 +
          (3 / s) * (1 + K / Real.log yr) * caseIIEndpointSigma11 K N (D : ℝ) σ +
        (3 / s) * (1 + K / Real.log yr) * caseIIEndpointQD H N (D : ℝ) d Δ σ C K +
        K * 3 ^ 2 / (s * Real.log (D : ℝ)) ≤
      caseIIPositiveDeltaIntegralPart H N (D : ℝ) yr d Δ σ C K s +
        P * E * (Real.log (D : ℝ)) ^ (-Δ) *
          caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K := by
    linarith
  have hVz : suzukiVProduct S (z : ℝ) = suzukiVProduct S zr :=
    suzukiVProduct_natCeil_real_eq S hz
  unfold caseIIRoundedTransportErr
  rw [hVz]
  dsimp [P, E] at hbracket_source ⊢
  simpa only [mul_add, add_assoc, add_left_comm, add_comm] using add_le_add_left
    (mul_le_mul_of_nonneg_left hbracket_source (suzukiVProduct_pos S zr).le) B0



end MathlibNt.SieveTheory
