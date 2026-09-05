import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedEndpointTransport

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- The rounded transport remainder, together with the sharp source-base term,
is absorbed by the canonical rounded positive-`Δ` endpoint packet.  The proof
expands `caseIIEndpointSigma11` and `caseIIEndpointQD`: the integral summand is
identified exactly with `caseIIPositiveDeltaIntegralPart`, while the three
remaining summands pay the fixed coefficients `A0`, `σ*A1`, and `σ*Aq0`. -/
theorem caseII_rounded_transportErr_le_positiveDelta_relative_packet_fixed_coefficients
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D z : ℕ} {yr zr d Δ σ C K B0 s : ℝ}
    (hH : Section13HatContract H 2) (hN : Odd N)
    (hD : Real.exp 1 ≤ (D : ℝ))
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hσ : 3 ≤ σ) (hs1 : 1 < s)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hsmall : (3 : ℝ) ^ d ≤ Real.log (D : ℝ))
    (hE : (1 / 3 : ℝ) ≤ errorEnvelope H N (D : ℝ) d s)
    (hyr : yr = (D : ℝ) ^ (1 / (3 : ℝ)))
    (hzr : zr = (D : ℝ) ^ (1 / s))
    (hz : z = ⌈zr⌉₊) :
    caseIIRoundedTransportErr S H N (D : ℝ) yr zr d Δ σ C K B0 s +
        suzukiVProduct S (z : ℝ) *
          (K * 3 ^ 2 / (s * Real.log (D : ℝ))) ≤
      B0 + suzukiVProduct S (z : ℝ) *
        (caseIIPositiveDeltaIntegralPart
            H N (D : ℝ) yr d Δ σ C K s +
          ((caseIIAlgebraicEndpointCoeffA0 N K *
                (Real.log (D : ℝ)) ^ (Δ - 1) +
            σ * caseIIAlgebraicEndpointCoeffA1 N K *
                (Real.log (D : ℝ)) ^ (Δ - 1) +
            σ * caseIIQDEndpointCoeffA0 d Δ C K /
                Real.log (D : ℝ) +
            27 * K * (Real.log (D : ℝ)) ^ (Δ - 1) *
              errorEnvelope H N (D : ℝ) d s) *
            (Real.log (D : ℝ)) ^ (-Δ))) := by
  have hD1 : 1 < (D : ℝ) :=
    (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hD
  have hD0 : 0 < (D : ℝ) := zero_lt_one.trans hD1
  have hlog1 : 1 ≤ Real.log (D : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hD0 hD
  have hlog : 0 < Real.log (D : ℝ) := zero_lt_one.trans_le hlog1
  have hs : 0 < s := zero_lt_one.trans hs1
  have hσ0 : 0 < σ := by linarith
  have hF : 0 ≤ finiteSourceLayer 1 2 N 3 :=
    caseII_finiteSourceLayer_three_nonneg hN
  have hNm : (N - 1) % 2 = 0 := by
    have hnmod : N % 2 = 1 := Nat.odd_iff.mp hN
    omega
  have hFp : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2 := by
    apply finiteSourceLayer_nonneg_on_parityDomain (by norm_num) (N - 1)
    simp [KappaOneModel.parityDomain, hNm]
  have hL : 0 ≤ (Real.log (D : ℝ)) ^ (-Δ) :=
    Real.rpow_nonneg hlog.le _
  have hlogyr : Real.log yr = (1 / 3 : ℝ) * Real.log (D : ℝ) := by
    rw [hyr, Real.log_rpow hD0]
  have hlogw : Real.log ((D : ℝ) ^ (1 / σ)) =
      (1 / σ) * Real.log (D : ℝ) := by
    rw [Real.log_rpow hD0]
  have hratio : 1 + K / Real.log yr =
      1 + 3 * K / Real.log (D : ℝ) := by
    rw [hlogyr]
    field_simp [ne_of_gt hlog]
  have hratio_le : 1 + 3 * K / Real.log (D : ℝ) ≤ 1 + 3 * K := by
    have hinv : (Real.log (D : ℝ))⁻¹ ≤ 1 := (inv_le_one₀ hlog).2 hlog1
    rw [div_eq_mul_inv]
    simpa [add_comm] using add_le_add_left
      (mul_le_mul_of_nonneg_left hinv
        (show 0 ≤ (3 : ℝ) * K by positivity)) 1
  have hthree : 3 / s ≤ (3 : ℝ) := by
    simpa using div_le_self (by norm_num : (0 : ℝ) ≤ 3) hs1.le
  have hSigma : caseIIEndpointSigma11 K N (D : ℝ) σ =
      6 * K ^ 2 * finiteSourceLayer 1 2 (N - 1) 2 * σ /
        Real.log (D : ℝ) := by
    unfold caseIIEndpointSigma11
    rw [hlogw]
    field_simp [ne_of_gt hσ0, ne_of_gt hlog]
  have hmain :
      (3 / s) * (K / Real.log yr) * finiteSourceLayer 1 2 N 3 ≤
        caseIIAlgebraicEndpointCoeffA0 N K / Real.log (D : ℝ) := by
    rw [hlogyr]
    unfold caseIIAlgebraicEndpointCoeffA0
    have hbase : 0 ≤ 9 * K * finiteSourceLayer 1 2 N 3 /
        Real.log (D : ℝ) := by positivity
    calc
      (3 / s) * (K / ((1 / 3 : ℝ) * Real.log (D : ℝ))) *
          finiteSourceLayer 1 2 N 3 =
          (9 * K * finiteSourceLayer 1 2 N 3 /
            Real.log (D : ℝ)) / s := by ring
      _ ≤ 9 * K * finiteSourceLayer 1 2 N 3 /
          Real.log (D : ℝ) := div_le_self hbase hs1.le
  have h11 :
      (3 / s) * (1 + K / Real.log yr) *
          caseIIEndpointSigma11 K N (D : ℝ) σ ≤
        σ * caseIIAlgebraicEndpointCoeffA1 N K /
          Real.log (D : ℝ) := by
    rw [hratio, hSigma]
    unfold caseIIAlgebraicEndpointCoeffA1
    let X : ℝ := 6 * K ^ 2 * finiteSourceLayer 1 2 (N - 1) 2 * σ /
      Real.log (D : ℝ)
    have hX : 0 ≤ X := by dsimp [X]; positivity
    calc
      (3 / s) * (1 + 3 * K / Real.log (D : ℝ)) * X ≤
          3 * (1 + 3 * K) * X := by gcongr
      _ = σ * (18 * K ^ 2 * (1 + 3 * K) *
          finiteSourceLayer 1 2 (N - 1) 2) /
          Real.log (D : ℝ) := by dsimp [X]; ring
  have hq3eq : qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ 3 =
      (1 + (3 : ℝ) ^ d / Real.log (D : ℝ)) ^ 2 * ((3 : ℝ) / 2) ^ Δ :=
    qD_opposite_three_eq_of_odd hH hN
  have hx0 : 0 ≤ (3 : ℝ) ^ d / Real.log (D : ℝ) := by positivity
  have hx1 : (3 : ℝ) ^ d / Real.log (D : ℝ) ≤ 1 :=
    (div_le_one hlog).2 hsmall
  have hq3 : qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ 3 ≤
      4 * ((3 : ℝ) / 2) ^ Δ := by
    rw [hq3eq]
    have hp : 0 ≤ ((3 : ℝ) / 2) ^ Δ := Real.rpow_nonneg (by norm_num) _
    apply mul_le_mul_of_nonneg_right _ hp
    nlinarith [sq_nonneg ((3 : ℝ) ^ d / Real.log (D : ℝ))]
  have hq3nonneg :
      0 ≤ qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ 3 := by
    rw [hq3eq]
    positivity
  have hqend :
      (3 / s) * (1 + K / Real.log yr) *
          (C * Real.exp (Real.sqrt K) * (Real.log (D : ℝ)) ^ (-Δ) *
            (6 * K ^ 2 *
              qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ 3 /
                Real.log ((D : ℝ) ^ (1 / σ)) * (3 / 3))) ≤
        (σ * caseIIQDEndpointCoeffA0 d Δ C K /
          Real.log (D : ℝ)) * (Real.log (D : ℝ)) ^ (-Δ) := by
    rw [hratio, hlogw]
    unfold caseIIQDEndpointCoeffA0
    let X : ℝ := C * Real.exp (Real.sqrt K) * (Real.log (D : ℝ)) ^ (-Δ)
    have hX : 0 ≤ X := by dsimp [X]; positivity
    have htail : 0 ≤ 6 * K ^ 2 * σ / Real.log (D : ℝ) := by positivity
    calc
      (3 / s) * (1 + 3 * K / Real.log (D : ℝ)) *
          (X * (6 * K ^ 2 *
            qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ 3 /
              ((1 / σ) * Real.log (D : ℝ)) * (3 / 3))) =
          (3 / s) * (1 + 3 * K / Real.log (D : ℝ)) * X *
            (6 * K ^ 2 * σ / Real.log (D : ℝ)) *
              qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ 3 := by
                field_simp [ne_of_gt hσ0, ne_of_gt hlog]
      _ ≤ 3 * (1 + 3 * K) * X *
            (6 * K ^ 2 * σ / Real.log (D : ℝ)) *
              (4 * ((3 : ℝ) / 2) ^ Δ) := by gcongr
      _ = (σ * (72 * K ^ 2 * (1 + 3 * K) * C *
              Real.exp (Real.sqrt K) * ((3 : ℝ) / 2) ^ Δ) /
            Real.log (D : ℝ)) * (Real.log (D : ℝ)) ^ (-Δ) := by
              dsimp [X]
              ring
  have hbracket :
      (3 / s) * (K / Real.log yr) * finiteSourceLayer 1 2 N 3 +
          (3 / s) * (1 + K / Real.log yr) *
            caseIIEndpointSigma11 K N (D : ℝ) σ +
        (3 / s) * (1 + K / Real.log yr) *
            caseIIEndpointQD H N (D : ℝ) d Δ σ C K ≤
      caseIIPositiveDeltaIntegralPart H N (D : ℝ) yr d Δ σ C K s +
        ((caseIIAlgebraicEndpointCoeffA0 N K +
            σ * caseIIAlgebraicEndpointCoeffA1 N K) /
              Real.log (D : ℝ) +
          (σ * caseIIQDEndpointCoeffA0 d Δ C K /
              Real.log (D : ℝ)) * (Real.log (D : ℝ)) ^ (-Δ)) := by
    have hqsplit :
        (3 / s) * (1 + K / Real.log yr) *
            caseIIEndpointQD H N (D : ℝ) d Δ σ C K =
          caseIIPositiveDeltaIntegralPart H N (D : ℝ) yr d Δ σ C K s +
            (3 / s) * (1 + K / Real.log yr) *
              (C * Real.exp (Real.sqrt K) * (Real.log (D : ℝ)) ^ (-Δ) *
                (6 * K ^ 2 *
                  qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ 3 /
                    Real.log ((D : ℝ) ^ (1 / σ)) * (3 / 3))) := by
      unfold caseIIEndpointQD caseIIPositiveDeltaIntegralPart
      ring
    rw [hqsplit]
    have hfixed :
        caseIIAlgebraicEndpointCoeffA0 N K / Real.log (D : ℝ) +
            σ * caseIIAlgebraicEndpointCoeffA1 N K / Real.log (D : ℝ) =
          (caseIIAlgebraicEndpointCoeffA0 N K +
            σ * caseIIAlgebraicEndpointCoeffA1 N K) / Real.log (D : ℝ) := by
      ring
    rw [← hfixed]
    linarith
  have htransport :
      caseIIRoundedTransportErr S H N (D : ℝ) yr zr d Δ σ C K B0 s ≤
        caseIIRoundedEndpointErr S H N D z yr zr d Δ σ C K B0 s := by
    have hVz : suzukiVProduct S (z : ℝ) = suzukiVProduct S zr :=
      suzukiVProduct_natCeil_real_eq S hz
    have hfinite := caseIIRoundedFiniteEndpointCorrections_eq_logD
      (N := N) (D := (D : ℝ)) (d := d) (Δ := Δ) (σ := σ)
      (C := C) (K := K) (s := s) (zr := zr) hD0 (ne_of_gt hs) hzr
    unfold caseIIRoundedTransportErr caseIIRoundedEndpointErr
    rw [hVz, hfinite]
    simpa [add_comm] using add_le_add_left
      (mul_le_mul_of_nonneg_left hbracket (suzukiVProduct_pos S zr).le) B0
  exact (add_le_add_left htransport
      (suzukiVProduct S (z : ℝ) *
        (K * 3 ^ 2 / (s * Real.log (D : ℝ))))).trans
    (caseII_rounded_positiveDelta_relative_packet_fixed_coefficients
      (S := S) (H := H) (N := N) (D := D) (z := z)
      (yr := yr) (zr := zr) (d := d) (Δ := Δ) (σ := σ)
      (C := C) (K := K) (B0 := B0) (s := s)
      hD1 hΔ0 hΔ1 hs1 hK hE hzr)




end MathlibNt.SieveTheory
