import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedTransportErrorBridge
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIFinalRelativeContraction

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- The relative coefficient used by the double-rounded Case-II endpoint.
The natural cutoffs occur only in the discrete sum and Euler product; all
analytic coordinates in this coefficient remain the exact real roots. -/
noncomputable def caseIIConcreteRoundedRelativeBracket
    (N : ℕ) (D d Δ σ C K : ℝ) : ℝ :=
  (1 + 3 * K / Real.log D) *
      (1 - 1 / σ) ^ (1 - Δ) * perturbation D d 0 3 +
    caseIISharpPositiveEndpointRelativeCoeff N D d Δ σ C K

/-- The repaired relative bracket is genuinely scale-free: changing the outer
constant `C` does not change it. -/
theorem caseIIConcreteRoundedRelativeBracket_C_independent
    (N : ℕ) (D d Δ σ C₁ C₂ K : ℝ) :
    caseIIConcreteRoundedRelativeBracket N D d Δ σ C₁ K =
      caseIIConcreteRoundedRelativeBracket N D d Δ σ C₂ K := by
  unfold caseIIConcreteRoundedRelativeBracket
    caseIISharpPositiveEndpointRelativeCoeff caseIIQDRelativeEndpointCoeffA0
  rfl


/-- Concrete relative assembly from the double-rounded sharp raw endpoint.

The premise `hRaw` is the canonicalized rounded raw conclusion obtained after
applying the explicit transport-error bridge.  A downstream direct theorem
connects it to the long Claim-14.5 input packet.  The rounded endpoint packet and the exact-real-root integral transport
are consumed internally. -/
theorem caseII_total_le_doubleRounded_concrete_relative_of_rawBase_natCeil
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D y z : ℕ} {yr zr d Δ σ C K B0 s : ℝ}
    (hD : Real.exp 1 ≤ (D : ℝ))
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hs1 : 1 < s)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hF0 : 0 ≤ finiteSourceLayer 1 2 N 3)
    (hF1 : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2)
    (hyr : yr = (D : ℝ) ^ (1 / (3 : ℝ)))
    (hzr : zr = (D : ℝ) ^ (1 / s))
    (_hyceil : y = ⌈yr⌉₊) (_hzceil : z = ⌈zr⌉₊)
    (hcut : 0 ≤ (1 - 1 / σ) ^ (1 - Δ))
    (hClaim14_6_iii : (∫ t in (3 : ℝ)..σ,
        qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) ≤
      (1 - 1 / σ) ^ (1 - Δ) *
        lambda H (ErrorSign.ofDepth N) (D : ℝ) d 0 3)
    (hLambdaCubic : lambda H (ErrorSign.ofDepth N) (D : ℝ) d 0 3 ≤
      perturbation (D : ℝ) d 0 3 *
        lambda H (ErrorSign.ofDepth N) (D : ℝ) d 0 s)
    (hP : 1 ≤ C * Real.exp (Real.sqrt K))
    (hPE : 1 ≤ (C * Real.exp (Real.sqrt K)) *
      errorEnvelope H N (D : ℝ) d s)
    (hE : (1 / 3 : ℝ) ≤ errorEnvelope H N (D : ℝ) d s)
    (hRaw :
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % 2 = N % 2),
        suzukiSourceV S n D z) ≤
        suzukiVProduct S (z : ℝ) * finiteSourceLayer 1 2 N s +
          caseIIRoundedEndpointErr S H N D z yr zr d Δ σ C K B0 s +
          suzukiVProduct S (z : ℝ) *
            (K * 3 ^ 2 / (s * Real.log (D : ℝ)))) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % 2 = N % 2),
        suzukiSourceV S n D z) ≤
      B0 + suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 N s +
          (C * Real.exp (Real.sqrt K)) *
            errorEnvelope H N (D : ℝ) d s *
            (Real.log (D : ℝ)) ^ (-Δ) *
            caseIIConcreteRoundedRelativeBracket
              N (D : ℝ) d Δ σ C K) := by
  have hD1 : 1 < (D : ℝ) :=
    (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hD
  have hs : 0 < s := zero_lt_one.trans hs1

  have hpacket := caseII_rounded_positiveDelta_relative_packet_fixed_coefficients
    (S := S) (H := H) (N := N) (D := D) (z := z)
    (yr := yr) (zr := zr) (d := d) (Δ := Δ) (σ := σ)
    (C := C) (K := K) (B0 := B0) (s := s)
    hD1 hΔ0 hΔ1 hs1 hK hE hzr
  have hIntegral := caseIIRoundedIntegralPart_source_relative
    (H := H) (N := N) (D := (D : ℝ)) (yr := yr)
    (d := d) (Δ := Δ) (σ := σ) (C := C) (K := K) (s := s)
    hyr hD1 hs hC hK hcut hClaim14_6_iii hLambdaCubic
  let P : ℝ := C * Real.exp (Real.sqrt K)
  let E : ℝ := errorEnvelope H N (D : ℝ) d s
  let L : ℝ := (Real.log (D : ℝ)) ^ (-Δ)
  let A : ℝ :=
    caseIIAlgebraicEndpointCoeffA0 N K * (Real.log (D : ℝ)) ^ (Δ - 1) +
    σ * caseIIAlgebraicEndpointCoeffA1 N K * (Real.log (D : ℝ)) ^ (Δ - 1)
  let Q : ℝ := σ * caseIIQDEndpointCoeffA0 d Δ C K / Real.log (D : ℝ)
  let Qr : ℝ :=
    σ * caseIIQDRelativeEndpointCoeffA0 d Δ C K / Real.log (D : ℝ)
  let B : ℝ := 27 * K * (Real.log (D : ℝ)) ^ (Δ - 1)
  let R : ℝ := (1 + 3 * K / Real.log (D : ℝ)) *
    (1 - 1 / σ) ^ (1 - Δ) * perturbation (D : ℝ) d 0 3
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos hD1
  have hL : 0 ≤ L := Real.rpow_nonneg hlog.le _
  have hE0 : 0 ≤ E := by dsimp [E]; linarith
  have hA0 : 0 ≤ A := by
    dsimp [A, caseIIAlgebraicEndpointCoeffA0, caseIIAlgebraicEndpointCoeffA1]
    positivity
  have hQscaled : Q ≤ P * E * Qr := by
    have hc := caseIIQDEndpointCoeffA0_le_commonScale_mul_relative
      d Δ C K E hC hK (by simpa [E] using hE)
    have hfac : 0 ≤ σ / Real.log (D : ℝ) := div_nonneg hσ hlog.le
    calc
      Q = (σ / Real.log (D : ℝ)) * caseIIQDEndpointCoeffA0 d Δ C K := by
        dsimp [Q]
        ring
      _ ≤ (σ / Real.log (D : ℝ)) *
          ((C * Real.exp (Real.sqrt K)) * E *
            caseIIQDRelativeEndpointCoeffA0 d Δ C K) :=
        mul_le_mul_of_nonneg_left hc hfac
      _ = P * E * Qr := by dsimp [P, Qr]; ring
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hAE : A + Q + B * E ≤ P * E * (A + Qr + B) := by
    have hA' : A ≤ P * E * A := by
      calc A = 1 * A := by ring
        _ ≤ (P * E) * A := mul_le_mul_of_nonneg_right (by simpa [P, E] using hPE) hA0
    have hB' : B * E ≤ P * E * B := by
      have := mul_le_mul_of_nonneg_right (by simpa [P] using hP) (mul_nonneg hE0 hB0)
      nlinarith
    nlinarith [hQscaled]
  have hEndpointScaled :
      caseIIRoundedEndpointErr S H N D z yr zr d Δ σ C K B0 s +
          suzukiVProduct S (z : ℝ) *
            (K * 3 ^ 2 / (s * Real.log (D : ℝ))) ≤
        B0 + suzukiVProduct S (z : ℝ) *
          (P * E * L * (R + A + Qr + B)) := by
    calc
      _ ≤ B0 + suzukiVProduct S (z : ℝ) *
          (caseIIPositiveDeltaIntegralPart H N (D : ℝ) yr d Δ σ C K s +
            (A + Q + B * E) * L) := by
              simpa [A, Q, B, E, L] using hpacket
      _ ≤ B0 + suzukiVProduct S (z : ℝ) *
          (P * E * L * R + (P * E * (A + Qr + B)) * L) := by
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (suzukiVProduct_pos S (z : ℝ)).le
        exact add_le_add (by simpa [P, E, L, R] using hIntegral)
          (mul_le_mul_of_nonneg_right hAE hL)
      _ = B0 + suzukiVProduct S (z : ℝ) *
          (P * E * L * (R + A + Qr + B)) := by ring
  calc
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % 2 = N % 2),
        suzukiSourceV S n D z) ≤
        suzukiVProduct S (z : ℝ) * finiteSourceLayer 1 2 N s +
          (caseIIRoundedEndpointErr S H N D z yr zr d Δ σ C K B0 s +
            suzukiVProduct S (z : ℝ) *
              (K * 3 ^ 2 / (s * Real.log (D : ℝ)))) := by
        simpa only [add_assoc] using hRaw
    _ ≤ suzukiVProduct S (z : ℝ) * finiteSourceLayer 1 2 N s +
          (B0 + suzukiVProduct S (z : ℝ) *
            (P * E * L * (R + A + Qr + B))) := by
        linarith [hEndpointScaled]
    _ = B0 + suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 N s +
          (C * Real.exp (Real.sqrt K)) *
            errorEnvelope H N (D : ℝ) d s *
            (Real.log (D : ℝ)) ^ (-Δ) *
            caseIIConcreteRoundedRelativeBracket N (D : ℝ) d Δ σ C K) := by
      dsimp [P, E, L, R, A, Qr, B, caseIIConcreteRoundedRelativeBracket,
        caseIISharpPositiveEndpointRelativeCoeff]
      ring

/-- Eventual consumer for the concrete rounded bracket. -/
theorem exists_caseIIConcreteRoundedRelativeBracket_lt_one_threshold
    (N : ℕ) (K C d Δ : ℝ)
    (hF0 : 0 ≤ finiteSourceLayer 1 2 N 3)
    (hF1 : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D →
      caseIIConcreteRoundedRelativeBracket N D d Δ (sourceSigma D d) C K < 1 := by
  simpa [caseIIConcreteRoundedRelativeBracket] using
    exists_caseII_source_relative_bracket_lt_one_threshold
      N K C d Δ hF0 hF1 hK hC hΔ0 hΔ1 hd




end MathlibNt.SieveTheory
