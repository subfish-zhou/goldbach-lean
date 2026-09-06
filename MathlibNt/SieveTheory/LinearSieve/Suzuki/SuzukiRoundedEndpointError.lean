import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIIntegralTransportRelative
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISharpPositiveEndpointCoefficients
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiNatCeilPowerCarrier

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- Product-ratio coefficient written at the real cubic coordinate. -/
noncomputable def caseIIRoundedProductTransportCoeff (K yr : ℝ) : ℝ :=
  1 + K / Real.log yr

/-- Reciprocal logarithmic transport coefficient written at the real target
coordinate.  In the rounded route this is evaluated at `zr = D^(1/s)`, never
at the cast of its natural ceiling. -/
noncomputable def caseIIRoundedLogTransportCoeff (zr : ℝ) : ℝ :=
  1 / Real.log zr

/-- The finite (non-integral) rounded endpoint corrections.  Division by `s`
is paired with `1 / log zr`; after `zr = D^(1/s)` this is exactly division by
`log D`. -/
noncomputable def caseIIRoundedFiniteEndpointCorrections
    (N : ℕ) (D d Δ σ C K s zr : ℝ) : ℝ :=
  ((caseIIAlgebraicEndpointCoeffA0 N K +
      σ * caseIIAlgebraicEndpointCoeffA1 N K) / s) *
      caseIIRoundedLogTransportCoeff zr +
    ((σ * caseIIQDEndpointCoeffA0 d Δ C K) / s) *
      caseIIRoundedLogTransportCoeff zr * (Real.log D) ^ (-Δ)

/-- Rounded Case-II endpoint error.  Analytic coordinates `yr,zr` are real,
while the Euler product retains the natural ceiling carrier `z`. -/
noncomputable def caseIIRoundedEndpointErr
    (S : BoundingSieve) (H : Section13HatLayers) (N D z : ℕ)
    (yr zr d Δ σ C K B0 s : ℝ) : ℝ :=
  B0 + suzukiVProduct S (z : ℝ) *
    (caseIIPositiveDeltaIntegralPart H N (D : ℝ) yr d Δ σ C K s +
      caseIIRoundedFiniteEndpointCorrections N (D : ℝ) d Δ σ C K s zr)

/-- A strict cutoff at a real number has the same natural carrier as a strict
cutoff at its natural ceiling. -/
theorem nat_lt_natCeil_iff {x : ℝ} {z p : ℕ} (hz : z = ⌈x⌉₊) :
    p < z ↔ (p : ℝ) < x := by
  rw [hz, Nat.lt_ceil]

/-- Euler products are literally unchanged by replacing a strict real cutoff
with its natural ceiling. -/
theorem suzukiVProduct_natCeil_real_eq
    (S : BoundingSieve) {x : ℝ} {z : ℕ} (hz : z = ⌈x⌉₊) :
    suzukiVProduct S (z : ℝ) = suzukiVProduct S x := by
  exact suzukiVProduct_natCeil_eq S hz

/-- At the real cubic coordinate, the product-ratio coefficient has the exact
`1 + 3K/log D` form. -/
theorem caseIIRoundedProductTransportCoeff_cuberoot
    {D K yr : ℝ} (hD : 0 < D)
    (hyr : yr = D ^ (1 / (3 : ℝ))) :
    caseIIRoundedProductTransportCoeff K yr =
      1 + 3 * K / Real.log D := by
  have hlog : Real.log yr = (1 / 3 : ℝ) * Real.log D := by
    rw [hyr, Real.log_rpow hD]
  unfold caseIIRoundedProductTransportCoeff
  rw [hlog]
  ring

/-- The rounded integral term is bounded at the genuine real cubic coordinate.
No equality between the cube root and the cast of its ceiling is needed. -/
theorem caseIIRoundedIntegralPart_source_relative
    (H : Section13HatLayers) {N : ℕ} {D yr d Δ σ C K s : ℝ}
    (hyr : yr = D ^ (1 / (3 : ℝ)))
    (hD : 1 < D) (hs : 0 < s) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hcut : 0 ≤ (1 - 1 / σ) ^ (1 - Δ))
    (hiii : (∫ t in (3 : ℝ)..σ,
        qD H (ErrorSign.ofDepth N).opposite D d Δ t) ≤
      (1 - 1 / σ) ^ (1 - Δ) *
        lambda H (ErrorSign.ofDepth N) D d 0 3)
    (hcubic : lambda H (ErrorSign.ofDepth N) D d 0 3 ≤
      perturbation D d 0 3 *
        lambda H (ErrorSign.ofDepth N) D d 0 s) :
    caseIIPositiveDeltaIntegralPart H N D yr d Δ σ C K s ≤
      C * Real.exp (Real.sqrt K) * errorEnvelope H N D d s *
        (Real.log D) ^ (-Δ) *
        ((1 + 3 * K / Real.log D) *
          (1 - 1 / σ) ^ (1 - Δ) * perturbation D d 0 3) := by
  rw [hyr]
  exact caseIIPositiveDeltaIntegralPart_source_exact_relative
    H hD hs hC hK hcut hiii hcubic

/-- At the real target coordinate, reciprocal-log transport is exactly
`s/log D`. -/
theorem caseIIRoundedLogTransportCoeff_rpow
    {D s zr : ℝ} (hD : 0 < D) (hs : s ≠ 0)
    (hzr : zr = D ^ (1 / s)) :
    caseIIRoundedLogTransportCoeff zr = s / Real.log D := by
  have hlog : Real.log zr = (1 / s) * Real.log D := by
    rw [hzr, Real.log_rpow hD]
  unfold caseIIRoundedLogTransportCoeff
  rw [hlog]
  field_simp [hs]

/-- The two finite rounded corrections are exactly the production `log D`
terms.  In particular this proof uses `log (D^(1/s))`, not
`log ((ceil (D^(1/s)) : ℕ) : ℝ)`. -/
theorem caseIIRoundedFiniteEndpointCorrections_eq_logD
    {N : ℕ} {D d Δ σ C K s zr : ℝ}
    (hD : 0 < D) (hs : s ≠ 0) (hzr : zr = D ^ (1 / s)) :
    caseIIRoundedFiniteEndpointCorrections N D d Δ σ C K s zr =
      (caseIIAlgebraicEndpointCoeffA0 N K +
          σ * caseIIAlgebraicEndpointCoeffA1 N K) / Real.log D +
        (σ * caseIIQDEndpointCoeffA0 d Δ C K / Real.log D) *
          (Real.log D) ^ (-Δ) := by
  rw [caseIIRoundedFiniteEndpointCorrections,
    caseIIRoundedLogTransportCoeff_rpow hD hs hzr]
  field_simp [hs]

/-- Exact transport expansion of the rounded error with the real Euler product.
The only use of the natural rounded target is the carrier identity. -/
theorem caseIIRoundedEndpointErr_eq_realTransport
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D z : ℕ} {yr zr d Δ σ C K B0 s : ℝ}
    (hz : z = ⌈zr⌉₊) :
    caseIIRoundedEndpointErr S H N D z yr zr d Δ σ C K B0 s =
      B0 + suzukiVProduct S zr *
        (caseIIPositiveDeltaIntegralPart H N (D : ℝ) yr d Δ σ C K s +
          caseIIRoundedFiniteEndpointCorrections
            N (D : ℝ) d Δ σ C K s zr) := by
  unfold caseIIRoundedEndpointErr
  rw [suzukiVProduct_natCeil_real_eq S hz]

/-- Exact log/product transport expansion when both real coordinates are the
prescribed powers and the target Euler carrier is their natural ceiling. -/
theorem caseIIRoundedEndpointErr_eq_logD_realProduct
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D z : ℕ} {yr zr d Δ σ C K B0 s : ℝ}
    (hD : 0 < (D : ℝ)) (hs : s ≠ 0)
    (hzr : zr = (D : ℝ) ^ (1 / s)) (hz : z = ⌈zr⌉₊) :
    caseIIRoundedEndpointErr S H N D z yr zr d Δ σ C K B0 s =
      B0 + suzukiVProduct S zr *
        (caseIIPositiveDeltaIntegralPart H N (D : ℝ) yr d Δ σ C K s +
          (caseIIAlgebraicEndpointCoeffA0 N K +
              σ * caseIIAlgebraicEndpointCoeffA1 N K) /
                Real.log (D : ℝ) +
          (σ * caseIIQDEndpointCoeffA0 d Δ C K /
              Real.log (D : ℝ)) * (Real.log (D : ℝ)) ^ (-Δ)) := by
  rw [caseIIRoundedEndpointErr_eq_realTransport S H hz,
    caseIIRoundedFiniteEndpointCorrections_eq_logD hD hs hzr]
  ring

/-- Positive-`Δ` rounded relative packet with fixed coefficients.  The
algebraic and cubic-`q_D` terms do not acquire an error-envelope factor; only
the sharp raw-base correction does. -/
theorem caseII_rounded_positiveDelta_relative_packet_fixed_coefficients
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D z : ℕ} {yr zr d Δ σ C K B0 s : ℝ}
    (hD : 1 < (D : ℝ))
    (_hΔ0 : 0 < Δ) (_hΔ1 : Δ < 1)
    (hs1 : 1 < s) (hK : 0 ≤ K)
    (hE : (1 / 3 : ℝ) ≤ errorEnvelope H N (D : ℝ) d s)
    (hzr : zr = (D : ℝ) ^ (1 / s)) :
    caseIIRoundedEndpointErr S H N D z yr zr d Δ σ C K B0 s +
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
  have hD0 : 0 < (D : ℝ) := zero_lt_one.trans hD
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos hD
  have hs : 0 < s := zero_lt_one.trans hs1
  have hL : 0 ≤ (Real.log (D : ℝ)) ^ (-Δ) :=
    Real.rpow_nonneg hlog.le _
  have hfactor (A : ℝ) :
      A / Real.log (D : ℝ) =
        (A * (Real.log (D : ℝ)) ^ (Δ - 1)) *
          (Real.log (D : ℝ)) ^ (-Δ) := by
    rw [mul_assoc, ← Real.rpow_add hlog]
    have hexp : Δ - 1 + -Δ = -(1 : ℝ) := by ring
    rw [hexp, Real.rpow_neg hlog.le, Real.rpow_one]
    simp [div_eq_mul_inv]
  have hbase0 :
      K * 3 ^ 2 / (s * Real.log (D : ℝ)) ≤
        9 * K / Real.log (D : ℝ) := by
    calc
      K * 3 ^ 2 / (s * Real.log (D : ℝ)) =
          (9 * K / Real.log (D : ℝ)) / s := by ring
      _ ≤ 9 * K / Real.log (D : ℝ) :=
        div_le_self (div_nonneg (mul_nonneg (by norm_num) hK) hlog.le) hs1.le
  have hbase :
      K * 3 ^ 2 / (s * Real.log (D : ℝ)) ≤
        (27 * K * (Real.log (D : ℝ)) ^ (Δ - 1) *
          errorEnvelope H N (D : ℝ) d s) *
            (Real.log (D : ℝ)) ^ (-Δ) := by
    calc
      _ ≤ 9 * K / Real.log (D : ℝ) := hbase0
      _ = (27 * K * (Real.log (D : ℝ)) ^ (Δ - 1) * (1 / 3)) *
          (Real.log (D : ℝ)) ^ (-Δ) := by
            rw [hfactor (9 * K)]
            ring
      _ ≤ (27 * K * (Real.log (D : ℝ)) ^ (Δ - 1) *
          errorEnvelope H N (D : ℝ) d s) *
            (Real.log (D : ℝ)) ^ (-Δ) := by
        have hp : 0 ≤ 27 * K * (Real.log (D : ℝ)) ^ (Δ - 1) := by positivity
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hE hp) hL
  have hfinite := caseIIRoundedFiniteEndpointCorrections_eq_logD
    (N := N) (D := (D : ℝ)) (d := d) (Δ := Δ) (σ := σ)
    (C := C) (K := K) (s := s) (zr := zr) hD0 (ne_of_gt hs) hzr
  have hVz : 0 ≤ suzukiVProduct S (z : ℝ) :=
    (suzukiVProduct_pos S (z : ℝ)).le
  unfold caseIIRoundedEndpointErr
  rw [hfinite, add_assoc]
  apply add_le_add le_rfl
  calc
    suzukiVProduct S (z : ℝ) *
          (caseIIPositiveDeltaIntegralPart H N (D : ℝ) yr d Δ σ C K s +
            ((caseIIAlgebraicEndpointCoeffA0 N K +
                σ * caseIIAlgebraicEndpointCoeffA1 N K) /
                  Real.log (D : ℝ) +
              (σ * caseIIQDEndpointCoeffA0 d Δ C K /
                  Real.log (D : ℝ)) * (Real.log (D : ℝ)) ^ (-Δ))) +
        suzukiVProduct S (z : ℝ) *
          (K * 3 ^ 2 / (s * Real.log (D : ℝ))) =
      suzukiVProduct S (z : ℝ) *
        (caseIIPositiveDeltaIntegralPart H N (D : ℝ) yr d Δ σ C K s +
          ((caseIIAlgebraicEndpointCoeffA0 N K +
              σ * caseIIAlgebraicEndpointCoeffA1 N K) /
                Real.log (D : ℝ) +
            (σ * caseIIQDEndpointCoeffA0 d Δ C K /
                Real.log (D : ℝ)) * (Real.log (D : ℝ)) ^ (-Δ) +
            K * 3 ^ 2 / (s * Real.log (D : ℝ)))) := by ring
    _ ≤ suzukiVProduct S (z : ℝ) *
        (caseIIPositiveDeltaIntegralPart H N (D : ℝ) yr d Δ σ C K s +
          (((caseIIAlgebraicEndpointCoeffA0 N K +
              σ * caseIIAlgebraicEndpointCoeffA1 N K) /
                Real.log (D : ℝ) +
            (σ * caseIIQDEndpointCoeffA0 d Δ C K /
                Real.log (D : ℝ)) * (Real.log (D : ℝ)) ^ (-Δ)) +
            (27 * K * (Real.log (D : ℝ)) ^ (Δ - 1) *
              errorEnvelope H N (D : ℝ) d s) *
                (Real.log (D : ℝ)) ^ (-Δ))) := by
      gcongr
    _ = _ := by
      rw [show (caseIIAlgebraicEndpointCoeffA0 N K +
              σ * caseIIAlgebraicEndpointCoeffA1 N K) /
              Real.log (D : ℝ) =
            caseIIAlgebraicEndpointCoeffA0 N K / Real.log (D : ℝ) +
              (σ * caseIIAlgebraicEndpointCoeffA1 N K) /
                Real.log (D : ℝ) by ring,
        hfactor (caseIIAlgebraicEndpointCoeffA0 N K),
        hfactor (σ * caseIIAlgebraicEndpointCoeffA1 N K)]
      ring


end MathlibNt.SieveTheory
