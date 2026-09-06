import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIPositiveEndpointPacket

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- The part of the algebraic endpoint coefficient which is independent of the
source cutoff parameter `σ`.  In particular it is fixed once `N` and `K` are
fixed. -/
noncomputable def caseIIAlgebraicEndpointCoeffA0 (N : ℕ) (K : ℝ) : ℝ :=
  9 * K * finiteSourceLayer 1 2 N 3

/-- The coefficient of `σ` in the algebraic endpoint coefficient.  This is
fixed once `N` and `K` are fixed. -/
noncomputable def caseIIAlgebraicEndpointCoeffA1 (N : ℕ) (K : ℝ) : ℝ :=
  18 * K ^ 2 * (1 + 3 * K) * finiteSourceLayer 1 2 (N - 1) 2

/-- The coefficient left after removing the single factor `σ` from the cubic
`q_D(3)` endpoint coefficient.  (The argument `d` is retained to match the
endpoint interface, although the explicit coefficient does not use it.) -/
noncomputable def caseIIQDEndpointCoeffA0
    (_d Δ C K : ℝ) : ℝ :=
  72 * K ^ 2 * (1 + 3 * K) * C * Real.exp (Real.sqrt K) *
    ((3 : ℝ) / 2) ^ Δ

/-- The cubic-`q_D(3)` coefficient after cancelling the already present common
scale `C * exp (sqrt K) * E`.  The factor `3` pays for `E ≥ 1/3`, so this
relative coefficient is independent of `C`. -/
noncomputable def caseIIQDRelativeEndpointCoeffA0
    (_d Δ _C K : ℝ) : ℝ :=
  216 * K ^ 2 * (1 + 3 * K) * ((3 : ℝ) / 2) ^ Δ

/-- Exact `a₀ + σ a₁` decomposition of the algebraic coefficient occurring in
`caseIIAlgebraicEndpointCoeff`.  The statement displays that coefficient
rather than using its coarse name as a black box. -/
theorem caseIIAlgebraicEndpointCoeff_exact_sigma_split
    (N : ℕ) (σ K : ℝ) :
    9 * K * finiteSourceLayer 1 2 N 3 +
        18 * K ^ 2 * σ * (1 + 3 * K) *
          finiteSourceLayer 1 2 (N - 1) 2 =
      caseIIAlgebraicEndpointCoeffA0 N K +
        σ * caseIIAlgebraicEndpointCoeffA1 N K := by
  unfold caseIIAlgebraicEndpointCoeffA0 caseIIAlgebraicEndpointCoeffA1
  ring

/-- Exact extraction of the single factor `σ` from the cubic `q_D(3)` endpoint
coefficient. -/
theorem caseIIQDEndpointCoeff_exact_sigma_split
    (d Δ σ C K : ℝ) :
    72 * K ^ 2 * σ * (1 + 3 * K) * C * Real.exp (Real.sqrt K) *
        ((3 : ℝ) / 2) ^ Δ =
      σ * caseIIQDEndpointCoeffA0 d Δ C K := by
  unfold caseIIQDEndpointCoeffA0
  ring

/-- The raw cubic endpoint coefficient is paid by one (not two) copies of the
common scale. -/
theorem caseIIQDEndpointCoeffA0_le_commonScale_mul_relative
    (d Δ C K E : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) (hE : (1 / 3 : ℝ) ≤ E) :
    caseIIQDEndpointCoeffA0 d Δ C K ≤
      (C * Real.exp (Real.sqrt K)) * E *
        caseIIQDRelativeEndpointCoeffA0 d Δ C K := by
  let X : ℝ :=
    72 * K ^ 2 * (1 + 3 * K) * ((3 : ℝ) / 2) ^ Δ
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hP : 0 ≤ C * Real.exp (Real.sqrt K) :=
    mul_nonneg hC (Real.exp_pos _).le
  have hthreeE : 1 ≤ 3 * E := by linarith
  calc
    caseIIQDEndpointCoeffA0 d Δ C K =
        (C * Real.exp (Real.sqrt K) * X) * 1 := by
          dsimp [X, caseIIQDEndpointCoeffA0]
          ring
    _ ≤ (C * Real.exp (Real.sqrt K) * X) * (3 * E) :=
      mul_le_mul_of_nonneg_left hthreeE (mul_nonneg hP hX)
    _ = (C * Real.exp (Real.sqrt K)) * E *
        caseIIQDRelativeEndpointCoeffA0 d Δ C K := by
          dsimp [X, caseIIQDRelativeEndpointCoeffA0]
          ring

/-- The fixed-coefficient relative endpoint expression.  Its only dependence
on the moving source cutoff is through the three displayed factors `σ`.
Consequently `a₀`, `a₁`, and `aq₀` can be frozen before an eventual argument. -/
noncomputable def caseIISharpPositiveEndpointRelativeCoeff
    (N : ℕ) (D d Δ σ C K : ℝ) : ℝ :=
  caseIIAlgebraicEndpointCoeffA0 N K * (Real.log D) ^ (Δ - 1) +
  σ * caseIIAlgebraicEndpointCoeffA1 N K * (Real.log D) ^ (Δ - 1) +
  σ * caseIIQDRelativeEndpointCoeffA0 d Δ C K / Real.log D +
  27 * K * (Real.log D) ^ (Δ - 1)

/-- Exact coefficient identity before inserting the error envelope. -/
theorem caseIISharpPositiveEndpointRelativeCoeff_eq
    (N : ℕ) (D d Δ σ C K : ℝ) :
    caseIISharpPositiveEndpointRelativeCoeff N D d Δ σ C K =
      caseIIAlgebraicEndpointCoeffA0 N K * (Real.log D) ^ (Δ - 1) +
      σ * caseIIAlgebraicEndpointCoeffA1 N K * (Real.log D) ^ (Δ - 1) +
      σ * caseIIQDRelativeEndpointCoeffA0 d Δ C K / Real.log D +
      27 * K * (Real.log D) ^ (Δ - 1) := by
  rfl

/-- Restatement of the positive endpoint packet with all `σ`-dependence
exposed.  Notice the position of `E`: the algebraic and cubic-`q_D` corrections
do **not** carry `E`; only the sharp raw-base term does.  This is the exact
shape needed before any later common-envelope absorption.

The premise is the positive endpoint packet written with the two explicit
production coefficients.  The conclusion is definitionally the same packet,
but with fixed coefficients `a₀`, `a₁`, and `aq₀`. -/
theorem caseII_positiveEndpoint_packet_fixed_coefficients
    {N : ℕ} {D d Δ σ C K E L I B0 V lhs : ℝ}
    (hpacket :
      lhs ≤ B0 + V *
        (I +
          ((9 * K * finiteSourceLayer 1 2 N 3 +
                18 * K ^ 2 * σ * (1 + 3 * K) *
                  finiteSourceLayer 1 2 (N - 1) 2) *
                (Real.log D) ^ (Δ - 1) +
            (72 * K ^ 2 * σ * (1 + 3 * K) * C *
                Real.exp (Real.sqrt K) * ((3 : ℝ) / 2) ^ Δ) /
              Real.log D +
            27 * K * (Real.log D) ^ (Δ - 1) * E) * L)) :
      lhs ≤ B0 + V *
        (I +
          ((caseIIAlgebraicEndpointCoeffA0 N K *
                (Real.log D) ^ (Δ - 1) +
            σ * caseIIAlgebraicEndpointCoeffA1 N K *
                (Real.log D) ^ (Δ - 1) +
            σ * caseIIQDEndpointCoeffA0 d Δ C K / Real.log D +
            27 * K * (Real.log D) ^ (Δ - 1) * E) * L)) := by
  convert hpacket using 1;
    unfold caseIIAlgebraicEndpointCoeffA0
      caseIIAlgebraicEndpointCoeffA1 caseIIQDEndpointCoeffA0;
    ring

/-- The same restatement specialized to the production normalization
`L = (log D)^(-Δ)` and the production error envelope.  This formulation makes
its correct location manifest and is directly consumable by eventual bounds. -/
theorem caseII_positiveEndpoint_relative_packet_fixed_coefficients
    (H : Section13HatLayers)
    {N : ℕ} {D d Δ σ s C K I B0 V lhs : ℝ}
    (hpacket :
      lhs ≤ B0 + V *
        (I +
          ((9 * K * finiteSourceLayer 1 2 N 3 +
                18 * K ^ 2 * σ * (1 + 3 * K) *
                  finiteSourceLayer 1 2 (N - 1) 2) *
                (Real.log D) ^ (Δ - 1) +
            (72 * K ^ 2 * σ * (1 + 3 * K) * C *
                Real.exp (Real.sqrt K) * ((3 : ℝ) / 2) ^ Δ) /
              Real.log D +
            27 * K * (Real.log D) ^ (Δ - 1) *
              errorEnvelope H N D d s) * (Real.log D) ^ (-Δ))) :
      lhs ≤ B0 + V *
        (I +
          ((caseIIAlgebraicEndpointCoeffA0 N K *
                (Real.log D) ^ (Δ - 1) +
            σ * caseIIAlgebraicEndpointCoeffA1 N K *
                (Real.log D) ^ (Δ - 1) +
            σ * caseIIQDEndpointCoeffA0 d Δ C K / Real.log D +
            27 * K * (Real.log D) ^ (Δ - 1) *
              errorEnvelope H N D d s) * (Real.log D) ^ (-Δ))) := by
  exact caseII_positiveEndpoint_packet_fixed_coefficients hpacket


end MathlibNt.SieveTheory
