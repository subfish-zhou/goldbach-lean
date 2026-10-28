import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIAbsorption

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false

/-!
# Case I, (14.23): source-faithful remainder interface

The paper does not replace the two Lemma-8.7 endpoints by an arbitrary fixed
quotient.  Claim 14.6(ii) licenses Lemma 8.7, Claim 14.6(iii) supplies the main
contraction, and the two remaining endpoint terms retain the literal coefficient
`3 * (κ + 1) * K^2`, hence `6 * K^2` in the production specialization `κ = 1`.

The paper's subsequent estimates contain `σ^3 log (e σ)`.  Consequently the
already accepted `σ^2` scalar decay is necessary normalization data but is not,
by itself, the source estimate.  The predicates below freeze the exact additional
source inequalities without choosing numerical constants hidden by the paper's
`O` notation.
-/

/-- Exact normalized unit used by every side remainder in (14.23). -/
noncomputable def caseI1423RemainderUnit (B D σ : ℝ) : ℝ :=
  B / (Real.log (Real.log D) * σ)

/-- The literal `Σ₁₁` Lemma-8.7 endpoint at `τ=s`, `κ=1`, `β=2`. -/
noncomputable def caseI1423Sigma11Endpoint
    (S : BoundingSieve) (N D z : ℕ) (K s σ : ℝ) : ℝ :=
  suzukiVProduct S (z : ℝ) *
    (6 * K ^ 2 * finiteSourceLayer 1 2 (N - 1) (s - 1) /
      Real.log ((D : ℝ) ^ (1 / σ)))

/-- The literal `Σ₁₂` Lemma-8.7 endpoint at `τ=s`, `κ=1`.
This is definitionally the existing endpoint after cancelling `s/s`. -/
noncomputable def caseI1423Sigma12Endpoint
    (S : BoundingSieve) (H : Section13HatLayers)
    (N D z : ℕ) (C K d Δ s σ : ℝ) : ℝ :=
  C * Real.exp (Real.sqrt K) * suzukiVProduct S (z : ℝ) *
    (Real.log (D : ℝ)) ^ (-Δ) *
      (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite
        (D : ℝ) d Δ s / Real.log ((D : ℝ) ^ (1 / σ)))


end MathlibNt.SieveTheory
