import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointCoefficientUniform

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

/-- The algebraic endpoint coefficient with the exact cubic product ratio
retained.  This scale-free definition lives upstream of both the rounded
transport bridge and the source-large uniform cutoff. -/
noncomputable def caseIIAlgebraicEndpointCoeffSourceLarge
    (N : ℕ) (D σ K : ℝ) : ℝ :=
  9 * K * finiteSourceLayer 1 2 N 3 +
    18 * K ^ 2 * σ * (1 + 3 * K / Real.log D) *
      finiteSourceLayer 1 2 (N - 1) 2

/-- The `C`-independent cubic `q_D(3)` relative coefficient, retaining the
exact source factor `1 + 3K/log D`. -/
noncomputable def caseIIQDRelativeEndpointCoeffSourceLarge
    (D Δ K : ℝ) : ℝ :=
  216 * K ^ 2 * (1 + 3 * K / Real.log D) * ((3 : ℝ) / 2) ^ Δ

/-- Positive finite endpoint terms used by the source-large-log Case-II
producer. -/
noncomputable def caseIIEndpointRelativeCoeffSourceLarge
    (N : ℕ) (D Δ σ K : ℝ) : ℝ :=
  caseIIAlgebraicEndpointCoeffSourceLarge N D σ K * (Real.log D) ^ (Δ - 1) +
    σ * caseIIQDRelativeEndpointCoeffSourceLarge D Δ K / Real.log D +
    27 * K * (Real.log D) ^ (Δ - 1)

end MathlibNt.SieveTheory
