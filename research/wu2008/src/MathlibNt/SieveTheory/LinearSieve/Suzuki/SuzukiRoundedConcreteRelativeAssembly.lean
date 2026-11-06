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
