import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseISourceLargeLogUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144EndpointSourceBoundsSourceLargeLogUniform

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Case-I endpoint consumer under the source parameter packet

This endpoint consumer discharges the literal `(14.23)` scalar with the sharpened
uniform theorem.  Its assumptions are exactly Suzuki's source packet, rather
than the stronger artificial condition
`7 / (1 - (Δ + 2 / Θ)) < d`.
-/

/-- Source-large-log endpoint bounds with the cutoff before `C`, `K`, depth, and
coordinate, under exactly the source parameter packet. -/
theorem exists_caseI1423EndpointSourceBounds_sourceLargeLog_uniform_of_source
    (S : BoundingSieve) (H : Section13HatLayers) {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ) :
    ∃ C1min : ℝ, 1 ≤ C1min ∧
      ∀ (C1 C K : ℝ), C1min ≤ C1 → 0 < C → 2 ≤ K →
        ∃ A11 A12 : ℝ, 0 ≤ A11 ∧ 0 ≤ A12 ∧
          ∀ (N D : ℕ) (s : ℝ), 3 ≤ D →
            C1 * K ^ Θ < Real.log (D : ℝ) →
            2 ≤ N → 2 ≤ s →
            s - 1 ∈ KappaOneModel.parityDomain 2 (N - 1) →
            s ≤ sourceSigma (D : ℝ) d →
            let σ := sourceSigma (D : ℝ) d
            let z := ⌈(D : ℝ) ^ (1 / s)⌉₊
            let B := sigma12InheritedBudget S H N D z C K d Δ s
            caseI1423Sigma11Endpoint S N D z K s σ ≤
                A11 * caseI1423RemainderUnit B (D : ℝ) σ ∧
              caseI1423Sigma12Endpoint S H N D z C K d Δ s σ ≤
                A12 * caseI1423RemainderUnit B (D : ℝ) σ := by
  obtain ⟨C1min, hC1min, hscalar⟩ :=
    exists_caseI1423_sourceScalar_sourceLargeLog_uniform_of_source hsrc
  refine ⟨C1min, hC1min, ?_⟩
  intro C1 C K hC1 hC hK
  obtain ⟨A11, A12, hA11, hA12, hendpoint⟩ :=
    caseI1423EndpointSourceBounds_of_sourceScalar S H C K d Δ hH hC
      hsrc.hDelta_pos hsrc.hDelta_lt hsrc.h14_1
  refine ⟨A11, A12, hA11, hA12, ?_⟩
  intro N D s hD3 hlarge hN hs hdom hsσ
  exact hendpoint D N s hD3
    (hscalar C1 K (D : ℝ) hC1 hK
      (by exact_mod_cast (show 2 ≤ D by omega)) hlarge)
    hN hs hdom hsσ


end MathlibNt.SieveTheory
