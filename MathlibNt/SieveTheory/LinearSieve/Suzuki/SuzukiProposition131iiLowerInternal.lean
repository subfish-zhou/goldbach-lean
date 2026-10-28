import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13PairingZeroSpecialized

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Quantitative lower profile in Proposition 13.1(ii), κ = 1. -/
noncomputable def proposition131iiLowerProfile (C s : ℝ) : ℝ :=
  Real.exp (-s * Real.log s - s * Real.log (Real.log (3 * s)) - C * s)

/-- Uniform two-sign quantitative lower form of Proposition 13.1(ii). -/
def Proposition131iiUniformQuantitativeLower (H : Section13HatLayers) : Prop :=
  ∃ C M : ℝ, 0 ≤ C ∧ 3 ≤ M ∧
    ∀ (sign : ErrorSign) (s : ℝ), M ≤ s →
      proposition131iiLowerProfile C s ≤ H.T sign s


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
