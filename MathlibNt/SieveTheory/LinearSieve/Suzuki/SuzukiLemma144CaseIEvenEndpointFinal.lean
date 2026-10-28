import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIEvenEndpoint
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144RecursiveCoordinateSourceSigma


open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 2000000

/-!
# Lemma 14.4, even Case-I endpoint

This file closes the discrete recurrence and the moving-domain pointwise-IH
part of the exceptional endpoint `s = 2`.  It also records the first analytic
statement that is not exported by the current Case-I successor API.  In
particular, no estimate for `suzukiActualT S M D ...` is postulated.
-/

/-- The predecessor assertion needed at the actual quotient coordinates. -/
def Lemma144EvenEndpointMovingIH
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (n Dmin : ℕ) : Prop :=
  ∀ D z : ℕ, Dmin ≤ D → 2 ≤ D → 2 ≤ z →
    ∀ x : ℝ, x ∈ KappaOneModel.parityDomain 2 n →
      x ≤ sourceSigma (D : ℝ) d →
      (D : ℝ) ^ (1 / x) = (z : ℝ) →
      suzukiActualT S n D z ≤
        suzukiVProduct S z *
          (finiteSourceLayer 1 2 n x +
            C * Real.exp (Real.sqrt K) *
              errorEnvelope H n (D : ℝ) d x *
                (Real.log (D : ℝ)) ^ (-Δ))


/-- The exact first missing analytic edge.  Existing `Σ₁₁` production requires
`2-1 ∈ parityDomain 2 (M-1)`, which is false for even `M`; the carrier packet
above is insufficient because the current Lemma-8.7 API asks for the formal
closed lower endpoint rather than only the actual strict prime coordinates. -/
def CaseIEvenEndpointSigma11Edge (S : BoundingSieve) (M D : ℕ) (K σ : ℝ) : Prop :=
  sigmaEleven (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊) S.nu
      (fun p => suzukiVProduct S p)
      (suzukiVProduct S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊) 2 M D σ 2 ≤
    suzukiVProduct S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ *
      finiteSourceLayer 1 2 M 2 +
    suzukiVProduct S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ *
      (6 * K ^ 2 * finiteSourceLayer 1 2 (M - 1) 1 /
        Real.log ((D : ℝ) ^ (1 / σ)))


end MathlibNt.SieveTheory
