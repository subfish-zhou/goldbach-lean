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

/-- The moving predecessor IH instantiates at every actual endpoint carrier
coordinate.  The illegal formal point `2-1=1` never occurs. -/
theorem evenEndpoint_pointwiseInductionContract_of_movingIH
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (M D Dmin : ℕ)
    (hDmin : 2 ≤ Dmin) (hM : Even M) (hM2 : 2 ≤ M) (hD : 4 ≤ D)
    (hscale : CarrierQuotientThresholdGeometry
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊) D Dmin
        (sourceSigma (D : ℝ) d) 2)
    (hrecursiveSigma : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊) D
        (sourceSigma (D : ℝ) d) 2,
      recursiveCoordinate D p ≤ sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d)
    (hError : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊) D
        (sourceSigma (D : ℝ) d) 2,
      errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (recursiveCoordinate D p) ≤
        errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (inheritedCoordinate D p))
    (hC : 0 ≤ C)
    (hIH : Lemma144EvenEndpointMovingIH S H C K d Δ (M - 1) Dmin) :
    PointwiseInductionContract
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊)
      (suzukiActualT S) (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ M D (sourceSigma (D : ℝ) d) 2 := by
  let z : ℕ := ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊
  have hpkt := lemma144_caseI_even_endpoint_source_packet S hM hM2 hD (z := z) rfl
  have hprime : ∀ p ∈ suzukiSupportedBelow S z, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hnatural : NaturalCeilPointwiseInductionContract
      (suzukiSupportedBelow S z) (suzukiActualT S)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ M D (sourceSigma (D : ℝ) d) 2 := by
    intro p hp
    have hpS := (Finset.mem_filter.mp hp).1
    have hpPrime := hprime p hpS
    have hqThreshold := ceilDiv_ge_threshold_of_scale hpPrime.pos (hscale p hp)
    have hq2 : 2 ≤ D ⌈/⌉ p := hDmin.trans hqThreshold
    exact hIH (D ⌈/⌉ p) p hqThreshold hq2 hpPrime.two_le
      (recursiveCoordinate D p) (hpkt p hpS).2.1
      (hrecursiveSigma p hp) (recursiveCoordinate_power_identity hpPrime.two_le hq2)
  apply naturalCeilContract_to_sourceCoordinate
    (suzukiSupportedBelow S z) (suzukiActualT S)
    (fun p => suzukiVProduct S p)
    (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
    2 C K Δ M D (sourceSigma (D : ℝ) d) 2
  · intro p _; exact (suzukiVProduct_pos S p).le
  · exact hC
  · intro p hp
    have hpS := (Finset.mem_filter.mp hp).1
    have hpPrime := hprime p hpS
    have hqThreshold := ceilDiv_ge_threshold_of_scale hpPrime.pos (hscale p hp)
    have hq2 : 2 ≤ D ⌈/⌉ p := hDmin.trans hqThreshold
    exact (Real.log_pos (by exact_mod_cast (show 1 < D ⌈/⌉ p by omega))).le
  · intro p hp; exact (hpkt p (Finset.mem_filter.mp hp).1).2.2
  · exact hError
  · simpa [z] using hnatural

/-- Exact endpoint recurrence together with its fully instantiated pointwise IH. -/
theorem evenEndpoint_recurrence_and_pointwise
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (M D Dmin : ℕ)
    (hDmin : 2 ≤ Dmin) (hM : Even M) (hM2 : 2 ≤ M) (hD : 4 ≤ D)
    (hscale : CarrierQuotientThresholdGeometry
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊) D Dmin
        (sourceSigma (D : ℝ) d) 2)
    (hrecursiveSigma : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊) D
        (sourceSigma (D : ℝ) d) 2,
      recursiveCoordinate D p ≤ sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d)
    (hError : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊) D
        (sourceSigma (D : ℝ) d) 2,
      errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (recursiveCoordinate D p) ≤
        errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (inheritedCoordinate D p))
    (hC : 0 ≤ C)
    (hIH : Lemma144EvenEndpointMovingIH S H C K d Δ (M - 1) Dmin) :
    suzukiActualT S M D ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ =
        ∑ p ∈ suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊,
          S.nu p * suzukiActualT S (M - 1) (D ⌈/⌉ p) p ∧
      PointwiseInductionContract
        (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊)
        (suzukiActualT S) (fun p => suzukiVProduct S p)
        (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
        2 C K Δ M D (sourceSigma (D : ℝ) d) 2 := by
  constructor
  · exact suzukiActualT_caseI_recurrence_strict S hM2
      (lemma144_caseI_even_endpoint_odd_carrier hM)
  · exact evenEndpoint_pointwiseInductionContract_of_movingIH S H C K d Δ M D Dmin
      hDmin hM hM2 hD hscale hrecursiveSigma hError hC hIH

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
