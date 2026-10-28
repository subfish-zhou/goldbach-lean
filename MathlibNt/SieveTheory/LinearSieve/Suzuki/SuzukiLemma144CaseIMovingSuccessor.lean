import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144MovingDomainFiniteInduction

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology
namespace MathlibNt.SieveTheory
open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne
set_option maxHeartbeats 3000000

/-- Instantiate the predecessor IH only at the actual quotient-recursive
coordinates.  The carrier geometry supplies their moving-domain bound. -/
theorem pointwiseInductionContract_of_movingDomainIH
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (N D Dmin : ℕ) (σ τ : ℝ)
    (hDmin : 2 ≤ Dmin)
    (hprime : ∀ p ∈ suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊, p.Prime)
    (hscale : CarrierQuotientThresholdGeometry
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) D Dmin σ τ)
    (hinherited : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) D σ τ,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1))
    (hV : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) D σ τ,
      0 ≤ suzukiVProduct S p)
    (hC : 0 ≤ C)
    (hSource : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) D σ τ,
      finiteSourceLayer 1 2 (N - 1) (recursiveCoordinate D p) ≤
        finiteSourceLayer 1 2 (N - 1) (inheritedCoordinate D p))
    (hError : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) D σ τ,
      errorEnvelope H (N - 1) (D ⌈/⌉ p : ℕ) d (recursiveCoordinate D p) ≤
        errorEnvelope H (N - 1) (D ⌈/⌉ p : ℕ) d (inheritedCoordinate D p))
    (hrecursiveSigma : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) D σ τ,
      recursiveCoordinate D p ≤ sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d)
    (hIH : Lemma144MovingDomainGlobalDepthAt S H C K d Δ (N - 1) Dmin) :
    PointwiseInductionContract
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) (suzukiActualT S)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ N D σ τ := by
  have hnatural : NaturalCeilPointwiseInductionContract
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) (suzukiActualT S)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ N D σ τ := by
    intro p hpCarrier
    have hpSupport : p ∈ suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊ :=
      (Finset.mem_filter.mp hpCarrier).1
    have hpPrime : p.Prime := hprime p hpSupport
    have hp2 : 2 ≤ p := hpPrime.two_le
    have hp0 : 0 < p := hpPrime.pos
    have hqThreshold : Dmin ≤ D ⌈/⌉ p :=
      ceilDiv_ge_threshold_of_scale hp0 (hscale p hpCarrier)
    have hq2 : 2 ≤ D ⌈/⌉ p := hDmin.trans hqThreshold
    have h2pD : 2 * p ≤ D :=
      (Nat.mul_le_mul_right p hDmin).trans (hscale p hpCarrier)
    have hrecursive : recursiveCoordinate D p ∈
        KappaOneModel.parityDomain 2 (N - 1) :=
      parityDomain_mono (hinherited p hpCarrier)
        (coordinate_bounds hp2 h2pD).1
    exact hIH (D ⌈/⌉ p) p hqThreshold hq2 hp2
      (recursiveCoordinate D p) hrecursive (hrecursiveSigma p hpCarrier)
      (recursiveCoordinate_power_identity hp2 hq2)
  have hlog : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) D σ τ,
      0 ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ) := by
    intro p hpCarrier
    have hpSupport := (Finset.mem_filter.mp hpCarrier).1
    have hp0 : 0 < p := (hprime p hpSupport).pos
    have hqThreshold := ceilDiv_ge_threshold_of_scale hp0 (hscale p hpCarrier)
    have hq2 : 2 ≤ D ⌈/⌉ p := hDmin.trans hqThreshold
    exact (Real.log_pos (by exact_mod_cast (show 1 < D ⌈/⌉ p by omega))).le
  exact naturalCeilContract_to_sourceCoordinate
    (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) (suzukiActualT S)
    (fun p => suzukiVProduct S p)
    (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
    2 C K Δ N D σ τ hV hC hlog hSource hError hnatural


end MathlibNt.SieveTheory
