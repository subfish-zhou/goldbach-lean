import MathlibNt.SieveTheory.LinearSieve.Rosser.LowerRosserAccumulatorNormalization
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSourceToLowerRosserDensityTransport
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145Complete
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145OddLowStripSmallLogActual
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseISourceLargeLogPointwiseProducer
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIEvenEndpointSourceLargeLogPointwise
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIISourceLargeLogMoving
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144NoDminAllDepthGlue

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

/-- Once the even depth contains every supported pair-depth, the lower-Rosser
density is exactly the finite Euler product minus Suzuki's actual parity sum.
The depth depends on the finite carrier, but the identity has no limiting or
fixed-depth approximation. -/
theorem lowerRosserSetDensitySum_eq_euler_sub_suzukiActualT_all_supported
    (S : BoundingSieve) {D z : ℕ} (hD1 : 1 < D) (hzD : z ≤ D) :
    lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) =
      sourceDiscreteEuler S z -
        suzukiActualT S (2 * ((suzukiSupportedBelow S z).card + 1)) D z := by
  let qs := suzukiSupportedBelowList S z
  have hcarrier : qs.toFinset = suzukiSupportedBelow S z := by
    exact suzukiSupportedBelowList_toFinset S z
  have hprime : ∀ q ∈ qs, q.Prime := by
    intro q hq
    have hq' : q ∈ suzukiSupportedBelow S z := by
      rw [← hcarrier]
      exact List.mem_toFinset.mpr hq
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq').1
  have hqD : ∀ q ∈ qs, q < D := by
    intro q hq
    have hq' : q ∈ suzukiSupportedBelow S z := by
      rw [← hcarrier]
      exact List.mem_toFinset.mpr hq
    exact (Finset.mem_filter.mp hq').2.trans_le hzD
  have hordered : qs.Pairwise (· < ·) := by
    exact (Finset.sortedLT_sort (suzukiSupportedBelow S z)).pairwise
  rw [lowerRosserSetDensitySum_eq_euler_sub_boundaryAccum S qs hcarrier
    hprime hqD hordered hD1]
  rw [← suzukiActualT_all_supported_depths_eq_lowerRosserBoundaryAccum
    S D z hzD]


end MathlibNt.SieveTheory
