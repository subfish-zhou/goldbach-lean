import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointTransport

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- Sharp source-native Case-II assembly at `β = 2`.

Unlike `caseII_total_le_concrete_finiteSourceLayer_add_errorEnvelope`, this
uses the unnormalised source assembly and therefore retains the base-layer loss
at its native `1 / (s * log D)` scale. -/
theorem caseII_total_le_concrete_finiteSourceLayer_add_rawBase
    (S : BoundingSieve)
    {K s endpointErr : ℝ} {N D y z : ℕ}
    (hN : Odd N)
    (hD : Real.exp 1 ≤ (D : ℝ))
    (hs : 0 < s) (hs3 : s ≤ 3) (hK : 0 ≤ K)
    (hyz : y ≤ z) (hyLower : (y - 1) ^ 3 < D) (hyUpper : D ≤ y ^ 3)
    (hz : (z : ℝ) = (D : ℝ) ^ (1 / s)) (hz2 : 2 ≤ (z : ℝ))
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hendpoint :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
        suzukiVProduct S (z : ℝ) *
          ((3 / s) * finiteSourceLayer 1 2 N 3) + endpointErr) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
      suzukiVProduct S (z : ℝ) * finiteSourceLayer 1 2 N s + endpointErr +
        suzukiVProduct S (z : ℝ) *
          (K * 3 ^ 2 / (s * Real.log (D : ℝ))) := by
  have hDone : 1 < (D : ℝ) :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hD
  have hbase : suzukiSourceV S 1 D z ≤
      suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 1 s +
          K * 3 ^ 2 / (s * Real.log (D : ℝ))) :=
    suzukiSourceV_one_le_V_mul_fOne_add_localError
      hDone hs hs3 hz hz2 hK hlocal
  have hendpoint' :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
        suzukiVProduct S (z : ℝ) *
          (((2 : ℝ) + 1) / s * finiteSourceLayer 1 2 N ((2 : ℝ) + 1)) +
            endpointErr := by
    convert hendpoint using 1; norm_num
  have hbase' : suzukiSourceV S 1 D z ≤
      suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 1 s +
          K * ((2 : ℝ) + 1) ^ 2 / (s * Real.log (D : ℝ))) := by
    convert hbase using 1; norm_num
  have hraw := caseII_source_finite_assembly
    (S := S) (β := (2 : ℝ)) (s := s) (K := K)
    (Vz := suzukiVProduct S (z : ℝ)) (endpointErr := endpointErr)
    hN hs (by norm_num at hs3 ⊢; exact hs3)
    hyz hyLower hyUpper hendpoint' hbase'
  convert hraw using 1; norm_num



end MathlibNt.SieveTheory
