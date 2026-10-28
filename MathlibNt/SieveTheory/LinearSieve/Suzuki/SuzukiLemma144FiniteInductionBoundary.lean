import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedBaseOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146FullInternal

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Lemma 14.4: finite-depth induction boundary

This file records the part of the requested assembly that follows from the
current source-faithful library without adding a Claim-14.5/14.6 conclusion,
a Case-II endpoint, or a `mainSum` inequality as a premise.

The base case and the natural-ceiling form of (14.10) are proved below.  The
finite logical induction is also closed while retaining the real `N,s` parity
domain.  The first unavailable mathematical edge is stated at the end: the
current Case-I/Case-II development does not produce a common successor theorem
from only the original recurrence/local-product/Section-13 data.  Consequently
there is no honest theorem here claiming the full Lemma 14.4 or the downstream
lower fundamental lemma.
-/

/-- The actual `N = 1` source-native base estimate at the natural ceiling.
The genuine odd parity domain and the base support range `s ≤ 3` are kept as
separate hypotheses; no
real-cutoff/cast-ceiling equality is used. -/
theorem lemma14_4_base_one_natCeil
    {S : BoundingSieve} {D z : ℕ} {s K : ℝ}
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hD : 1 < (D : ℝ))
    (hdom : s ∈ suzukiParityDomainOne 2 1)
    (hs3 : s ≤ 3)
    (hroot2 : 2 ≤ (D : ℝ) ^ (1 / s))
    (hK : 0 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K) :
    suzukiSourceV S 1 D z ≤ suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 1 s + 9 * K / (s * Real.log (D : ℝ))) := by
  have hs : 0 < s := by
    simp [suzukiParityDomainOne, KappaOneModel.parityDomain] at hdom
    linarith
  exact suzukiSourceV_one_le_V_natCeil_mul_fOne_add_localError
    hz hD hs hs3 hroot2 hK hlocal


/-!
## Earliest non-bypassable gap

`lemma14_4_base_one_natCeil` supplies the true base and
`lemma14_4_equation14_10_naturalCeil` supplies the source-correct finite
recurrence assembly.  To instantiate
`finiteDepth_induction_on_suzukiParityDomain`, one still needs a theorem whose
conclusion is the common `N+1` Lemma-14.4 bound and whose hypotheses are only
original source data.

The strongest current exact dispatcher,
`claim14_5_natEventual_exact_case_split_with_internalClaim146_caseII`, still asks
for `MovingCaseIIRelativeAssembler`, `MovingCaseIINormalization`, and a Case-I
producer.  Those are respectively the forbidden main-sum/endpoint-normalization
surface and the missing common Case-I successor.  Hence it cannot instantiate
`hstep` without reintroducing precisely the conclusions that the requested
interface forbids.

The downstream lower-sieve route has an independent earlier explicit boundary:
`lowerSuzukiNormalizedLayer_le_sourceCorrect_canonical` requires
`LowerSuzukiCanonicalCorrespondence`.  That proposition is not original local
product or Section-13 data; it is the unproved discrete-to-continuous comparison
identified in `LowerSuzukiSourceCorrectBridge` as the genuine Lemma-14.4 step.
Treating it as a premise would therefore merely rename the theorem to be proved.
-/


end MathlibNt.SieveTheory
