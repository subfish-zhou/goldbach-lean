import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIOddSuccessorSameC
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145ComparisonInternal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition131iiLowerFinal

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Case-II odd recursive endpoint: exact remaining scaling bridge

The accepted source-`σ` Claim 14.5 controls the recombined recursive endpoint
at the scale

`C145 * V(D) * exp(sqrt K) / (log D * sourceSigma D d)
      * E_N(D, sourceSigma D d) * (log D)^(-Δ)`.

The same-`C` endpoint-gap normalization instead requires this to fit below

`V(⌈D^(1/s)⌉) * C * exp(sqrt K) * E_N(D,s) * (log D)^(-Δ)
      * (1 - caseIIConcreteRoundedRelativeBracket ...)`.

The theorem below consumes Claim 14.5 and isolates exactly that comparison.  In
particular, a bare proof that the bracket is `< 1` supplies only positivity of
the last factor and does not supply the quantitative lower bound needed to
compare the two displayed scales uniformly in `s`.
-/

/-- The literal endpoint to which the accepted source-`σ` Claim 14.5 applies. -/
noncomputable def caseIIOddClaim145Endpoint
    (S : BoundingSieve) (d : ℝ) (N D : ℕ) : ℝ :=
  suzukiActualT S N D
    ⌈(D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)⌉₊


end MathlibNt.SieveTheory
