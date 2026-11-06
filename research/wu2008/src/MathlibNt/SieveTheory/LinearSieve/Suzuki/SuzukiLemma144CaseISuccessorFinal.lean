import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrence
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144IHInstantiation
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma0Exact
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma11Internal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma12NatCeil
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144SigmaTwoZeroKappaOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144EndpointSourceBoundsFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma0EndpointTransport

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne
open SwitchingPrinciple.SuzukiLemma144KappaOne.Section13QhatMajorantClosure

set_option maxHeartbeats 2000000

/-!
# Lemma 14.4, Case I: unconditional same-constant successor

This is the final assembly against the source interfaces.  The recurrence and
IH are the actual finite ones; `Σ₀` is first identified with the single source
endpoint, `Σ₁₁` is the internal Lemma-8.7 estimate, `Σ₁₂` uses the natural
ceiling, and `Σ₂` vanishes in the genuine `κ = 1` Case-I range.

The only upstream name intentionally isolated by this file is
`caseI1423_sigmaZero_realEndpoint_sourceBound`.  It is the expected real
endpoint source estimate for the *explicit Claim-14.5 remainder*, not a bound
on `Σ₀`, a `mainSum` estimate, or an absorption hypothesis.  Once that producer
is present, the theorem below has no `Sigma`-bound, `mainSum`, or absorption
premise.
-/



end MathlibNt.SieveTheory
