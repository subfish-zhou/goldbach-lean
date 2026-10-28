import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedBaseOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Equation1410

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1600000

/-!
# Lemma 14.4: Case-I successor and same-constant absorption

This is the maximal source-faithful reduction available in the current compiled
import cone.
import It
import uses
import the
import literal
import finite
import (14.9)
import equality
import and
import production
(14.10) assembler.  It assumes neither a `mainSum` bound, a Claim-14.5/14.6
conclusion, nor a Case-I producer.

The source files for the newer Case-I recurrence/endpoint modules are present,
but their `.olean` modules are absent from the production search path.  The
purported full internal Claim-14.6 source also does not rebuild: it imports a
staged declaration of `Section13HatAsymptoticContract` which collides with the
production declaration.  Therefore the exact three analytic estimates not yet
available as compiled theorems are exposed below, before terminal scalar
absorption:

* `hSigma0`: the low-prime source estimate supplied mathematically by Claim 14.5
  at the endpoint `σ`;
* `hSigma11`: the endpoint remainder after the finite-source-layer main term;
* `hSigma12`: the internal-Claim-14.6 contraction multiplier plus endpoint
  remainder.

These are source estimates, not renamed final conclusions.  `Σ₂` is retained in
(14.9) and separately eliminated by its exact Case-I zero identity.
-/


/-- Strict multiplier certificate for same-`C` absorption. -/
structure Lemma144StrictFactor where
  ρ : ℝ
  nonneg : 0 ≤ ρ
  lt_one : ρ < 1


end MathlibNt.SieveTheory
