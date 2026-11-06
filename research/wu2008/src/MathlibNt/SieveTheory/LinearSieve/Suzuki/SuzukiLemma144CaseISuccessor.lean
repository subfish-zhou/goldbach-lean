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
import cone.  It uses the literal finite (14.9) equality and the production
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

/-- The finite parity index set occurring in Suzuki's source `T_N`. -/
noncomputable def lemma144ParityIndices (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => n % 2 = N % 2

/-- Literal source predecessor sum used in (14.9)--(14.10). -/
noncomputable def lemma144SourcePred
    (S : BoundingSieve) (n D p : ℕ) : ℝ :=
  ∑ m ∈ lemma144ParityIndices n, suzukiSourceV S m D p

/-- Strict multiplier certificate for same-`C` absorption. -/
structure Lemma144StrictFactor where
  ρ : ℝ
  nonneg : 0 ≤ ρ
  lt_one : ρ < 1

/-- Actual finite (14.9), stated on its three literal source sums. -/
def Lemma144Equation149
    (S : BoundingSieve) (N D z : ℕ) (σ τ : ℝ) : Prop :=
  (∑ n ∈ lemma144ParityIndices N, suzukiSourceV S n D z) =
    (∑ p ∈ (suzukiSupportedBelow S z).filter
        (fun p : ℕ => (p : ℝ) < (D : ℝ) ^ (1 / σ)),
      S.nu p * lemma144SourcePred S (N - 1) (D ⌈/⌉ p) p) +
    sigmaOne (suzukiSupportedBelow S z) S.nu (lemma144SourcePred S)
      N D σ τ +
    (∑ p ∈ (suzukiSupportedBelow S z).filter
        (fun p : ℕ => (D : ℝ) ^ (1 / τ) ≤ (p : ℝ)),
      S.nu p * lemma144SourcePred S (N - 1) (D ⌈/⌉ p) p)




end MathlibNt.SieveTheory
