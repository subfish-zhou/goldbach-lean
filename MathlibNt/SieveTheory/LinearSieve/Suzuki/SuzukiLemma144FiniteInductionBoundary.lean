import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedBaseOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Equation1410
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

/-- Equation (14.10), with the recursive natural argument left literally as
`D ⌈/⌉ p`.  This is only the finite one-step assembly; neither endpoint sum is
smuggled into the hypotheses. -/
theorem lemma14_4_equation14_10_naturalCeil
    (support : Finset ℕ) (omega V : ℕ → ℝ)
    (T : ℕ → ℕ → ℕ → ℝ) (E : ℕ → ℕ → ℝ → ℝ)
    (Vz β C K Δ : ℝ) (N D : ℕ) (σ τ : ℝ)
    (hVz : Vz ≠ 0)
    (homega : ∀ p ∈ sigmaOneCarrier support D σ τ, 0 ≤ omega p)
    (hIH : PointwiseInductionContract support T V E β C K Δ N D σ τ) :
    sigmaOne support omega T N D σ τ ≤
      sigmaEleven support omega V Vz β N D σ τ +
        sigmaTwelve support omega V E Vz C K Δ N D σ τ := by
  exact equation14_10_finset_assembly support omega V T E Vz β C K Δ
    N D σ τ hVz homega hIH

/-- Pure finite-depth induction, indexed from the genuine base depth `1`.
The property itself includes `N`, so callers cannot erase depth or parity data.
This theorem closes only the logical induction once a mathematical successor
edge has been constructed. -/
theorem finiteDepth_induction_from_one
    (depth : ℕ) (P : ℕ → Prop)
    (hbase : P 1)
    (hstep : ∀ N, 1 ≤ N → N < depth → P N → P (N + 1)) :
    ∀ N, 1 ≤ N → N ≤ depth → P N := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro hN1 hNd
      by_cases hN : N = 1
      · simpa [hN] using hbase
      · have hpred1 : 1 ≤ N - 1 := by omega
        have hpredN : N - 1 < N := by omega
        have hpredDepth : N - 1 < depth := by omega
        have hprev : P (N - 1) := ih (N - 1) hpredN hpred1 (by omega)
        have hs := hstep (N - 1) hpred1 hpredDepth hprev
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ N)] using hs

/-- A domain-preserving specialization of the preceding induction principle.
It quantifies the actual Suzuki parity domain separately at every depth; no
uniform-in-`s` or global contraction statement is inferred. -/
theorem finiteDepth_induction_on_suzukiParityDomain
    (depth : ℕ) (P : ℕ → ℝ → Prop)
    (hbase : ∀ s, s ∈ suzukiParityDomainOne 2 1 → P 1 s)
    (hstep : ∀ N, 1 ≤ N → N < depth →
      (∀ t, t ∈ suzukiParityDomainOne 2 N → P N t) →
      ∀ s, s ∈ suzukiParityDomainOne 2 (N + 1) → P (N + 1) s) :
    ∀ N, 1 ≤ N → N ≤ depth →
      ∀ s, s ∈ suzukiParityDomainOne 2 N → P N s := by
  let Q : ℕ → Prop := fun N =>
    ∀ s, s ∈ suzukiParityDomainOne 2 N → P N s
  exact finiteDepth_induction_from_one depth Q hbase hstep

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
