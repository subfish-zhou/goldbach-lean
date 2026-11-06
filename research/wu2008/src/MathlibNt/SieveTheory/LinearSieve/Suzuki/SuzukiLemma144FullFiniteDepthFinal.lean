import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIFinalBoundary
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIBaseOneSameC
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIOddSuccessorSameC
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144FiniteInductionFinal

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000


def Lemma144UniformNatCeilRestrictedAt
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (N Dmin : ℕ) (Q : ℝ → Prop) : Prop :=
  ∀ D : ℕ, Dmin ≤ D → 2 ≤ D →
    ∀ x : ℝ, x ∈ KappaOneModel.parityDomain 2 N → Q x →
    2 ≤ ⌈(D : ℝ) ^ (1 / x)⌉₊ →
    suzukiActualT S N D ⌈(D : ℝ) ^ (1 / x)⌉₊ ≤
      suzukiVProduct S (⌈(D : ℝ) ^ (1 / x)⌉₊ : ℝ) *
        (finiteSourceLayer 1 2 N x +
          C * Real.exp (Real.sqrt K) *
            errorEnvelope H N (D : ℝ) d x *
              (Real.log (D : ℝ)) ^ (-Δ))

theorem lemma144UniformNatCeilAt_of_restricted_cases
    {S : BoundingSieve} {H : Section13HatLayers}
    {C K d Δ : ℝ} {N DI DII : ℕ} {QI QII : ℝ → Prop}
    (hcover : ∀ x, x ∈ KappaOneModel.parityDomain 2 N → QI x ∨ QII x)
    (hI : Lemma144UniformNatCeilRestrictedAt S H C K d Δ N DI QI)
    (hII : Lemma144UniformNatCeilRestrictedAt S H C K d Δ N DII QII) :
    Lemma144UniformNatCeilAt S H C K d Δ N (max DI DII) := by
  intro D hD hD2 x hx hz
  rcases hcover x hx with hxI | hxII
  · exact hI D ((le_max_left DI DII).trans hD) hD2 x hx hxI hz
  · exact hII D ((le_max_right DI DII).trans hD) hD2 x hx hxII hz



end MathlibNt.SieveTheory
