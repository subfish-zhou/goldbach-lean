import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIFinalProducer

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Lemma 14.4: source-faithful moving-domain finite-depth contract

The source producer is only asserted while the continuous coordinate lies below
`sourceSigma D d`.  Accordingly, every clause quantified over `D` and a
coordinate carries the pointwise hypothesis

`x ≤ sourceSigma (D : ℝ) d`.

No theorem in this file promotes this moving-domain statement to the legacy
all-coordinate contract `Lemma144UniformNatCeilAt` or to
`GlobalDepthLemma144InductionHypothesis`.
-/

/-- The exact-power form of Lemma 14.4 on its source-native moving domain. -/
def Lemma144MovingDomainGlobalDepthAt
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (N Dmin : ℕ) : Prop :=
  ∀ D z : ℕ, Dmin ≤ D → 2 ≤ D → 2 ≤ z →
    ∀ x : ℝ, x ∈ KappaOneModel.parityDomain 2 N →
      x ≤ sourceSigma (D : ℝ) d →
      (D : ℝ) ^ (1 / x) = (z : ℝ) →
      suzukiActualT S N D z ≤
        suzukiVProduct S z *
          (finiteSourceLayer 1 2 N x +
            C * Real.exp (Real.sqrt K) *
              errorEnvelope H N (D : ℝ) d x *
                (Real.log (D : ℝ)) ^ (-Δ))

/-- Natural-ceiling form of the same moving-domain assertion.  The common
cutoff precedes `D`; the source endpoint is evaluated at that `D`. -/
def Lemma144MovingDomainNatCeilAt
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (N Dmin : ℕ) : Prop :=
  ∀ D : ℕ, Dmin ≤ D → 2 ≤ D →
    ∀ x : ℝ, x ∈ KappaOneModel.parityDomain 2 N →
      x ≤ sourceSigma (D : ℝ) d →
      2 ≤ ⌈(D : ℝ) ^ (1 / x)⌉₊ →
      suzukiActualT S N D ⌈(D : ℝ) ^ (1 / x)⌉₊ ≤
        suzukiVProduct S (⌈(D : ℝ) ^ (1 / x)⌉₊ : ℝ) *
          (finiteSourceLayer 1 2 N x +
            C * Real.exp (Real.sqrt K) *
              errorEnvelope H N (D : ℝ) d x *
                (Real.log (D : ℝ)) ^ (-Δ))


/-- The natural ceiling gives the exact-power form without changing the moving
coordinate domain. -/
theorem lemma144MovingDomainGlobalDepthAt_of_natCeil
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (N Dmin : ℕ)
    (hceil : Lemma144MovingDomainNatCeilAt S H C K d Δ N Dmin) :
    Lemma144MovingDomainGlobalDepthAt S H C K d Δ N Dmin := by
  intro D z hDmin hD2 hz2 x hx hxSigma hpower
  have hceilz : ⌈(D : ℝ) ^ (1 / x)⌉₊ = z := by
    rw [hpower]
    exact Nat.ceil_natCast z
  have hc := hceil D hDmin hD2 x hx hxSigma
  rw [hceilz] at hc
  exact hc hz2


end MathlibNt.SieveTheory
