import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144FiniteInductionBoundary

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

/-!
# Lemma 14.4 Case II: exact final dispatcher boundary

The accepted double-rounded endpoint starts at `2 ≤ N`; for odd depths this is
the range `3 ≤ N`.  The source-native base theorem instead gives the depth-one
bound with local remainder `9 K / (s log D)`.  This file records the exact common
same-`C` eventual conclusion and proves that these two disjoint producers are
sufficient.  It also names the first producer still absent from the accepted
chain: absorption of the depth-one local remainder into the same `C` envelope.
-/

/-- The natural-ceiling Lemma-14.4 estimate at one parameter value.  The
constant `C` occurs literally in the conclusion and is therefore shared by the
base and odd-successor branches. -/
def Lemma144CaseIISameCAt
    (S : BoundingSieve) (H : Section13HatLayers)
    (N D : ℕ) (d Δ C K s : ℝ) : Prop :=
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % 2 = N % 2),
      suzukiSourceV S n D z) ≤
    suzukiVProduct S (z : ℝ) *
      (finiteSourceLayer 1 2 N s +
        C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s *
          (Real.log (D : ℝ)) ^ (-Δ))


end MathlibNt.SieveTheory
