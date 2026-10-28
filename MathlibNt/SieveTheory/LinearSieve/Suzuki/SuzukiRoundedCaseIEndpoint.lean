import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointFromCaseI

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- Integer cutoffs below a natural ceiling have exactly the same carrier as the
strict real cutoff. -/
theorem nat_lt_of_eq_ceil_iff {x : ℝ} {z p : ℕ} (hz : z = ⌈x⌉₊) :
    p < z ↔ (p : ℝ) < x := by
  rw [hz, Nat.lt_ceil]

/-- Suzuki's finite Euler product is unchanged when a strict real cutoff is
replaced by its natural ceiling. -/
theorem suzukiVProduct_natCeil_eq
    (S : BoundingSieve) {x : ℝ} {z : ℕ} (hz : z = ⌈x⌉₊) :
    suzukiVProduct S (z : ℝ) = suzukiVProduct S x := by
  exact SwitchingPrinciple.suzukiVProduct_natCeil_eq S hz


end MathlibNt.SieveTheory
