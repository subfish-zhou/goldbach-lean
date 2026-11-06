import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteContinuousLayersKappaOne

open scoped Classical BigOperators
open Finset Set

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers

set_option autoImplicit false

/-- Proposition 11.8, specialized to the compact source strip needed in
Suzuki (13.11). -/
def Proposition118InitialStripSourceBound : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ (N : ℕ) (x : ℝ),
    1 ≤ N →
    x ∈ KappaOneModel.parityDomain 2 N →
    x ≤ 4 →
    x * finiteSourceLayer 1 2 N x ≤ B



end MathlibNt.SieveTheory
