import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma147LowerFiniteFactor

/-!
# The even continuous-layer limit at the lower source

The available source theory proves nonnegativity of every dimension-one layer,
but does not yet prove summability of the lower even layers.  Accordingly this
module defines the unconditional limit honestly in `ℝ≥0∞`, as the supremum of
the even partial sums.  This allows the production depth to vary with the
finite carrier: no fixed-depth diagonal argument is used.
-/

open scoped Classical BigOperators ENNReal
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers

/-- The sum of the first `m` even dimension-one continuous source layers at
`β = 2`. -/
noncomputable def suzukiEvenSourceLowerPartialSum (m : ℕ) (s : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, suzukiLayer 1 2 (2 * (k + 1)) s

/-- The explicit even partial sum is exactly the finite source layer at depth
`2*m`. -/
theorem suzukiEvenSourceLowerPartialSum_eq_finiteSourceLayer (m : ℕ) (s : ℝ) :
    suzukiEvenSourceLowerPartialSum m s = finiteSourceLayer 1 2 (2 * m) s := by
  exact (finiteSourceLayer_two_mul_eq_sum_evenLayers m s).symm

/-- Every even layer is nonnegative on the lower parity domain `s ≥ 2`. -/
theorem suzukiLayer_one_two_even_nonneg {s : ℝ} (hs : 2 ≤ s) (k : ℕ) :
    0 ≤ suzukiLayer 1 2 (2 * (k + 1)) s := by
  apply suzukiLayer_one_nonneg_on_parityDomain (by norm_num : (1 : ℝ) < 2)
  simp [suzukiParityDomainOne,
    SuzukiFiniteContinuousLayers.KappaOneModel.parityDomain, hs]


end MathlibNt.SieveTheory
