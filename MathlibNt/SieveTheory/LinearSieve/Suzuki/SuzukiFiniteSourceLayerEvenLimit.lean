import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteContinuousLayersKappaOne
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

/-- The even lower-source partial sums increase with pair depth. -/
theorem suzukiEvenSourceLowerPartialSum_monotone {s : ℝ} (hs : 2 ≤ s) :
    Monotone (fun m => suzukiEvenSourceLowerPartialSum m s) := by
  apply monotone_nat_of_le_succ
  intro m
  change (∑ k ∈ Finset.range m, suzukiLayer 1 2 (2 * (k + 1)) s) ≤
    ∑ k ∈ Finset.range (m + 1), suzukiLayer 1 2 (2 * (k + 1)) s
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (suzukiLayer_one_two_even_nonneg hs m)

/-- The unconditional extended-real lower source-layer limit.  The name records
that this is a supremum; no finiteness or real summability assertion is hidden. -/
noncomputable def suzukiEvenSourceLowerLayerSup (s : ℝ) : ℝ≥0∞ :=
  ⨆ m : ℕ, ENNReal.ofReal (suzukiEvenSourceLowerPartialSum m s)

/-- Every finite even source layer, including one whose depth is chosen after
inspecting arithmetic data, is controlled by the extended-real limit. -/
theorem finiteSourceLayer_even_le_suzukiEvenSourceLowerLayerSup
    {s : ℝ} (m : ℕ) :
    ENNReal.ofReal (finiteSourceLayer 1 2 (2 * m) s) ≤
      suzukiEvenSourceLowerLayerSup s := by
  rw [← suzukiEvenSourceLowerPartialSum_eq_finiteSourceLayer]
  exact le_iSup (fun j : ℕ => ENNReal.ofReal (suzukiEvenSourceLowerPartialSum j s)) m

/-- Production-facing adaptive-depth bound.  In particular, the pair depth may
be the cardinality of a carrier plus one; it is not fixed before the data. -/
theorem finiteSourceLayer_adaptive_card_le_suzukiEvenSourceLowerLayerSup
    {α : Type*} {s : ℝ} (carrier : Finset α) :
    ENNReal.ofReal
        (finiteSourceLayer 1 2 (2 * (carrier.card + 1)) s) ≤
      suzukiEvenSourceLowerLayerSup s :=
  finiteSourceLayer_even_le_suzukiEvenSourceLowerLayerSup (carrier.card + 1)

/-- The exact adaptive depth used by the production lower-Rosser theorem is
controlled by the same limit, uniformly in the sieve and cutoff. -/
theorem finiteSourceLayer_supportedBelow_adaptive_le_suzukiEvenSourceLowerLayerSup
    (S : BoundingSieve) (z : ℕ) (s : ℝ) :
    ENNReal.ofReal
        (finiteSourceLayer 1 2 (2 * ((suzukiSupportedBelow S z).card + 1)) s) ≤
      suzukiEvenSourceLowerLayerSup s :=
  finiteSourceLayer_adaptive_card_le_suzukiEvenSourceLowerLayerSup
    (suzukiSupportedBelow S z)

/-- Genuine monotone convergence of the even partial sums to their extended-real
supremum.  This theorem remains valid when the supremum is infinite. -/
theorem tendsto_suzukiEvenSourceLowerPartialSum_ofReal {s : ℝ} (hs : 2 ≤ s) :
    Filter.Tendsto
      (fun m => ENNReal.ofReal (suzukiEvenSourceLowerPartialSum m s))
      Filter.atTop (nhds (suzukiEvenSourceLowerLayerSup s)) := by
  apply tendsto_atTop_iSup
  exact ENNReal.ofReal_mono.comp (suzukiEvenSourceLowerPartialSum_monotone hs)


end MathlibNt.SieveTheory
