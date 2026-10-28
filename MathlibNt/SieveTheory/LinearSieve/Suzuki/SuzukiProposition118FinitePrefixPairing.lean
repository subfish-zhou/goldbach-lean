import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition118SourceTailPairingZero

/-!
# Proposition 11.8 from finite full-layer prefixes

The prefix below follows the production source definition exactly.  Above the
source boundary it contains the first `m` odd and first `m` even source layers;
below the boundary it uses the finite amplitude `A_m / s`.  Thus the initial
history is part of the prefix, rather than being silently replaced by the
out-of-domain values of the recursive layer formula.
-/

open scoped Classical BigOperators Interval
open Finset Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 800000


theorem suzukiLayer_weighted_eq_integral_to_upper
    {β s : ℝ} {n : ℕ} (hβ : 1 < β) (hn : 2 ≤ n)
    (hs : β + sourceEpsilon n ≤ s) :
    s * suzukiLayer 1 β n s =
      ∫ t in s..(β + n), suzukiLayer 1 β (n - 1) (t - 1) := by
  have hs0 : 0 < s := by
    have heps : (0 : ℝ) ≤ sourceEpsilon n := Nat.cast_nonneg _
    linarith
  rw [show s * suzukiLayer 1 β n s = suzukiLayerNumerator 1 β n s by
    simpa using rpow_mul_suzukiLayer 1 β n hs0]
  rw [SwitchingPrinciple.suzukiLayerNumerator_eq_sourceRecursion_of_two_le β s hn]
  have hlower : recursionLower β s n = min s (β + n) := by
    unfold recursionLower
    rw [max_eq_left (by simpa [sourceEpsilon] using hs)]
  rw [hlower]
  by_cases hsb : s ≤ β + n
  · rw [min_eq_left hsb]
  · have hbs : β + n ≤ s := le_of_not_ge hsb
    rw [min_eq_right hbs, intervalIntegral.integral_same]
    symm
    calc
      (∫ t in s..(β + n), suzukiLayer 1 β (n - 1) (t - 1)) =
          ∫ _t in s..(β + n), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_ge hbs] at ht
        apply suzukiLayer_eq_zero_of_le
        have hnsub : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
          exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ n)
        linarith [ht.1, hnsub]
      _ = 0 := intervalIntegral.integral_zero


end MathlibNt.SieveTheory
