import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLowerSieveFactorFirstIntervalIdentity

/-!
# Suzuki Lemma 14.7: continuous lower factor on the first interval

This module upgrades the finite-factor lower Rosser density estimate to the
actual first-interval continuous factor.  It uses only the one-sided fact that
the carrier-adaptive finite even source sum is bounded by the full summable
source series.  In particular, it makes no claim that an adaptive finite depth
is itself a limit.
-/

open scoped Classical BigOperators Interval
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false

/-- Every carrier-adaptive finite even source layer is bounded by the genuine
summable lower source series `T⁻(s)`. -/
theorem finiteSourceLayer_adaptive_le_suzukiProposition118SourceTMinus
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {α : Type*} (carrier : Finset α) {s : ℝ} (hs : 2 ≤ s) :
    finiteSourceLayer 1 2 (2 * (carrier.card + 1)) s ≤
      suzukiProposition118SourceTMinus s := by
  rw [finiteSourceLayer_two_mul_eq_sum_evenLayers]
  unfold suzukiProposition118SourceTMinus
  exact
    (summable_suzukiProposition118SourceTMinus_of_sourceContract hH hs).sum_le_tsum
      (Finset.range (carrier.card + 1))
      (fun k _ => suzukiLayer_one_two_even_nonneg hs k)


end MathlibNt.SieveTheory
