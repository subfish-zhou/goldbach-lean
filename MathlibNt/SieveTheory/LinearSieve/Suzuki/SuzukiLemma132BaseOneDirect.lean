import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13PairingZeroSpecialized
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteSourceLayerProp93

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false

/-!
# Direct `N = 1` base for Suzuki Lemma 13.2

At `κ = 1`, `β = 2`, the first finite source layer is explicit.  On its
legal odd-parity domain `x > 1`, its weighted value is `3 - x` for `x ≤ 3`
and is zero for `x ≥ 3`.  The Section-13 initial condition says that the
weighted positive hat layer is exactly one on `0 < x ≤ 3`.  Thus the fixed
constant `2` proves the whole `N = 1` layer, including the zero-support tail.
-/

private lemma finiteSourceLayer_one_eq_suzukiLayer_one (x : ℝ) :
    finiteSourceLayer 1 2 1 x = suzukiLayer 1 2 1 x := by
  simp [finiteSourceLayer]

private lemma weighted_finiteSourceLayer_one_of_le_three
    {x : ℝ} (hx0 : 0 < x) (hx3 : x ≤ 3) :
    x * finiteSourceLayer 1 2 1 x = 3 - x := by
  rw [finiteSourceLayer_one_eq_suzukiLayer_one]
  rw [suzukiLayer_one]
  norm_num [baseLower, min_eq_left hx3, dPowDensity]
  field_simp

/-- Pointwise fixed-witness form of the direct base case. -/
theorem lemma132_base_one_direct_two
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∀ x : ℝ, x ∈ KappaOneModel.parityDomain 2 1 →
      x * finiteSourceLayer 1 2 1 x ≤
        2 * x ^ 2 * H.T (ErrorSign.ofDepth 1) x := by
  intro x hxdom
  have hx1 : 1 < x := by
    norm_num [KappaOneModel.parityDomain] at hxdom ⊢
    exact hxdom
  have hx0 : 0 < x := by linarith
  by_cases hx3 : x ≤ 3
  · have hfinite := weighted_finiteSourceLayer_one_of_le_three hx0 hx3
    have hhat : x ^ 2 * H.T (ErrorSign.ofDepth 1) x = 1 := by
      have hi := hH.initial_plus x hx0 (by norm_num; exact hx3)
      norm_num [weightedHat] at hi ⊢
      exact hi
    rw [hfinite]
    calc
      3 - x ≤ 2 * 1 := by linarith
      _ = 2 * (x ^ 2 * H.T (ErrorSign.ofDepth 1) x) :=
        congrArg (fun z : ℝ => 2 * z) hhat.symm
      _ = 2 * x ^ 2 * H.T (ErrorSign.ofDepth 1) x := by ring
  · have h3x : 3 ≤ x := le_of_not_ge hx3
    have hzero : finiteSourceLayer 1 2 1 x = 0 :=
      finiteSourceLayer_eq_zero_of_le 2 1 (by norm_num; exact h3x)
    rw [hzero, mul_zero]
    have hT0 : 0 ≤ H.T (ErrorSign.ofDepth 1) x :=
      (hH.positive _ x hx0).le
    positivity


/-- Uniform direct base case for (13.13), with the compact constant `C = 2`.
The quantifier order is `∃ C, ∀ x`; the constant does not depend on `x` or on
`H`. -/
theorem lemma132_base_one_direct
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ,
      x ∈ KappaOneModel.parityDomain 2 1 →
      x * finiteSourceLayer 1 2 1 x ≤
        C * x ^ 2 * H.T (ErrorSign.ofDepth 1) x := by
  exact ⟨2, by norm_num, lemma132_base_one_direct_two hH⟩


end MathlibNt.SieveTheory
