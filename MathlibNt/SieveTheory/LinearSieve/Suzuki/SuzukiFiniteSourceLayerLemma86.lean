import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteSourceLayerProp93

/-!
# Suzuki Lemma 8.6 for the source-correct finite source layer

The normalized finite layer is only naturally continuous on its parity domain.
A lower clamp gives a global continuous extension without changing any value on
the source interval `[s, σ]` or at its prime coordinates.
-/

namespace MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers

open Set

noncomputable section

private theorem suzukiParityDomainOne_upperClosed {β : ℝ} {N : ℕ} :
    ∀ {x y : ℝ}, x ∈ suzukiParityDomainOne β N → x ≤ y →
      y ∈ suzukiParityDomainOne β N := by
  intro x y hx hxy
  by_cases hpar : N % 2 = 1
  · simp [suzukiParityDomainOne, KappaOneModel.parityDomain, hpar] at hx ⊢
    exact hx.trans_le hxy
  · have hzero : N % 2 = 0 := by omega
    simp [suzukiParityDomainOne, KappaOneModel.parityDomain, hzero] at hx ⊢
    exact hx.trans hxy

/-- Global lower-clamped extension of a finite source layer. -/
noncomputable def finiteSourceLayerOneClamp
    (β : ℝ) (N : ℕ) (s : ℝ) (t : ℝ) : ℝ :=
  finiteSourceLayer 1 β N (max s t)

@[simp] theorem finiteSourceLayerOneClamp_eq_of_le
    (β : ℝ) (N : ℕ) {s t : ℝ} (hst : s ≤ t) :
    finiteSourceLayerOneClamp β N s t = finiteSourceLayer 1 β N t := by
  simp [finiteSourceLayerOneClamp, max_eq_right hst]

/-- The clamp is globally continuous once its lower endpoint lies in the exact
source parity domain. -/
theorem finiteSourceLayerOneClamp_continuous
    {β s : ℝ} (hβ : 1 < β) (N : ℕ)
    (hsdom : s ∈ suzukiParityDomainOne β N) :
    Continuous (finiteSourceLayerOneClamp β N s) := by
  unfold finiteSourceLayerOneClamp
  apply (finiteSourceLayer_continuousOn_parityDomain hβ N).comp_continuous
    (continuous_const.max continuous_id)
  intro t
  exact suzukiParityDomainOne_upperClosed hsdom (le_max_left s t)


end
end MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open MeasureTheory intervalIntegral
open SuzukiFiniteContinuousLayers


end MathlibNt.SieveTheory.SwitchingPrinciple
