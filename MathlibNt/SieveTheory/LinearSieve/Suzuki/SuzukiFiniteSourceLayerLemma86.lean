import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteSourceLayerProp93
import MathlibNt.SieveTheory.SwitchingPrinciple

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

/-- Nonnegativity of the clamped extension on the source interval. -/
theorem finiteSourceLayerOneClamp_nonneg_on_Icc
    {β s σ : ℝ} (hβ : 1 < β) (N : ℕ)
    (hsdom : s ∈ suzukiParityDomainOne β N) :
    ∀ t ∈ Set.Icc s σ, 0 ≤ finiteSourceLayerOneClamp β N s t := by
  intro t ht
  rw [finiteSourceLayerOneClamp_eq_of_le β N ht.1]
  exact finiteSourceLayer_nonneg_on_parityDomain hβ N
    (suzukiParityDomainOne_upperClosed hsdom ht.1)

/-- Weighted antitonicity of the clamped extension on the unchanged interval. -/
theorem finiteSourceLayerOneClamp_weighted_antitoneOn_Icc
    {β s σ : ℝ} (hβ : 1 < β) (N : ℕ)
    (hsdom : s ∈ suzukiParityDomainOne β N) :
    AntitoneOn (fun t => finiteSourceLayerOneClamp β N s t * t) (Set.Icc s σ) := by
  intro x hx y hy hxy
  change finiteSourceLayerOneClamp β N s y * y ≤
    finiteSourceLayerOneClamp β N s x * x
  rw [finiteSourceLayerOneClamp_eq_of_le β N hx.1,
    finiteSourceLayerOneClamp_eq_of_le β N hy.1]
  have h := finiteSourceLayer_weighted_antitoneOn_parityDomain hβ N
    (suzukiParityDomainOne_upperClosed hsdom hx.1)
    (suzukiParityDomainOne_upperClosed hsdom hy.1) hxy
  simpa [mul_comm] using h

end
end MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open MeasureTheory intervalIntegral
open SuzukiFiniteContinuousLayers

/-- Suzuki Lemma 8.6 specialized to the source-correct finite parity sum
`T_N`.  The clamp is eliminated from the public conclusion. -/
theorem suzukiLemmaEightSix_finiteSourceLayer
    {S : BoundingSieve} {D w z s σ K β : ℝ} {N : ℕ}
    (hβ : 1 < β) (hsdom : s ∈ suzukiParityDomainOne β N)
    (hD : 1 < D) (hw2 : 2 ≤ w)
    (hs : 0 < s) (hsσ : s ≤ σ)
    (hz : z = D ^ (1 / s)) (hw : w = D ^ (1 / σ))
    (hK : 0 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    suzukiLemmaEightSixPrimeSum S D w z (finiteSourceLayer 1 β N) ≤
      (1 / s) * (∫ t in s..σ, finiteSourceLayer 1 β N t) +
        2 * K * finiteSourceLayer 1 β N s / Real.log w := by
  let H : ℝ → ℝ := finiteSourceLayerOneClamp β N s
  have hcont : Continuous H :=
    finiteSourceLayerOneClamp_continuous hβ N hsdom
  have hnonneg : ∀ t ∈ Set.Icc s σ, 0 ≤ H t :=
    finiteSourceLayerOneClamp_nonneg_on_Icc hβ N hsdom
  have hanti : AntitoneOn (fun t => H t * t) (Set.Icc s σ) :=
    finiteSourceLayerOneClamp_weighted_antitoneOn_Icc hβ N hsdom
  have hbound := suzukiLemmaEightSixDimensionOne hD hw2 hs hsσ hz hw
    hcont hnonneg hanti hK hlocal
  have hcoord : ∀ x ∈ Set.Icc w z,
      Real.log D / Real.log x ∈ Set.Icc s σ := by
    intro x hx
    exact SuzukiPowerCoordinates.log_div_log_mem_Icc hD hs hsσ hz hw hx
  have hprime : suzukiLemmaEightSixPrimeSum S D w z H =
      suzukiLemmaEightSixPrimeSum S D w z (finiteSourceLayer 1 β N) := by
    unfold suzukiLemmaEightSixPrimeSum
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    have ht := hcoord (p : ℝ) ⟨hp'.1, hp'.2.le⟩
    rw [show H (Real.log D / Real.log p) = finiteSourceLayer 1 β N
        (Real.log D / Real.log p) by
      exact finiteSourceLayerOneClamp_eq_of_le β N ht.1]
  have hint : (∫ t in s..σ, H t) =
      ∫ t in s..σ, finiteSourceLayer 1 β N t := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hsσ]
    intro t ht
    exact finiteSourceLayerOneClamp_eq_of_le β N ht.1
  have hsH : H s = finiteSourceLayer 1 β N s :=
    finiteSourceLayerOneClamp_eq_of_le β N le_rfl
  rw [hprime, hint, hsH] at hbound
  exact hbound

end MathlibNt.SieveTheory.SwitchingPrinciple
