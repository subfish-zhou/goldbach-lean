import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrence
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseSplitFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Equation1410

open scoped Classical BigOperators
open Finset Set

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

/-!
# Lemma 14.4: the low-prime endpoint and the uniformity boundary

The discrete object in Claim 14.5 has real cutoff arguments, whereas the actual
recurrence has natural cutoff arguments.  `suzukiActualTReal` is the canonical
rounded adapter.  On the natural arguments occurring in the recurrence it is
literally `suzukiActualT`.

The currently reachable Claim-14.5 interface is pointwise eventual: `N`, `s`
and the other endpoint data are fixed before its threshold is chosen.  In the
low-prime sum, however, `s = recursiveCoordinate D p`, and both that coordinate
and the carrier prime vary after the outer `D` is chosen.  Consequently the
pointwise theorem does not justify moving its threshold in front of `D`.
`ActualSigmaZeroClaim145Uniformity` freezes exactly that missing quantifier
swap.  The final theorem below is only the finite-sum algebra showing that this
uniform statement is sufficient; it is not advertised as an internal proof of
the missing uniformity.
-/

/-- Real-argument adapter for the actual natural-valued parity aggregate. -/
noncomputable def suzukiActualTReal (S : BoundingSieve) :
    ℕ → ℝ → ℝ → ℝ :=
  fun N D z => suzukiActualT S N ⌈D⌉₊ ⌈z⌉₊

@[simp] theorem suzukiActualTReal_natCast
    (S : BoundingSieve) (N D z : ℕ) :
    suzukiActualTReal S N (D : ℝ) (z : ℝ) = suzukiActualT S N D z := by
  simp [suzukiActualTReal]

/-- The sum of the pointwise Claim-14.5 budgets at the literal recursive
arguments of the low-prime part of (14.9). -/
noncomputable def suzukiSigmaZeroClaim145Budget
    (S : BoundingSieve) (H : Section13HatLayers)
    (N D z : ℕ) (d Δ σ K C145 : ℝ) : ℝ :=
  ∑ p ∈ (suzukiSupportedBelow S z).filter
      (fun p : ℕ => (p : ℝ) < (D : ℝ) ^ (1 / σ)),
    S.nu p *
      (C145 * claim14_5Scale S H (N - 1) (D ⌈/⌉ p : ℕ)
        d Δ σ K (recursiveCoordinate D p))

/-- The genuine uniformity needed to apply Claim 14.5 inside `Σ₀`.

The threshold is selected before `D`, `N`, and the carrier prime.  The two
coordinate hypotheses are the actual Claim-14.5 domain hypotheses; neither a
Claim-14.5 conclusion nor a bound for `Σ₀` is hidden among the source data of a
purported endpoint theorem. -/
def ActualSigmaZeroClaim145Uniformity
    (S : BoundingSieve) (H : Section13HatLayers)
    (d Δ σ K C145 : ℝ) : Prop :=
  ∃ D₀ : ℝ, 1 < D₀ ∧
    ∀ (D N z p : ℕ), D₀ ≤ (D : ℝ) → 2 ≤ N →
      p ∈ (suzukiSupportedBelow S z).filter
        (fun q : ℕ => (q : ℝ) < (D : ℝ) ^ (1 / σ)) →
      2 ≤ D ⌈/⌉ p →
      recursiveCoordinate D p ∈
        SuzukiFiniteContinuousLayers.suzukiParityDomainOne 2 (N - 1) →
      recursiveCoordinate D p ≤ σ →
      Claim14_5Bound (suzukiActualTReal S) S H (N - 1)
        (D ⌈/⌉ p : ℕ) (p : ℕ) d Δ σ K
        (recursiveCoordinate D p) C145

/-- Once the genuinely uniform Claim-14.5 statement is available, the endpoint
estimate is just monotonicity of the finite low-prime sum.  This lemma makes the
remaining analytic obligation exact; it does not accept the desired `Σ₀`
inequality as a premise. -/
theorem suzukiSigmaZero_eventually_le_claim145Budget_of_uniformity
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ σ K C145 : ℝ}
    (huniform : ActualSigmaZeroClaim145Uniformity S H d Δ σ K C145)
    (hnu : ∀ z p : ℕ, p ∈ suzukiSupportedBelow S z → 0 ≤ S.nu p)
    (hq2 : ∀ (D N z p : ℕ), 2 ≤ N →
      p ∈ (suzukiSupportedBelow S z).filter
        (fun q : ℕ => (q : ℝ) < (D : ℝ) ^ (1 / σ)) → 2 ≤ D ⌈/⌉ p)
    (hdom : ∀ (D N z p : ℕ), 2 ≤ N →
      p ∈ (suzukiSupportedBelow S z).filter
        (fun q : ℕ => (q : ℝ) < (D : ℝ) ^ (1 / σ)) →
      recursiveCoordinate D p ∈
        SuzukiFiniteContinuousLayers.suzukiParityDomainOne 2 (N - 1))
    (hcoordσ : ∀ (D N z p : ℕ), 2 ≤ N →
      p ∈ (suzukiSupportedBelow S z).filter
        (fun q : ℕ => (q : ℝ) < (D : ℝ) ^ (1 / σ)) →
      recursiveCoordinate D p ≤ σ) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ (D N z : ℕ), D₀ ≤ (D : ℝ) → 2 ≤ N →
      suzukiSigmaZero S N D z ((D : ℝ) ^ (1 / σ)) ≤
        suzukiSigmaZeroClaim145Budget S H N D z d Δ σ K C145 := by
  rcases huniform with ⟨D₀, hD₀, hu⟩
  refine ⟨D₀, hD₀, ?_⟩
  intro D N z hD hN
  unfold suzukiSigmaZero suzukiSigmaZeroClaim145Budget
  apply Finset.sum_le_sum
  intro p hp
  have hpSupport : p ∈ suzukiSupportedBelow S z := (Finset.mem_filter.mp hp).1
  have hpBound := hu D N z p hD hN hp (hq2 D N z p hN hp)
    (hdom D N z p hN hp) (hcoordσ D N z p hN hp)
  unfold Claim14_5Bound at hpBound
  rw [suzukiActualTReal_natCast] at hpBound
  exact mul_le_mul_of_nonneg_left hpBound (hnu z p hpSupport)


end MathlibNt.SieveTheory
