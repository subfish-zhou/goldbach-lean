import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace Section10Lemma1028FirstCrossing

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Lemma 10.28: the global minus-envelope first crossing

This file isolates the topological first-crossing step on pp. 55--58.  It does
not assume the desired derivative sign and it does not take a common-majorant
record as input.  The only frozen source boundary is the stationary-point
exclusion obtained from the pairing calculation and the unit-interval estimate
(10.53).  This is the earliest presently unformalized analytic estimate.
-/

/-- The normalized part of (10.44), before subtracting `c₋`. -/
noncomputable def normalizedMinusBase
    (R ξ : ℝ → ℝ) (s : ℝ) : ℝ :=
  -R (s - 1) / (s * R s) + ξ s - 2 / s

/-- Minimal DDE/pairing data.  In particular this has no derivative-sign or
common-majorant field. -/
structure FirstCrossingDDEApparatus (R : ℝ → ℝ) (β : ℝ) where
  adjoint : ℝ → ℝ
  beta_ge_one : 1 ≤ β
  continuous : ContinuousOn R (Ioi (β - 1))
  positive : ∀ s, β - 1 < s → 0 < R s
  original_dde : ∀ s, β < s →
    HasDerivAt R (-(2 * R s + R (s - 1)) / s) s
  adjoint_positive : ∀ s, β ≤ s → 0 < adjoint s
  adjoint_dde : ∀ s, 0 < s →
    HasDerivAt (fun u => u * adjoint u)
      (2 * adjoint s + adjoint (s + 1)) s
  pairing_zero : ∀ s, β < s →
    s * adjoint s * R s = ∫ t in s - 1..s, adjoint (t + 1) * R t

/-- Canonical facts about Suzuki's `ξ`, separated from Lemma 10.28.  The final
field is the standard eventual comparison `ξ(s)-c-2/s ≫ log(es)` from
Proposition 10.20. -/
structure CanonicalXiTheorem (ξ : ℝ → ℝ) : Prop where
  continuous : Continuous ξ
  positive : ∀ s, 1 < s → 0 < ξ s
  equation : ∀ s, 1 < s → Real.exp (ξ s) - 1 = s * ξ s
  eventual_log_lower : ∀ c : ℝ, ∃ S A : ℝ, 3 ≤ S ∧ 1 ≤ A ∧
    ∀ s, S ≤ s →
      (1 / A) * Real.log (Real.exp 1 * s) ≤ ξ s - c - 2 / s

/-- Frozen boundary at (10.53): pairing-zero plus the unit-interval expansion
exclude a stationary point of the minus envelope once both `s` and `c₋` are
large.  Unlike the old residual API, this is neither a derivative-sign premise
nor a common-majorant premise. -/
def Equation1053MinusExclusion
    (R ξ : ℝ → ℝ) (s₀ C : ℝ) : Prop :=
  ∀ c, C ≤ c → ∀ s, s₀ ≤ s → normalizedMinusBase R ξ s ≠ c

/-- Pure first-crossing lemma.  Compactness chooses `c` large enough on the
initial interval.  If positivity occurred later, IVT would produce the
stationary point excluded by (10.53). -/
theorem global_nonpos_of_equation1053
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 4))
    {s₀ C : ℝ} (hs₀ : 4 ≤ s₀) (hC : 1 ≤ C)
    (h1053 : ∀ c, C ≤ c → ∀ s, s₀ ≤ s → f s ≠ c) :
    ∃ c, 1 ≤ c ∧ ∀ s, 4 ≤ s → f s - c ≤ 0 := by
  have hcont : ContinuousOn f (Icc 4 s₀) :=
    hf.mono (by intro x hx; exact hx.1)
  rcases (isCompact_Icc.bddAbove_image hcont) with ⟨B, hB⟩
  let c : ℝ := max C (B + 1)
  have hCc : C ≤ c := le_max_left _ _
  have hc1 : 1 ≤ c := hC.trans hCc
  have hlocal : ∀ x ∈ Icc 4 s₀, f x - c < 0 := by
    intro x hx
    have hfxB : f x ≤ B := hB ⟨x, hx, rfl⟩
    have hBc : B + 1 ≤ c := le_max_right _ _
    linarith
  refine ⟨c, hc1, ?_⟩
  intro s hs
  by_cases hss₀ : s ≤ s₀
  · exact (hlocal s ⟨hs, hss₀⟩).le
  · have hs₀s : s₀ ≤ s := le_of_not_ge hss₀
    by_contra hnot
    have hpos : 0 < f s - c := lt_of_not_ge hnot
    have hleft : f s₀ < c := by
      have := hlocal s₀ ⟨hs₀, le_rfl⟩
      linarith
    have hright : c ≤ f s := by linarith
    have hcIcc : c ∈ Icc (f s₀) (f s) := ⟨hleft.le, hright⟩
    have hcont' : ContinuousOn f (Icc s₀ s) :=
      hf.mono (by intro x hx; exact hs₀.trans hx.1)
    rcases intermediate_value_Icc hs₀s hcont' hcIcc with ⟨u, hu, hfu⟩
    exact h1053 c hCc u hu.1 hfu

/-- The explicit normalized slope is continuous on the legal half-line. -/
theorem normalizedMinusBase_continuousOn
    {R ξ : ℝ → ℝ} {β : ℝ} (h : FirstCrossingDDEApparatus R β)
    (hξ : CanonicalXiTheorem ξ) (hβ : β ≤ 3) :
    ContinuousOn (normalizedMinusBase R ξ) (Ici 4) := by
  intro s hs
  have hs4 : 4 ≤ s := hs
  have hsβ : β - 1 < s := by linarith
  have hsmβ : β - 1 < s - 1 := by linarith
  have hRs : 0 < R s := h.positive s hsβ
  have hs0 : s ≠ 0 := by linarith
  have hRc : ContinuousAt R s :=
    h.continuous.continuousAt (Ioi_mem_nhds hsβ)
  have hRmc : ContinuousAt (fun u : ℝ => R (u - 1)) s := by
    exact (h.continuous.continuousAt (Ioi_mem_nhds hsmβ)).comp_of_eq
      (continuousAt_id.sub continuousAt_const) (by simp)
  have hxic : ContinuousAt ξ s := hξ.continuous.continuousAt
  apply ContinuousAt.continuousWithinAt
  change ContinuousAt
    (fun u => -R (u - 1) / (u * R u) + ξ u - 2 / u) s
  exact (((hRmc.neg.div (continuousAt_id.mul hRc)
      (mul_ne_zero hs0 (ne_of_gt hRs))).add hxic).sub
        (continuousAt_const.div continuousAt_id hs0))

/-- Global nonpositive normalized (10.44), obtained rather than assumed. -/
theorem lemma1028_global_minus_slope
    {R ξ : ℝ → ℝ} {β s₀ C : ℝ}
    (h : FirstCrossingDDEApparatus R β) (hξ : CanonicalXiTheorem ξ)
    (hβ : β ≤ 3) (hs₀ : 4 ≤ s₀) (hC : 1 ≤ C)
    (h1053 : Equation1053MinusExclusion R ξ s₀ C) :
    ∃ c, 1 ≤ c ∧ ∀ s, 4 ≤ s →
      -R (s - 1) / (s * R s) + ξ s - c - 2 / s ≤ 0 := by
  obtain ⟨c, hc, hall⟩ := global_nonpos_of_equation1053
    (normalizedMinusBase_continuousOn h hξ hβ) hs₀ hC h1053
  refine ⟨c, hc, ?_⟩
  intro s hs
  dsimp [normalizedMinusBase] at hall
  linarith [hall s hs]

/-- Sanitized output contract: it records a cutoff, so the source's eventual
`ξ-c₋` lower bound is not incorrectly asserted on the fixed interval `[3,S]`.
The slope conclusion is populated by the constructor below, never supplied as
an input to it. -/
structure Section10CommonMajorant (R : ℝ → ℝ) where
  xi : ℝ → ℝ
  cMinus : ℝ
  cutoff : ℝ
  A : ℝ
  four_le_cutoff : 4 ≤ cutoff
  one_le_A : 1 ≤ A
  majorizes_log : ∀ s, cutoff ≤ s →
    (1 / A) * Real.log (Real.exp 1 * s) ≤ xi s - cMinus - 2 / s
  envelope_slope_nonpos : ∀ s, cutoff ≤ s →
    -(R (s - 1)) + s * (xi s - cMinus - 2 / s) * R s ≤ 0

/-- Lemma 10.28 constructor, conditional only on the canonical `ξ` theorem and
the explicitly frozen (10.53) stationary-point exclusion. -/
noncomputable def section10_lemma1028_commonMajorant
    {R ξ : ℝ → ℝ} {β s₀ C : ℝ}
    (h : FirstCrossingDDEApparatus R β) (hξ : CanonicalXiTheorem ξ)
    (hβ : β ≤ 3) (hs₀ : 4 ≤ s₀) (hC : 1 ≤ C)
    (h1053 : Equation1053MinusExclusion R ξ s₀ C) :
    Section10CommonMajorant R := by
  let w := lemma1028_global_minus_slope h hξ hβ hs₀ hC h1053
  let c : ℝ := Classical.choose w
  have hc : 1 ≤ c := (Classical.choose_spec w).1
  have hslope : ∀ s, 4 ≤ s →
      -R (s - 1) / (s * R s) + ξ s - c - 2 / s ≤ 0 :=
    (Classical.choose_spec w).2
  let wS := hξ.eventual_log_lower c
  let S : ℝ := Classical.choose wS
  let wA := Classical.choose_spec wS
  let A : ℝ := Classical.choose wA
  have hSA := Classical.choose_spec wA
  have hS : 3 ≤ S := hSA.1
  have hA : 1 ≤ A := hSA.2.1
  have hlog : ∀ s, S ≤ s →
      (1 / A) * Real.log (Real.exp 1 * s) ≤ ξ s - c - 2 / s := hSA.2.2
  let T : ℝ := max 4 S
  refine ⟨ξ, c, T, A, le_max_left _ _, hA, ?_, ?_⟩
  · intro s hs
    exact hlog s ((le_max_right 4 S).trans hs)
  intro s hs
  have hs4 : 4 ≤ s := (le_max_left 4 S).trans hs
  have hs0 : 0 < s := by linarith
  have hRs : 0 < R s := h.positive s (by linarith)
  have hn := hslope s hs4
  have hscale : 0 < s * R s := mul_pos hs0 hRs
  have heq :
      -(R (s - 1)) + s * (ξ s - c - 2 / s) * R s =
        (s * R s) * (-R (s - 1) / (s * R s) + ξ s - c - 2 / s) := by
    field_simp [ne_of_gt hs0, ne_of_gt hRs]
    ring
  rw [heq]
  exact mul_nonpos_of_nonneg_of_nonpos hscale.le hn


end Section10Lemma1028FirstCrossing
