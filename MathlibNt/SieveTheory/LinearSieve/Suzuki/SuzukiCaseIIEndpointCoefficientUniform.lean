import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma132SlackFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma132FiniteHatUniformInterface
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISharpPositiveEndpointCoefficients

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false

/-!
# Uniform Case-II endpoint coefficients

The Case-II source carrier does not eventually vanish with the odd depth.  The
uniform estimate instead comes from Suzuki Lemma 13.2: specialize (13.13) at the
fixed endpoint coordinates `3` and `2`, then dominate the depth sign by the
maximum of the two fixed hat-layer values.
-/

/-- Uniform-in-depth bounds for the two finite source layers occurring in the
Case-II algebraic endpoint coefficient. -/
theorem caseII_endpoint_source_layers_uniform
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∃ L3 L2 : ℝ, 0 ≤ L3 ∧ 0 ≤ L2 ∧
      ∀ N : ℕ, Odd N → 3 ≤ N →
        finiteSourceLayer 1 2 N 3 ≤ L3 ∧
        finiteSourceLayer 1 2 (N - 1) 2 ≤ L2 := by
  obtain ⟨C, hC, hfinite⟩ :=
    finiteSourceLayer_le_uniform_mul_hat (lemma132_finiteLayerHatUniform_slack hH)
  let L3 : ℝ := C * (3 * max (H.T .plus 3) (H.T .minus 3))
  let L2 : ℝ := C * (2 * max (H.T .plus 2) (H.T .minus 2))
  have hT3p : 0 ≤ H.T .plus 3 := (hH.positive .plus 3 (by norm_num)).le
  have hT3m : 0 ≤ H.T .minus 3 := (hH.positive .minus 3 (by norm_num)).le
  have hT2p : 0 ≤ H.T .plus 2 := (hH.positive .plus 2 (by norm_num)).le
  have hT2m : 0 ≤ H.T .minus 2 := (hH.positive .minus 2 (by norm_num)).le
  refine ⟨L3, L2, ?_, ?_, ?_⟩
  · dsimp [L3]
    positivity
  · dsimp [L2]
    positivity
  · intro N hN hN3
    have hNmod : N % 2 = 1 := Nat.odd_iff.mp hN
    have hpredmod : (N - 1) % 2 = 0 := by omega
    have h3dom : (3 : ℝ) ∈ KappaOneModel.parityDomain 2 N := by
      rw [KappaOneModel.parityDomain, if_pos hNmod]
      norm_num
    have h2dom : (2 : ℝ) ∈ KappaOneModel.parityDomain 2 (N - 1) := by
      rw [KappaOneModel.parityDomain, if_neg (by omega : (N - 1) % 2 ≠ 1)]
      norm_num
    have h3 := hfinite N 3 (by omega) (by norm_num) h3dom
    have h2 := hfinite (N - 1) 2 (by omega) (by norm_num) h2dom
    have hsign3 :
        H.T (ErrorSign.ofDepth N) 3 ≤ max (H.T .plus 3) (H.T .minus 3) := by
      cases ErrorSign.ofDepth N with
      | plus => exact le_max_left _ _
      | minus => exact le_max_right _ _
    have hsign2 :
        H.T (ErrorSign.ofDepth (N - 1)) 2 ≤
          max (H.T .plus 2) (H.T .minus 2) := by
      cases ErrorSign.ofDepth (N - 1) with
      | plus => exact le_max_left _ _
      | minus => exact le_max_right _ _
    constructor
    · calc
        finiteSourceLayer 1 2 N 3 ≤ C * (3 * H.T (ErrorSign.ofDepth N) 3) := h3
        _ ≤ L3 := by
          dsimp [L3]
          gcongr
    · calc
        finiteSourceLayer 1 2 (N - 1) 2 ≤
            C * (2 * H.T (ErrorSign.ofDepth (N - 1)) 2) := h2
        _ ≤ L2 := by
          dsimp [L2]
          gcongr

/-- For fixed source data and fixed `K ≥ 0`, both Case-II algebraic endpoint
coefficients admit nonnegative bounds independent of the odd depth `N`. -/
theorem caseII_algebraic_endpoint_coefficients_uniform
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ A0 A1 : ℝ, 0 ≤ A0 ∧ 0 ≤ A1 ∧
      ∀ N : ℕ, Odd N → 3 ≤ N →
        caseIIAlgebraicEndpointCoeffA0 N K ≤ A0 ∧
        caseIIAlgebraicEndpointCoeffA1 N K ≤ A1 := by
  obtain ⟨L3, L2, hL3, hL2, hfinite⟩ :=
    caseII_endpoint_source_layers_uniform hH
  let A0 : ℝ := 9 * K * L3
  let A1 : ℝ := 18 * K ^ 2 * (1 + 3 * K) * L2
  refine ⟨A0, A1, ?_, ?_, ?_⟩
  · dsimp [A0]
    positivity
  · dsimp [A1]
    positivity
  · intro N hN hN3
    obtain ⟨h3, h2⟩ := hfinite N hN hN3
    constructor
    · unfold caseIIAlgebraicEndpointCoeffA0
      dsimp [A0]
      gcongr
    · unfold caseIIAlgebraicEndpointCoeffA1
      dsimp [A1]
      gcongr


end MathlibNt.SieveTheory
