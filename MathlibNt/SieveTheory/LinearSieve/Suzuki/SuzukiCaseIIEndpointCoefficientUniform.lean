import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma132SlackFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIPositiveEndpointPacket

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


end MathlibNt.SieveTheory
