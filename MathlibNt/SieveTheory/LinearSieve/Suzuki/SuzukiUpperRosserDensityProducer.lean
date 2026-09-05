/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperSourcePTail

/-!
# Source factor for the dimension-one upper Rosser density

This module closes the source-normalization side of the upper Rosser density
producer on Chen's varying-`q` window.  It deliberately does not postulate a
Rosser-density inequality.  The only residual source input below is the literal
first-interval identity for Suzuki's already-defined odd layer series.  Above
`3`, the identity is derived from the parity integral DDE; the amplitude remains
separate and is then replaced by its independently produced value `2 exp γ`.
-/

namespace MathlibNt.SieveTheory

open MeasureTheory intervalIntegral Set
open SuzukiFiniteContinuousLayers

noncomputable section

/-- The literal first-interval statement for Suzuki's upper parity source.
This is a source-series identification, not an upper-density conclusion. -/
def SuzukiContinuousUpperFactorFirstIntervalIdentity : Prop :=
  ∀ s : ℝ, 3 / 2 ≤ s → s ≤ 3 →
    suzukiContinuousUpperFactor s = suzukiLowerSieveAmplitude / s

namespace SwitchingPrinciple

/-- The first upper source interval follows from the genuine source-series
finite-prefix identity and its proved summable limit. -/
theorem suzukiContinuousUpperFactorFirstIntervalIdentity_of_sourceContract
    (H : SuzukiLemma144KappaOne.Section13HatLayers)
    (hH : SuzukiLemma144KappaOne.Section13HatSourceContract H) :
    SuzukiContinuousUpperFactorFirstIntervalIdentity := by
  intro s hslo hs3
  have hs1 : 1 < s := by linarith
  have hsource := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub hH hs1 hs3
  unfold suzukiContinuousUpperFactor
  have hs0 : s ≠ 0 := ne_of_gt (by linarith)
  field_simp
  nlinarith

/-- On the complete varying-`q` window, Suzuki's genuine upper source factor is
exactly the Jurkat--Richert factor.  The first interval and post-3 source formula
are both consumed from the actual Section-13 source contract; no finite
Rosser-density estimate is assumed. -/
theorem suzukiContinuousUpperFactor_eq_jurkatRichertUpperLinearSieveFactor
    (H : SuzukiLemma144KappaOne.Section13HatLayers)
    (hH : SuzukiLemma144KappaOne.Section13HatSourceContract H)
    (hA : suzukiLowerSieveAmplitude =
      2 * Real.exp Real.eulerMascheroniConstant)
    {s : ℝ} (hslo : 3 / 2 ≤ s) (hshi : s ≤ 4) :
    suzukiContinuousUpperFactor s =
      jurkatRichertUpperLinearSieveFactor s := by
  by_cases hs3 : s ≤ 3
  · rw [suzukiContinuousUpperFactorFirstIntervalIdentity_of_sourceContract
      H hH s hslo hs3, hA]
    simp [jurkatRichertUpperLinearSieveFactor, hs3]
  · have h3s : 3 ≤ s := le_of_not_ge hs3
    have hsource :=
      suzukiContinuousUpperFactor_eq_second_source_formula
        hH h3s (hshi.trans (by norm_num : (4 : ℝ) ≤ 5))
    rw [hsource, hA]
    unfold jurkatRichertUpperLinearSieveFactor
    rw [if_neg hs3]
    rfl

/-- The complete upper-factor identification on Chen's varying-`q` window,
with the amplitude normalization discharged by the same genuine source
contract. -/
theorem suzukiContinuousUpperFactor_eq_jurkatRichertUpperLinearSieveFactor_of_sourceContract
    (H : SuzukiLemma144KappaOne.Section13HatLayers)
    (hH : SuzukiLemma144KappaOne.Section13HatSourceContract H)
    {s : ℝ} (hslo : 3 / 2 ≤ s) (hshi : s ≤ 4) :
    suzukiContinuousUpperFactor s =
      jurkatRichertUpperLinearSieveFactor s :=
  suzukiContinuousUpperFactor_eq_jurkatRichertUpperLinearSieveFactor H hH
    (suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract hH)
    hslo hshi

end SwitchingPrinciple
end


end MathlibNt.SieveTheory
