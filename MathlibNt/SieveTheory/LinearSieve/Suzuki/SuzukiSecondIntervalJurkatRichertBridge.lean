/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.SieveTheory.SwitchingPrinciple
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiContinuousLowerFactorSecondInterval

/-!
# Suzuki's second lower interval and the Jurkat--Richert factor

This module isolates the analytic identification of Suzuki's source bracket on
`4 ≤ s ≤ 6` with the production Jurkat--Richert kernel.  The source amplitude
is kept symbolic; identifying it with the standard dimension-one factor is
explicitly conditional on `A = 2 * exp γ`.
-/

namespace MathlibNt.SieveTheory

open MeasureTheory intervalIntegral
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple

noncomputable section

/-- The bracket produced by Suzuki's delay equation on the second lower
interval, after separating its elementary and delayed terms. -/
noncomputable def suzukiLowerSecondIntervalSourceKernel (s : ℝ) : ℝ :=
  Real.log 3 +
    (∫ x in (4 : ℝ)..s, (x - 1)⁻¹) +
    ∫ x in (4 : ℝ)..s,
      SwitchingPrinciple.jurkatRichertInnerIntegral (x - 1) / (x - 1)

/-- Suzuki's second-interval source factor with an abstract amplitude `A`. -/
noncomputable def suzukiLowerSecondIntervalSourceFactor (A s : ℝ) : ℝ :=
  A / s * suzukiLowerSecondIntervalSourceKernel s

/-- Unconditional analytic bridge: evaluate the elementary primitive and
translate the delayed integral by `u = x - 1`. -/
theorem suzukiLowerSecondIntervalSourceKernel_eq_jurkatRichert
    {s : ℝ} (hs : 4 ≤ s) :
    suzukiLowerSecondIntervalSourceKernel s =
      Real.log (s - 1) +
        ∫ u in (3 : ℝ)..s - 1,
          SwitchingPrinciple.jurkatRichertInnerIntegral u / u := by
  have hlog : (∫ x in (4 : ℝ)..s, (x - 1)⁻¹) =
      Real.log (s - 1) - Real.log 3 := by
    have hderiv : ∀ x ∈ Set.uIcc (4 : ℝ) s,
        HasDerivAt (fun y : ℝ => Real.log (y - 1)) ((x - 1)⁻¹) x := by
      intro x hx
      rw [Set.uIcc_of_le hs] at hx
      simpa [one_div] using
        ((hasDerivAt_id x).sub_const 1).log
          (by linarith [hx.1] : x - 1 ≠ 0)
    have hint : IntervalIntegrable (fun x : ℝ => (x - 1)⁻¹) volume 4 s :=
      ((continuousOn_id.sub continuousOn_const).inv₀
        (fun x hx => by
          rw [Set.uIcc_of_le hs] at hx
          exact ne_of_gt (by linarith [hx.1] : 0 < x - 1))).intervalIntegrable
    have hraw := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    norm_num at hraw ⊢
    exact hraw
  have hshift :
      (∫ x in (4 : ℝ)..s,
          SwitchingPrinciple.jurkatRichertInnerIntegral (x - 1) / (x - 1)) =
        ∫ u in (3 : ℝ)..s - 1,
          SwitchingPrinciple.jurkatRichertInnerIntegral u / u := by
    convert intervalIntegral.integral_comp_sub_right
      (fun u : ℝ => SwitchingPrinciple.jurkatRichertInnerIntegral u / u)
      (a := (4 : ℝ)) (b := s) 1 using 1 <;> norm_num
  unfold suzukiLowerSecondIntervalSourceKernel
  rw [hlog, hshift]
  ring

/-- The literal nested bracket produced by the source module is the separated
source kernel used by the analytic bridge. -/
theorem suzukiLowerSecondIntervalNestedBracket_eq_sourceKernel
    {s : ℝ} (hs₄ : 4 ≤ s) (hs₆ : s ≤ 6) :
    Real.log 3 +
        (∫ x in (4 : ℝ)..s, (x - 1)⁻¹ *
          (1 + ∫ t in (2 : ℝ)..(x - 2), Real.log (t - 1) / t)) =
      suzukiLowerSecondIntervalSourceKernel s := by
  let J : ℝ → ℝ := fun y =>
    ∫ t in (2 : ℝ)..y, Real.log (t - 1) / t
  have hfcont : ContinuousOn (fun t : ℝ => Real.log (t - 1) / t)
      (Set.Icc (2 : ℝ) 4) := by
    apply (Real.continuousOn_log.comp
      (continuousOn_id.sub continuousOn_const) ?_).div continuousOn_id
    · intro t ht
      change t ≠ 0
      exact ne_of_gt (by linarith [ht.1] : 0 < t)
    · intro t ht
      change t - 1 ≠ 0
      exact ne_of_gt (by linarith [ht.1] : 0 < t - 1)
  have hfint : IntegrableOn (fun t : ℝ => Real.log (t - 1) / t)
      (Set.Icc (2 : ℝ) 4) volume :=
    hfcont.integrableOn_Icc
  have hJraw := intervalIntegral.continuousOn_primitive hfint
  have hJcont : ContinuousOn J (Set.Icc (2 : ℝ) 4) := by
    apply hJraw.congr
    intro y hy
    dsimp [J]
    exact intervalIntegral.integral_of_le hy.1
  have hshift : ContinuousOn (fun x : ℝ => J (x - 2))
      (Set.uIcc (4 : ℝ) s) := by
    apply hJcont.comp (continuousOn_id.sub continuousOn_const)
    intro x hx
    rw [Set.uIcc_of_le hs₄] at hx
    change x - 2 ∈ Set.Icc (2 : ℝ) 4
    exact ⟨by linarith [hx.1], by linarith [hx.2, hs₆]⟩
  have hinv : IntervalIntegrable (fun x : ℝ => (x - 1)⁻¹) volume 4 s := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_id.sub continuousOn_const).inv₀
    intro x hx
    rw [Set.uIcc_of_le hs₄] at hx
    exact ne_of_gt (by linarith [hx.1] : 0 < x - 1)
  have hdelayed : IntervalIntegrable
      (fun x : ℝ => SwitchingPrinciple.jurkatRichertInnerIntegral (x - 1) / (x - 1))
      volume 4 s := by
    have hcont : ContinuousOn (fun x : ℝ => J (x - 2) / (x - 1))
        (Set.uIcc (4 : ℝ) s) := by
      apply hshift.div (continuousOn_id.sub continuousOn_const)
      intro x hx
      rw [Set.uIcc_of_le hs₄] at hx
      simpa only [id_eq, Pi.sub_apply] using
        (ne_of_gt (by linarith [hx.1] : 0 < x - 1))
    apply ContinuousOn.intervalIntegrable
    apply hcont.congr
    intro x _hx
    unfold SwitchingPrinciple.jurkatRichertInnerIntegral
    dsimp [J]
    congr 2
    ring
  have hdecomp :
      (∫ x in (4 : ℝ)..s, (x - 1)⁻¹ *
          (1 + ∫ t in (2 : ℝ)..(x - 2), Real.log (t - 1) / t)) =
        (∫ x in (4 : ℝ)..s, (x - 1)⁻¹) +
          ∫ x in (4 : ℝ)..s,
            SwitchingPrinciple.jurkatRichertInnerIntegral (x - 1) / (x - 1) := by
    rw [← intervalIntegral.integral_add hinv hdelayed]
    apply intervalIntegral.integral_congr
    intro x _hx
    unfold SwitchingPrinciple.jurkatRichertInnerIntegral
    ring
  unfold suzukiLowerSecondIntervalSourceKernel
  rw [hdecomp]
  ring

/-- The actual production source formula, rather than a carried formula
contract, feeds the separated analytic source factor. -/
theorem suzukiContinuousLowerFactor_eq_secondIntervalSourceFactor
    {H : SwitchingPrinciple.SuzukiLemma144KappaOne.Section13HatLayers}
    (hH : SwitchingPrinciple.SuzukiLemma144KappaOne.Section13HatSourceContract H)
    {s : ℝ} (hs₄ : 4 ≤ s) (hs₆ : s ≤ 6) :
    suzukiContinuousLowerFactor s =
      suzukiLowerSecondIntervalSourceFactor suzukiLowerSieveAmplitude s := by
  rw [suzukiContinuousLowerFactor_eq_second_source_formula hH hs₄ hs₆]
  unfold suzukiLowerSecondIntervalSourceFactor
  rw [suzukiLowerSecondIntervalNestedBracket_eq_sourceKernel hs₄ hs₆]

/-- Conditional amplitude-normalization bridge from Suzuki's source factor to
the production dimension-one Jurkat--Richert lower factor. -/
theorem suzukiLowerSecondIntervalSourceFactor_eq_dimensionOne_conditional
    {A s : ℝ}
    (hA : A = 2 * Real.exp Real.eulerMascheroniConstant)
    (hs : 4 ≤ s) :
    suzukiLowerSecondIntervalSourceFactor A s =
      SwitchingPrinciple.dimensionOneLowerLinearSieveFactor s := by
  rw [suzukiLowerSecondIntervalSourceFactor,
    suzukiLowerSecondIntervalSourceKernel_eq_jurkatRichert hs, hA]
  rfl

/-- On the second lower interval, the genuine production source factor equals
the standard Jurkat--Richert factor, conditional only on amplitude
normalization. -/
theorem suzukiContinuousLowerFactor_eq_dimensionOne_conditional
    {H : SwitchingPrinciple.SuzukiLemma144KappaOne.Section13HatLayers}
    (hH : SwitchingPrinciple.SuzukiLemma144KappaOne.Section13HatSourceContract H)
    (hA : suzukiLowerSieveAmplitude =
      2 * Real.exp Real.eulerMascheroniConstant)
    {s : ℝ} (hs₄ : 4 ≤ s) (hs₆ : s ≤ 6) :
    suzukiContinuousLowerFactor s =
      SwitchingPrinciple.dimensionOneLowerLinearSieveFactor s := by
  rw [suzukiContinuousLowerFactor_eq_secondIntervalSourceFactor hH hs₄ hs₆]
  exact suzukiLowerSecondIntervalSourceFactor_eq_dimensionOne_conditional hA hs₄

end


end MathlibNt.SieveTheory
