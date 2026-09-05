/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma147ContinuousLowerFactor

/-!
# Suzuki's continuous lower factor on the second interval

The factors here are the genuine Proposition 11.8 source series.  The source
integral identities and the already proved first lower interval determine the
upper factor on `[3,5]` and then the lower factor on `[4,6]`.  Suzuki's source
amplitude remains symbolic throughout.
-/

namespace MathlibNt.SieveTheory

open MeasureTheory intervalIntegral Set
open scoped Interval BigOperators
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

noncomputable section

set_option autoImplicit false

/-- The genuine even source tail `T⁻`. -/
noncomputable def suzukiContinuousLowerTail (s : ℝ) : ℝ :=
  suzukiProposition118SourceTMinus s

/-- The continuous lower factor `F⁻ = 1 - T⁻`. -/
noncomputable def suzukiContinuousLowerFactor (s : ℝ) : ℝ :=
  1 - suzukiContinuousLowerTail s

/-- The continuous upper factor `F⁺ = 1 + T⁺`. -/
noncomputable def suzukiContinuousUpperFactor (s : ℝ) : ℝ :=
  1 + suzukiProposition118SourceTPlus s

/-- The source amplitude is the weighted upper factor at the first upper
endpoint. -/
theorem suzukiLowerSieveAmplitude_eq_three_mul_upperFactor :
    suzukiLowerSieveAmplitude = 3 * suzukiContinuousUpperFactor 3 := by
  rfl

/-- Translation of the first upper integral into the usual source/JR
coordinates. -/
private theorem upper_inner_shift {u : ℝ} :
    (∫ x in (3 : ℝ)..u, Real.log (x - 2) / (x - 1)) =
      ∫ t in (2 : ℝ)..(u - 1), Real.log (t - 1) / t := by
  let f : ℝ → ℝ := fun t => Real.log (t - 1) / t
  have h := intervalIntegral.integral_comp_sub_right (a := (3 : ℝ)) (b := u) f 1
  calc
    (∫ x in (3 : ℝ)..u, Real.log (x - 2) / (x - 1)) =
        ∫ x in (3 : ℝ)..u, f (x - 1) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp [f]
      congr 2 <;> ring
    _ = ∫ t in (2 : ℝ)..(u - 1), f t := by
      convert h using 1 <;> norm_num
    _ = ∫ t in (2 : ℝ)..(u - 1), Real.log (t - 1) / t := by rfl

/-- The production source identity and the first lower interval give the
explicit upper factor on `3 ≤ u ≤ 5`. -/
theorem suzukiContinuousUpperFactor_eq_second_source_formula
    {H : SwitchingPrinciple.SuzukiLemma144KappaOne.Section13HatLayers}
    (hH : SwitchingPrinciple.SuzukiLemma144KappaOne.Section13HatSourceContract H)
    {u : ℝ} (hu₃ : 3 ≤ u) (hu₅ : u ≤ 5) :
    suzukiContinuousUpperFactor u =
      suzukiLowerSieveAmplitude / u *
        (1 + ∫ t in (2 : ℝ)..(u - 1), Real.log (t - 1) / t) := by
  have hsource := suzukiProposition118SourceTPlus_weighted_sub hH
    (x := (3 : ℝ)) (y := u) (by norm_num) hu₃
  have hpoint : ∀ x ∈ Set.uIcc (3 : ℝ) u,
      suzukiProposition118SourceTMinus (x - 1) =
        1 - suzukiLowerSieveAmplitude * (Real.log (x - 2) / (x - 1)) := by
    rw [Set.uIcc_of_le hu₃]
    intro x hx
    have hx₂ : 2 ≤ x - 1 := by linarith [hx.1]
    have hx₄ : x - 1 ≤ 4 := by linarith [hx.2, hu₅]
    have hid := one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
      hH hx₂ hx₄
    rw [suzukiLowerSieveFactorFirstInterval_eq_log hx₂ hx₄] at hid
    calc
      suzukiProposition118SourceTMinus (x - 1) =
          1 - (1 - suzukiProposition118SourceTMinus (x - 1)) := by ring
      _ = 1 - suzukiLowerSieveAmplitude * Real.log (x - 1 - 1) / (x - 1) := by
        rw [hid]
      _ = 1 - suzukiLowerSieveAmplitude * (Real.log (x - 2) / (x - 1)) := by ring_nf
  rw [intervalIntegral.integral_congr hpoint] at hsource
  have hratio : IntervalIntegrable
      (fun x : ℝ => Real.log (x - 2) / (x - 1)) volume 3 u := by
    apply ContinuousOn.intervalIntegrable
    apply (Real.continuousOn_log.comp
      (continuousOn_id.sub continuousOn_const) ?_).div
      (continuousOn_id.sub continuousOn_const)
    · intro x hx
      rw [Set.uIcc_of_le hu₃] at hx
      change x - 1 ≠ 0
      exact ne_of_gt (by linarith [hx.1] : 0 < x - 1)
    · intro x hx
      rw [Set.uIcc_of_le hu₃] at hx
      change x - 2 ≠ 0
      exact ne_of_gt (by linarith [hx.1] : 0 < x - 2)
  have hone : IntervalIntegrable (fun _x : ℝ => (1 : ℝ)) volume 3 u :=
    continuousOn_const.intervalIntegrable
  rw [intervalIntegral.integral_sub hone
    (hratio.const_mul suzukiLowerSieveAmplitude),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hsource
  rw [upper_inner_shift] at hsource
  have hbase : 3 * suzukiProposition118SourceTPlus 3 =
      suzukiLowerSieveAmplitude - 3 := by
    exact mul_suzukiProposition118SourceTPlus_eq_amplitude_sub hH
      (s := (3 : ℝ)) (by norm_num) (by norm_num)
  have hu0 : u ≠ 0 := by linarith
  unfold suzukiContinuousUpperFactor
  field_simp
  change (1 + suzukiProposition118SourceTPlus u) * u = _
  simp only [smul_eq_mul, mul_one] at hsource
  ring_nf at hsource hbase ⊢
  nlinarith [hsource, hbase]

/-- Suzuki's explicit second lower interval, with the genuine source amplitude
kept symbolic. -/
theorem suzukiContinuousLowerFactor_eq_second_source_formula
    {H : SwitchingPrinciple.SuzukiLemma144KappaOne.Section13HatLayers}
    (hH : SwitchingPrinciple.SuzukiLemma144KappaOne.Section13HatSourceContract H)
    {s : ℝ} (hs₄ : 4 ≤ s) (hs₆ : s ≤ 6) :
    suzukiContinuousLowerFactor s =
      suzukiLowerSieveAmplitude / s *
        (Real.log 3 +
          ∫ x in (4 : ℝ)..s, (x - 1)⁻¹ *
            (1 + ∫ t in (2 : ℝ)..(x - 2), Real.log (t - 1) / t)) := by
  have hsource := suzukiProposition118SourceTMinus_weighted_sub hH
    (x := (4 : ℝ)) (y := s) (by norm_num) hs₄
  let J : ℝ → ℝ := fun y =>
    ∫ t in (2 : ℝ)..y, Real.log (t - 1) / t
  let g : ℝ → ℝ := fun x =>
    (x - 1)⁻¹ * (1 + J (x - 2))
  have hpoint : ∀ x ∈ Set.uIcc (4 : ℝ) s,
      suzukiProposition118SourceTPlus (x - 1) =
        suzukiLowerSieveAmplitude * g x - 1 := by
    rw [Set.uIcc_of_le hs₄]
    intro x hx
    have hu := suzukiContinuousUpperFactor_eq_second_source_formula hH
      (u := x - 1) (by linarith [hx.1]) (by linarith [hx.2, hs₆])
    unfold suzukiContinuousUpperFactor at hu
    dsimp [g, J]
    have hx1 : x - 1 ≠ 0 := by linarith [hx.1]
    field_simp at hu ⊢
    change (x - 1) * suzukiProposition118SourceTPlus (x - 1) = _
    calc
      (x - 1) * suzukiProposition118SourceTPlus (x - 1) =
          (x - 1) * (1 + suzukiProposition118SourceTPlus (x - 1)) - (x - 1) := by
        ring
      _ = suzukiLowerSieveAmplitude *
          (1 + ∫ t in (2 : ℝ)..(x - 2), Real.log (t - 1) / t) - (x - 1) := by
        convert congrArg (fun z : ℝ => z - (x - 1)) hu using 1 <;> ring_nf
  rw [intervalIntegral.integral_congr hpoint] at hsource
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
  have hshift : ContinuousOn (fun x : ℝ => J (x - 2)) (Set.uIcc (4 : ℝ) s) := by
    apply hJcont.comp (continuousOn_id.sub continuousOn_const)
    intro x hx
    rw [Set.uIcc_of_le hs₄] at hx
    change x - 2 ∈ Set.Icc (2 : ℝ) 4
    exact ⟨by linarith [hx.1], by linarith [hx.2, hs₆]⟩
  have hgcont : ContinuousOn g (Set.uIcc (4 : ℝ) s) := by
    dsimp [g]
    apply ((continuousOn_id.sub continuousOn_const).inv₀ ?_).mul
      (continuousOn_const.add hshift)
    intro x hx
    rw [Set.uIcc_of_le hs₄] at hx
    simpa only [id_eq, Pi.sub_apply] using
      (ne_of_gt (by linarith [hx.1] : 0 < x - 1))
  have hgint : IntervalIntegrable g volume 4 s := hgcont.intervalIntegrable
  have hone : IntervalIntegrable (fun _x : ℝ => (1 : ℝ)) volume 4 s :=
    continuousOn_const.intervalIntegrable
  rw [intervalIntegral.integral_sub
    (hgint.const_mul suzukiLowerSieveAmplitude) hone,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hsource
  have hbaseId := one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
    hH (s := (4 : ℝ)) (by norm_num) (by norm_num)
  rw [suzukiLowerSieveFactorFirstInterval_eq_log (by norm_num) (by norm_num)] at hbaseId
  have hs0 : s ≠ 0 := by linarith
  have hsmul : (s - 4) • (1 : ℝ) = s - 4 := by
    simp
  rw [hsmul] at hsource
  have hweighted :
      s * (1 - suzukiProposition118SourceTMinus s) =
        suzukiLowerSieveAmplitude *
          (Real.log 3 + ∫ x in (4 : ℝ)..s, g x) := by
    nlinarith [hsource, hbaseId]
  calc
    suzukiContinuousLowerFactor s =
        (s * (1 - suzukiProposition118SourceTMinus s)) / s := by
      rw [suzukiContinuousLowerFactor, suzukiContinuousLowerTail]
      field_simp
    _ = suzukiLowerSieveAmplitude / s *
        (Real.log 3 +
          ∫ x in (4 : ℝ)..s, (x - 1)⁻¹ *
            (1 + ∫ t in (2 : ℝ)..(x - 2), Real.log (t - 1) / t)) := by
      rw [hweighted]
      dsimp [g, J]
      ring

end


end MathlibNt.SieveTheory
