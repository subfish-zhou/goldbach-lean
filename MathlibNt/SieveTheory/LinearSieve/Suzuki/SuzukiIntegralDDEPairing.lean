/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Pairing conservation directly from an integral delay equation

This module avoids differentiating the source function at the left endpoint.
The integral DDE itself supplies the required right derivative, including at
`x = 2`, where only right continuity of the delayed value at `1` is used.
-/

namespace MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers

open Filter Topology MeasureTheory intervalIntegral Set
open scoped Interval

noncomputable section

/-- The κ=1 Iwaniec pairing in weighted coordinates `F(s) = s Q(s)`. -/
noncomputable def sourceWeightedPairing (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  (s - 1) * F s - ∫ t in (s - 1)..s, F t

/-- An integral delay equation conserves the κ=1 Iwaniec pairing.  Crucially,
`F` is assumed continuous only on `[1,∞)`, and the equation is used only in
forward form on `[2,∞)`.  Thus the theorem includes `x = 2` without any
left-continuity hypothesis at the threshold. -/
theorem sourceWeightedPairing_eq_of_integralDDE
    {F : ℝ → ℝ} (hF : ContinuousOn F (Ici (1 : ℝ)))
    (hDDE : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      F b - F a = -∫ t in a..b, F (t - 1) / (t - 1))
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    sourceWeightedPairing F y = sourceWeightedPairing F x := by
  let H : ℝ → ℝ := fun t => F (t - 1) / (t - 1)
  let A : ℝ → ℝ := fun u => ∫ t in (1 : ℝ)..u, F t
  have hF_Icc (a b : ℝ) (ha : 1 ≤ a) : ContinuousOn F (Icc a b) :=
    hF.mono (fun t ht => by exact ha.trans ht.1)
  have hH_Ici (z : ℝ) (hz : 2 ≤ z) : ContinuousOn H (Ici z) := by
    apply ContinuousOn.div
    · exact hF.comp (continuousOn_id.sub continuousOn_const) (by
        intro t ht
        simp only [mem_Ici] at ht ⊢
        linarith)
    · exact continuousOn_id.sub continuousOn_const
    · intro t ht
      simp only [mem_Ici] at ht
      linarith
  have hA_right (z : ℝ) (hz : 1 ≤ z) :
      HasDerivWithinAt A (F z) (Ici z) z := by
    have : Fact (z ∈ Ici z) := ⟨by simp⟩
    have hFz : ContinuousOn F (Ici z) := hF.mono (by
      intro t ht
      simp only [mem_Ici] at ht ⊢
      linarith)
    have hcont : ContinuousWithinAt F (Ioi z) z :=
      (hFz z (by simp)).mono Ioi_subset_Ici_self
    have hint : IntervalIntegrable F volume 1 z :=
      (hF_Icc 1 z (by norm_num)).intervalIntegrable_of_Icc hz
    exact intervalIntegral.integral_hasDerivWithinAt_right hint
      ((hFz.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin
        measurableSet_Ioi z) hcont
  have hA_cont_Icc : ContinuousOn A (Icc (1 : ℝ) y) := by
    have hint : IntervalIntegrable F volume 1 y :=
      (hF_Icc 1 y (by norm_num)).intervalIntegrable_of_Icc (by linarith)
    simpa only [A, uIcc_of_le (show (1 : ℝ) ≤ y by linarith)] using
      (intervalIntegral.continuousOn_primitive_interval'
        (a := (1 : ℝ)) (b₁ := (1 : ℝ)) (b₂ := y) hint left_mem_uIcc)
  have hF_right (z : ℝ) (hz : 2 ≤ z) :
      HasDerivWithinAt F (-H z) (Ici z) z := by
    have hHz : ContinuousWithinAt H (Ioi z) z :=
      (hH_Ici z hz z (by simp)).mono Ioi_subset_Ici_self
    have hint : IntervalIntegrable H volume z z :=
      ((hH_Ici z hz).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc le_rfl
    have hInt : HasDerivWithinAt (fun u => ∫ t in z..u, H t) (H z) (Ici z) z :=
      intervalIntegral.integral_hasDerivWithinAt_right hint
        (((hH_Ici z hz).mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin
          measurableSet_Ioi z) hHz
    have hmodel :=
      (hasDerivWithinAt_const (x := z) (c := F z) (s := Ici z)).sub hInt
    rw [zero_sub] at hmodel
    apply hmodel.congr
    · intro u hu
      have hd := hDDE z u hz hu
      dsimp [H] at hd ⊢
      linarith
    · simp
  have hpair_right (z : ℝ) (hz : 2 ≤ z) :
      HasDerivWithinAt (sourceWeightedPairing F) 0 (Ici z) z := by
    have hlin : HasDerivWithinAt (fun s : ℝ => s - 1) 1 (Ici z) z :=
      (hasDerivAt_id z).sub_const 1 |>.hasDerivWithinAt
    have hfirst := hlin.mul (hF_right z hz)
    have hAz := hA_right z (by linarith)
    have hshift : HasDerivWithinAt (fun s : ℝ => s - 1) 1 (Ici z) z :=
      (hasDerivAt_id z).sub_const 1 |>.hasDerivWithinAt
    have hAshift_base := hA_right (z - 1) (by linarith)
    have hAshift0 := hAshift_base.comp z hshift (by
        intro s hs
        simp only [mem_Ici] at hs ⊢
        linarith)
    rw [mul_one] at hAshift0
    change HasDerivWithinAt (fun s => A (s - 1)) (F (z - 1)) (Ici z) z at hAshift0
    have hAshift := hAshift0
    have hwindow : HasDerivWithinAt (fun s => A s - A (s - 1))
        (F z - F (z - 1)) (Ici z) z := hAz.sub hAshift
    have hwindow_eq : ∀ s ∈ Ici z,
        A s - A (s - 1) = ∫ t in (s - 1)..s, F t := by
      intro s hs
      dsimp [A]
      have hs2 : 2 ≤ s := hz.trans hs
      have h1 : IntervalIntegrable F volume 1 (s - 1) :=
        (hF_Icc 1 (s - 1) (by norm_num)).intervalIntegrable_of_Icc (by linarith)
      have h2 : IntervalIntegrable F volume (s - 1) s :=
        (hF_Icc (s - 1) s (by linarith)).intervalIntegrable_of_Icc (by linarith)
      have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
      linarith
    have hwindow' := hwindow.congr
      (fun s hs => (hwindow_eq s hs).symm) (hwindow_eq z (by simp)).symm
    have hraw := hfirst.sub hwindow'
    have hz1 : z - 1 ≠ 0 := by linarith
    have hcoef : 1 * F z + (z - 1) * -H z - (F z - F (z - 1)) = 0 := by
      dsimp [H]
      field_simp
      ring
    have hout := hraw.congr_deriv hcoef
    exact hout.congr (fun _ _ => rfl) rfl
  have hpair_cont : ContinuousOn (sourceWeightedPairing F) (Icc x y) := by
    let P : ℝ → ℝ := fun s => (s - 1) * F s - (A s - A (s - 1))
    have hFx : ContinuousOn F (Icc x y) := hF.mono (by
      intro s hs
      simp only [mem_Ici]
      linarith [hx, hs.1])
    have hAs : ContinuousOn A (Icc x y) := hA_cont_Icc.mono (by
      intro s hs
      exact ⟨by linarith [hx, hs.1], hs.2⟩)
    have hAsh : ContinuousOn (fun s => A (s - 1)) (Icc x y) :=
      hA_cont_Icc.comp (continuousOn_id.sub continuousOn_const) (by
        intro s hs
        exact ⟨by linarith [hx, hs.1], by linarith [hs.2]⟩)
    have hP : ContinuousOn P (Icc x y) :=
      ((continuousOn_id.sub continuousOn_const).mul hFx).sub (hAs.sub hAsh)
    apply hP.congr
    intro s hs
    unfold P sourceWeightedPairing
    have hs2 : 2 ≤ s := hx.trans hs.1
    have h1 : IntervalIntegrable F volume 1 (s - 1) :=
      (hF_Icc 1 (s - 1) (by norm_num)).intervalIntegrable_of_Icc (by linarith)
    have h2 : IntervalIntegrable F volume (s - 1) s :=
      (hF_Icc (s - 1) s (by linarith)).intervalIntegrable_of_Icc (by linarith)
    have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
    dsimp [A]
    linarith
  have hconst := constant_of_has_deriv_right_zero hpair_cont (fun z hz =>
    hpair_right z (hx.trans hz.1))
  exact hconst y ⟨hxy, le_rfl⟩

end
end MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
