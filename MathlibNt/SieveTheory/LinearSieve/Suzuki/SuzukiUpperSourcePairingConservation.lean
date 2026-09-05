/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiStandardUpperAdjointScaledTail
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiIntegralDDEPairing

/-!
# Unconditional upper-source pairing conservation route

This module separates the two genuine analytic producers still missing from the
upper source construction: its forward integral DDE and its tail `P(s) → 2`.
It proves the Iwaniec pairing is constant on `[2,∞)` from the integral DDE and
the standard-adjoint DDE, without using Proposition 11.8(iii).
-/

namespace MathlibNt.SieveTheory

open Filter Topology MeasureTheory intervalIntegral Set
open scoped Interval

noncomputable section

/-- Exact forward integral DDE required of the already-defined genuine upper
source.  This is an independently producible source-series theorem. -/
def SuzukiUpperSourcePIntegralDDE : Prop :=
  ContinuousOn suzukiUpperSourceP (Ici (1 : ℝ)) ∧
    ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      b * suzukiUpperSourceP b - a * suzukiUpperSourceP a =
        ∫ t in a..b, suzukiUpperSourceP (t - 1)

/-- Exact, independent tail target for the genuine upper source. -/
def SuzukiUpperSourcePTail : Prop :=
  Tendsto suzukiUpperSourceP atTop (nhds 2)

/-- The differential identity required from the Laplace-integral standard
adjoint.  It does not include any pairing normalization. -/
def SuzukiStandardUpperAdjointDDE : Prop :=
  ∀ s : ℝ, 2 ≤ s →
    HasDerivAt suzukiStandardUpperAdjoint
      (-suzukiStandardUpperAdjoint (s + 1) / s) s


/-- The residual moving-window estimate.  It is isolated from both the source
DDE and Proposition 11.8; analytically it follows from the two pointwise tails
and local continuity. -/
def SuzukiUpperSourcePairingWindowTail : Prop :=
  Tendsto (fun s : ℝ =>
    ∫ t in (s - 1)..s,
      suzukiStandardUpperAdjoint (t + 1) * suzukiUpperSourceP t)
    atTop (nhds 0)

/-- The same pairing formula with the source exposed as an argument. -/
noncomputable def upperSourcePairingFor (P p : ℝ → ℝ) (s : ℝ) : ℝ :=
  s * p s * P s + ∫ t in (s - 1)..s, p (t + 1) * P t

/-- Pairing conservation from a forward integral DDE.  The one-sided derivative
at `2` is extracted from the integral equation, so no derivative of `P` is
assumed at the switching point. -/
theorem upperSourcePairing_eq_of_integralDDE
    {P p : ℝ → ℝ}
    (hP : ContinuousOn P (Ici (1 : ℝ)))
    (hDDE : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      b * P b - a * P a = ∫ t in a..b, P (t - 1))
    (hp : ∀ s : ℝ, 2 ≤ s → HasDerivAt p (-p (s + 1) / s) s)
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    upperSourcePairingFor P p y = upperSourcePairingFor P p x := by
  let F : ℝ → ℝ := fun s => s * P s
  let g : ℝ → ℝ := fun t => p (t + 1) * P t
  let G : ℝ → ℝ := fun u => ∫ t in (1 : ℝ)..u, g t
  have hP_Icc (a b : ℝ) (ha : 1 ≤ a) : ContinuousOn P (Icc a b) :=
    hP.mono (fun t ht => ha.trans ht.1)
  have hpOn : ContinuousOn p (Ici (2 : ℝ)) := by
    intro s hs
    exact (hp s hs).continuousAt.continuousWithinAt
  have hgOn : ContinuousOn g (Ici (1 : ℝ)) := by
    apply ContinuousOn.mul
    · exact hpOn.comp (continuousOn_id.add continuousOn_const) (by
        intro t ht
        simp only [mem_Ici] at ht ⊢
        linarith)
    · exact hP
  have hF_right (z : ℝ) (hz : 2 ≤ z) :
      HasDerivWithinAt F (P (z - 1)) (Ici z) z := by
    have hshift : ContinuousWithinAt (fun t => P (t - 1)) (Ioi z) z := by
      have hc : ContinuousOn (fun t => P (t - 1)) (Ici z) :=
        hP.comp (continuousOn_id.sub continuousOn_const) (by
          intro t ht
          simp only [mem_Ici] at ht ⊢
          linarith)
      exact (hc z (by simp)).mono Ioi_subset_Ici_self
    have hint : IntervalIntegrable (fun t => P (t - 1)) volume z z := by
      have hc : ContinuousOn (fun t => P (t - 1)) (uIcc z z) := by
        apply hP.comp (continuousOn_id.sub continuousOn_const)
        intro t ht
        simp only [uIcc_self, mem_singleton_iff] at ht
        subst t
        simp only [Pi.sub_apply, id_eq, mem_Ici]
        linarith
      exact hc.intervalIntegrable
    have hInt : HasDerivWithinAt
        (fun u => ∫ t in z..u, P (t - 1)) (P (z - 1)) (Ici z) z :=
      intervalIntegral.integral_hasDerivWithinAt_right hint
        ((hP.comp (continuousOn_id.sub continuousOn_const) (by
          intro t ht
          simp only [mem_Ioi] at ht
          simp only [Pi.sub_apply, id_eq, mem_Ici]
          linarith)).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi z)
        hshift
    have hmodel := (hasDerivWithinAt_const (x := z) (c := F z) (s := Ici z)).add hInt
    rw [zero_add] at hmodel
    apply hmodel.congr
    · intro u hu
      have hd := hDDE z u hz hu
      dsimp only [F]
      change u * P u = z * P z + ∫ t in z..u, P (t - 1)
      rw [← hd]
      ring
    · simp
  have hG_right (z : ℝ) (hz : 1 ≤ z) :
      HasDerivWithinAt G (g z) (Ici z) z := by
    have hgz : ContinuousOn g (Ici z) := hgOn.mono (by
      intro t ht
      simp only [mem_Ici] at ht ⊢
      linarith)
    have hint : IntervalIntegrable g volume 1 z :=
      (hgOn.mono (by
        intro t ht
        rw [uIcc_of_le hz] at ht
        exact ht.1)).intervalIntegrable
    exact intervalIntegral.integral_hasDerivWithinAt_right hint
      ((hgz.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin
        measurableSet_Ioi z)
      ((hgz z (by simp)).mono Ioi_subset_Ici_self)
  have hpair_right (z : ℝ) (hz : 2 ≤ z) :
      HasDerivWithinAt (upperSourcePairingFor P p) 0 (Ici z) z := by
    have hpz : HasDerivWithinAt p (-p (z + 1) / z) (Ici z) z :=
      (hp z hz).hasDerivWithinAt
    have hfirst := hpz.mul (hF_right z hz)
    have hGz := hG_right z (by linarith)
    have hshift : HasDerivWithinAt (fun s : ℝ => s - 1) 1 (Ici z) z :=
      (hasDerivAt_id z).sub_const 1 |>.hasDerivWithinAt
    have hGshift0 := (hG_right (z - 1) (by linarith)).comp z hshift (by
      intro s hs
      simp only [mem_Ici] at hs ⊢
      linarith)
    rw [mul_one] at hGshift0
    change HasDerivWithinAt (fun s => G (s - 1)) (g (z - 1)) (Ici z) z at hGshift0
    have hwindow := hGz.sub hGshift0
    have hwindow_eq : ∀ s ∈ Ici z,
        G s - G (s - 1) = ∫ t in (s - 1)..s, g t := by
      intro s hs
      have hs2 : 2 ≤ s := hz.trans hs
      dsimp only [G]
      have h1 : IntervalIntegrable g volume 1 (s - 1) :=
        (hgOn.mono (by
          intro t ht
          rw [uIcc_of_le (by linarith [hs2] : (1 : ℝ) ≤ s - 1)] at ht
          exact ht.1)).intervalIntegrable
      have h2 : IntervalIntegrable g volume (s - 1) s :=
        (hgOn.mono (by
          intro t ht
          rw [uIcc_of_le (by linarith : s - 1 ≤ s)] at ht
          exact (show (1 : ℝ) ≤ t by linarith [hs2, ht.1]))).intervalIntegrable
      have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
      linarith
    have hwindow' := hwindow.congr
      (fun s hs => (hwindow_eq s hs).symm) (hwindow_eq z (by simp)).symm
    have hraw := hfirst.add hwindow'
    have hz0 : z ≠ 0 := by linarith
    have hzero :
        (-p (z + 1) / z) * F z + p z * P (z - 1) +
          (g z - g (z - 1)) = 0 := by
      dsimp only [F, g]
      field_simp
      ring
    have hout := hraw.congr_deriv hzero
    apply hout.congr
    · intro s hs
      unfold upperSourcePairingFor
      dsimp only [F, g]
      simp only [Pi.add_apply, Pi.mul_apply]
      ring
    · unfold upperSourcePairingFor
      dsimp only [F, g]
      simp only [Pi.add_apply, Pi.mul_apply]
      ring
  have hpair_cont : ContinuousOn (upperSourcePairingFor P p) (Icc x y) := by
    have hpI : ContinuousOn p (Icc x y) := hpOn.mono (by
      intro s hs
      exact hx.trans hs.1)
    have hPI : ContinuousOn P (Icc x y) := hP_Icc x y (by linarith)
    have hfirst : ContinuousOn (fun s => p s * (s * P s)) (Icc x y) :=
      hpI.mul (continuousOn_id.mul hPI)
    have hGI : ContinuousOn G (Icc (1 : ℝ) y) := by
      have hint : IntervalIntegrable g volume 1 y :=
        (hgOn.mono (by
          intro t ht
          rw [uIcc_of_le (by linarith : (1 : ℝ) ≤ y)] at ht
          exact ht.1)).intervalIntegrable
      simpa only [G, uIcc_of_le (show (1 : ℝ) ≤ y by linarith)] using
        (intervalIntegral.continuousOn_primitive_interval'
          (a := (1 : ℝ)) (b₁ := (1 : ℝ)) (b₂ := y) hint left_mem_uIcc)
    have hGs : ContinuousOn G (Icc x y) := hGI.mono (by
      intro s hs
      exact ⟨by linarith [hx, hs.1], hs.2⟩)
    have hGshift : ContinuousOn (fun s => G (s - 1)) (Icc x y) :=
      hGI.comp (continuousOn_id.sub continuousOn_const) (by
        intro s hs
        exact ⟨by linarith [hx, hs.1], by linarith [hs.2]⟩)
    have hsum := hfirst.add (hGs.sub hGshift)
    apply hsum.congr
    intro s hs
    have hs2 : 2 ≤ s := hx.trans hs.1
    unfold upperSourcePairingFor
    rw [show s * p s * P s = p s * (s * P s) by ring]
    have h1 : IntervalIntegrable g volume 1 (s - 1) :=
      (hgOn.mono (by
        intro t ht
        rw [uIcc_of_le (by linarith [hs2] : (1 : ℝ) ≤ s - 1)] at ht
        exact ht.1)).intervalIntegrable
    have h2 : IntervalIntegrable g volume (s - 1) s :=
      (hgOn.mono (by
        intro t ht
        rw [uIcc_of_le (by linarith : s - 1 ≤ s)] at ht
        exact (show (1 : ℝ) ≤ t by linarith [hs2, ht.1]))).intervalIntegrable
    have hw := intervalIntegral.integral_add_adjacent_intervals h1 h2
    have hw' : (∫ t in (s - 1)..s, g t) = G s - G (s - 1) := by
      dsimp only [G]
      linarith
    change p s * (s * P s) + (∫ t in (s - 1)..s, g t) =
      p s * (s * P s) + (G s - G (s - 1))
    rw [hw']
  have hconst := constant_of_has_deriv_right_zero hpair_cont (fun z hz =>
    hpair_right z (hx.trans hz.1))
  exact hconst y ⟨hxy, le_rfl⟩

@[simp] theorem upperSourcePairingFor_actual (p : ℝ → ℝ) (s : ℝ) :
    upperSourcePairingFor suzukiUpperSourceP p s =
      suzukiUpperSourcePairing p s := rfl

/-- Production conservation theorem for the genuine upper source and genuine
standard adjoint. -/
theorem suzukiUpperSourcePairing_eq_of_productionDDE
    (hP : SuzukiUpperSourcePIntegralDDE)
    (hp : SuzukiStandardUpperAdjointDDE)
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    suzukiUpperSourcePairing suzukiStandardUpperAdjoint y =
      suzukiUpperSourcePairing suzukiStandardUpperAdjoint x := by
  rcases hP with ⟨hcont, hDDE⟩
  simpa only [upperSourcePairingFor_actual] using
    upperSourcePairing_eq_of_integralDDE hcont hDDE hp hx hxy

/-- The upper pairing tends to `2` from the genuine source tail, the elementary
scaled Laplace tail, and the residual unit-window estimate. -/
theorem tendsto_suzukiUpperSourcePairing_two
    (hP : SuzukiUpperSourcePTail)
    (hp : SuzukiStandardUpperAdjointScaledTail)
    (hwindow : SuzukiUpperSourcePairingWindowTail) :
    Tendsto (suzukiUpperSourcePairing suzukiStandardUpperAdjoint)
      atTop (nhds 2) := by
  have hfirst : Tendsto (fun s : ℝ =>
      s * suzukiStandardUpperAdjoint s * suzukiUpperSourceP s)
      atTop (nhds 2) := by
    have hmul := hp.mul hP
    simpa only [one_mul] using hmul
  change Tendsto (fun s : ℝ =>
    s * suzukiStandardUpperAdjoint s * suzukiUpperSourceP s +
      ∫ t in (s - 1)..s,
        suzukiStandardUpperAdjoint (t + 1) * suzukiUpperSourceP t)
    atTop (nhds 2)
  simpa only [add_zero] using hfirst.add hwindow

/-- No invocation of Proposition 11.8(iii): conservation transports the
independently computed value at infinity back to every finite `s ≥ 2`. -/
theorem suzukiUpperSourcePairing_eq_two
    (hDDE : SuzukiUpperSourcePIntegralDDE)
    (hpDDE : SuzukiStandardUpperAdjointDDE)
    (hPtail : SuzukiUpperSourcePTail)
    (hptail : SuzukiStandardUpperAdjointScaledTail)
    (hwindow : SuzukiUpperSourcePairingWindowTail)
    {s : ℝ} (hs : 2 ≤ s) :
    suzukiUpperSourcePairing suzukiStandardUpperAdjoint s = 2 := by
  let B := suzukiUpperSourcePairing suzukiStandardUpperAdjoint
  have hlim : Tendsto B atTop (nhds 2) :=
    tendsto_suzukiUpperSourcePairing_two hPtail hptail hwindow
  have hevent : ∀ᶠ x : ℝ in atTop, B x = B 2 := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    exact suzukiUpperSourcePairing_eq_of_productionDDE hDDE hpDDE
      (x := (2 : ℝ)) (y := x) (by norm_num) hx
  have hconst : Tendsto B atTop (nhds (B 2)) :=
    tendsto_const_nhds.congr' (hevent.mono fun _ h => h.symm)
  have hbase : B 2 = 2 := tendsto_nhds_unique hconst hlim
  rw [suzukiUpperSourcePairing_eq_of_productionDDE hDDE hpDDE
    (x := (2 : ℝ)) (y := s) (by norm_num) hs]
  exact hbase


end

end MathlibNt.SieveTheory
