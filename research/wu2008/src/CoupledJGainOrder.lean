import CoupledJErrorRows

namespace CoupledJLogRecovery
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open CoupledIntegralRecovery FiniteEndpointPayment FirstErrorFullPayment
open scoped Interval BigOperators
noncomputable section

theorem firstError_nonneg {A u : ℝ} (hA : 2 ≤ A) (hu : A-1 ≤ u) :
    0 ≤ errorDensity (A+1) u := by
  have hx0 : 0 < (u+1)/(A+1-1) := div_pos (by linarith) (by linarith)
  have hx : 1 ≤ (u+1)/(A+1-1) := (one_le_div (by linarith)).mpr (by linarith)
  have hu0 : 0 ≤ u := by linarith
  unfold errorDensity
  rw [OriginalFirstErrorRecovery.envelope_gap hx0]
  have : 0 ≤ (u+1)/(A+1-1)-1 := sub_nonneg.mpr hx
  positivity

theorem primitive_gain_nonneg {S A a b : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S-1)
    (ha : A-1 ≤ a) (hab : a ≤ b) (hb : b ≤ S-2) :
    0 ≤ (errorPrimitive (A+1) b-errorPrimitive (A+1) a)+
      (secondPrimitive S A b-secondPrimitive S A a) := by
  rw [← error_integral (by linarith : 3 ≤ A+1) (by linarith : 0<a) hab,
    ← second_integral hA hAS ha hab hb]
  apply add_nonneg
  · apply intervalIntegral.integral_nonneg hab
    intro u hu
    exact firstError_nonneg hA (ha.trans hu.1)
  · apply intervalIntegral.integral_nonneg hab
    intro u hu
    exact secondError_nonneg hA hAS ⟨ha.trans hu.1,hu.2.trans hb⟩

theorem jRecovery_nonneg {z : Fin 9 → ℝ} (hz : ∀ k,0 ≤ z k) {s S : ℝ}
    (hA : 2 ≤ jStart s S) (hAS : jStart s S ≤ S-1) :
    0 ≤ jRecovery z s S := by
  unfold jRecovery
  apply Finset.sum_nonneg
  intro k _
  have hab : jStart s S-1 ≤ S-2 := by linarith
  exact mul_nonneg (hz k)
    (primitive_gain_nonneg hA hAS (clip_bounds hab).1 (cell_order _ _ k) (clip_bounds hab).2)

theorem original_jRecoveries_nonneg (i : Fin 4) :
    0 ≤ jRecovery NineFeedbackStrength.originalH (coupledRow i).s (coupledRow i).S ∧
    0 ≤ jRecovery NineFeedbackStrength.originalH (coupledRow i).kappa2 (coupledRow i).S ∧
    0 ≤ jRecovery NineFeedbackStrength.originalH (coupledRow i).kappa3 (coupledRow i).S := by
  have hp := coupledRow_geometry i
  have hg := coupled_geometry_bounds hp
  have hend {s S : ℝ} (hs : 2 ≤ s) (hsS : s ≤ S) : jStart s S ≤ S-1 := by
    have h := (one_le_div (by linarith : 0<s)).mpr hsS
    unfold jStart
    linarith
  exact ⟨jRecovery_nonneg originalH_nonneg hp.2.2.1 (hend hg.1 hg.2.1),
    jRecovery_nonneg originalH_nonneg hp.2.2.2.1 (hend hg.2.2.1 hg.2.2.2.1),
    jRecovery_nonneg originalH_nonneg hp.2.2.2.2 (hend hg.2.2.2.2.1 hg.2.2.2.2.2.1)⟩

theorem parent_le_cubicLower (i : Fin 4) : CoupledCorrectedE.lower (coupledRow i) ≤
    cubicLower (coupledRow i) := by
  rw [exact_replacement]
  obtain ⟨h0,h2,h3⟩ := original_jRecoveries_nonneg i
  linarith only [h0,h2,h3]

end
end CoupledJLogRecovery
