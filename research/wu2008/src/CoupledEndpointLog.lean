import CoupledWeightedLower

namespace CoupledIntegralRecovery
open Real Set MeasureTheory NodeExtension ActualNineFeedback Wu2008DoubleSieve
open scoped Interval
noncomputable section

/-- The physical FTC coefficient is exactly the original endpoint logarithm. -/
theorem odds_J_endpoint {s S : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S) :
    odds S (jStart s S) (S-1) = log ((S-1)/(s-1)) := by
  have hs0 : s≠0 := by linarith
  have hs1 : s-1≠0 := by linarith
  have hS0 : S≠0 := by linarith
  have ha : jStart s S = S*(s-1)/s := by unfold jStart; field_simp
  have ha0 : 0<jStart s S := by rw [ha]; exact div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hd : S-jStart s S=S/s := by unfold jStart; ring
  unfold odds
  rw [← log_mul (div_ne_zero (by linarith : S-1≠0) ha0.ne')
    (div_ne_zero (by rw [hd]; exact div_ne_zero hS0 hs0) (by ring_nf; norm_num))]
  congr 1
  rw [ha]
  field_simp [hs0,hs1,hS0]
  ring

/-- Exact full weighted J, including the nonconstant original profile, at original log endpoints. -/
theorem profileJ_original_log (z : Fin 9 → ℝ) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5) (hsS : s ≤ S) (hr : 2 ≤ S-S/s) :
    profileJ z s S =
      gProfile (nineProfile z) (S-1)*log ((S-1)/(s-1))+
      ∫ t in (jStart s S)..(S-1), nineProfile z (t-1)/(t-1)*odds S (jStart s S) t := by
  rw [profileJ_eq_flat z hs hS hS5 hsS hr]
  unfold jFlat
  rw [odds_J_endpoint hs hS]

end
end CoupledIntegralRecovery
