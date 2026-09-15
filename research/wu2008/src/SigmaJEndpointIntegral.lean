import SigmaJEndpointKernel

namespace SigmaJEndpoint
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open CoupledIntegralRecovery FiniteEndpointPayment FirstErrorFullPayment
open scoped Interval BigOperators
noncomputable section

def endpointPrimitive (S A u : ℝ) : ℝ :=
  jPrimitive S A u+firstScale S A*errorPrimitive (A+1) u+
    secondScale S A*CoupledJLogRecovery.secondPrimitive S A u

theorem endpointKernel_continuous {S A a b : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S-1)
    (ha : A-1 ≤ a) (hab : a ≤ b) (hb : b ≤ S-2) :
    ContinuousOn (endpointKernel S A) (uIcc a b) := by
  exact ((jKernel_continuous hA hAS ha hab hb).add
    ((errorDensity_continuous (by linarith : 3 ≤ A+1) (by linarith : 0 < a) hab).const_mul _)).add
    ((CoupledJLogRecovery.secondError_continuous hA hAS ha hab hb).const_mul _)

theorem endpointKernel_integral {S A a b : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S-1)
    (ha : A-1 ≤ a) (hab : a ≤ b) (hb : b ≤ S-2) :
    (∫ u in a..b,endpointKernel S A u)=endpointPrimitive S A b-endpointPrimitive S A a := by
  have hj : IntervalIntegrable (jKernel S A) volume a b := (jKernel_continuous hA hAS ha hab hb).intervalIntegrable
  have he : IntervalIntegrable (errorDensity (A+1)) volume a b :=
    (errorDensity_continuous (by linarith : 3 ≤ A+1) (by linarith : 0 < a) hab).intervalIntegrable
  have ht : IntervalIntegrable (CoupledJLogRecovery.secondError S A) volume a b :=
    (CoupledJLogRecovery.secondError_continuous hA hAS ha hab hb).intervalIntegrable
  unfold endpointKernel
  rw [intervalIntegral.integral_add (hj.add (he.const_mul _)) (ht.const_mul _),
    intervalIntegral.integral_add hj (he.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    jKernel_integral hA hAS ha hab hb,
    error_integral (by linarith) (by linarith) hab,
    CoupledJLogRecovery.second_integral hA hAS ha hab hb]
  unfold endpointPrimitive
  ring

def endpointRest (z : Fin 9 → ℝ) (s S : ℝ) : ℝ :=
  tail z (S-2)*log ((S-1)/(s-1))+
    ∑ k : Fin 9,z k*(endpointPrimitive S (jStart s S) (right (jStart s S-1) (S-2) k)-
      endpointPrimitive S (jStart s S) (left (jStart s S-1) (S-2) k))

theorem weighted_kernel_identity (z : Fin 9 → ℝ) {S A : ℝ}
    (hA : 2 ≤ A) (hAS : A ≤ S-1) (hS5 : S ≤ 5) :
    (∫ u in (A-1)..(S-2),nineProfile z u*endpointKernel S A u)=
      ∑ k : Fin 9,z k*(endpointPrimitive S A (right (A-1) (S-2) k)-
        endpointPrimitive S A (left (A-1) (S-2) k)) := by
  have ha : 1 ≤ A-1 := by linarith
  have hab : A-1 ≤ S-2 := by linarith
  have hb : S-2 ≤ 3 := by linarith
  have hp : IntervalIntegrable (nineProfile z) volume (A-1) (S-2) := by
    apply (profile_subinterval (nineProfile_integrable z) ha (hab.trans hb)).mono_set
    rw [uIcc_of_le hab,uIcc_of_le (hab.trans hb)]
    exact Icc_subset_Icc le_rfl hb
  rw [integral_cells z ha hab hb (hp.mul_continuousOn
    (endpointKernel_continuous hA hAS le_rfl hab le_rfl))]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun v => z k*v)
    (endpointKernel_integral hA hAS (clip_bounds hab).1 (cell_order _ _ k) (clip_bounds hab).2)

theorem endpointRest_le (z : Fin 9 → ℝ) (hz : ∀ k,0 ≤ z k) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5) (hsS : s ≤ S) (hr : 2 ≤ S-S/s) :
    aProfile (nineProfile z)*log ((S-1)/(s-1))+endpointRest z s S ≤ profileJ z s S := by
  have hA : 2 ≤ jStart s S := hr
  have hAS : jStart s S ≤ S-1 := by
    have h := (one_le_div (by linarith : 0 < s)).mpr hsS
    dsimp [jStart]
    linarith
  have hab : jStart s S-1 ≤ S-2 := by linarith
  have hb : S-2 ≤ 3 := by linarith
  have hip : IntervalIntegrable (nineProfile z) volume (jStart s S-1) (S-2) := by
    apply (profile_subinterval (nineProfile_integrable z) (by linarith : 1 ≤ jStart s S-1)
      (hab.trans hb)).mono_set
    rw [uIcc_of_le hab,uIcc_of_le (hab.trans hb)]
    exact Icc_subset_Icc le_rfl hb
  have ho : ContinuousOn (fun u => odds S (jStart s S) (u+1)/u)
      (uIcc (jStart s S-1) (S-2)) := by
    rw [uIcc_of_le hab]
    intro u hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have ha0 : jStart s S ≠ 0 := by linarith
    have hd : S-(u+1) ≠ 0 := by linarith [hu.2]
    have hx : (u+1)/jStart s S ≠ 0 := div_ne_zero (by linarith [hu.1]) ha0
    have hy : (S-jStart s S)/(S-(u+1)) ≠ 0 := div_ne_zero (by linarith) hd
    apply ContinuousAt.continuousWithinAt
    unfold odds
    fun_prop (disch := assumption)
  have hm := intervalIntegral.integral_mono_on hab
    (hip.mul_continuousOn (endpointKernel_continuous hA hAS le_rfl hab le_rfl))
    (hip.mul_continuousOn ho)
    (fun u hu => mul_le_mul_of_nonneg_left (endpointKernel_le hA hAS hu) (nineProfile_nonneg hz u))
  rw [weighted_kernel_identity z hA hAS hS5] at hm
  have shift := intervalIntegral.integral_comp_add_right
    (a := jStart s S-1) (b := S-2)
    (fun t => nineProfile z (t-1)/(t-1)*odds S (jStart s S) t) 1
  simp only [sub_add_cancel,add_sub_cancel_right,show S-2+1=S-1 by ring] at shift
  have identity : (fun u => nineProfile z u*(odds S (jStart s S) (u+1)/u))=
      (fun u => nineProfile z u/u*odds S (jStart s S) (u+1)) := by funext u; ring
  rw [identity,shift] at hm
  rw [profileJ_original_log z hs hS hS5 hsS hr,g_tail_eq z hS hS5]
  unfold endpointRest
  linarith only [hm]

end
end SigmaJEndpoint
