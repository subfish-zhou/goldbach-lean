import CoupledJSecondPrimitive

namespace CoupledJLogRecovery
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open CoupledIntegralRecovery FiniteEndpointPayment FirstErrorFullPayment
open scoped Interval BigOperators
noncomputable section

def fullPrimitive (S A u : ℝ) : ℝ :=
  jPrimitive S A u+errorPrimitive (A+1) u+secondPrimitive S A u

theorem kernel_continuous {S A a b : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S-1)
    (ha : A-1 ≤ a) (hab : a ≤ b) (hb : b ≤ S-2) :
    ContinuousOn (kernel S A) (uIcc a b) :=
  ((jKernel_continuous hA hAS ha hab hb).add
    (errorDensity_continuous (by linarith) (by linarith) hab)).add
      (secondError_continuous hA hAS ha hab hb)

theorem kernel_integral {S A a b : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S-1)
    (ha : A-1 ≤ a) (hab : a ≤ b) (hb : b ≤ S-2) :
    (∫ u in a..b,kernel S A u)=fullPrimitive S A b-fullPrimitive S A a := by
  have hj : IntervalIntegrable (jKernel S A) volume a b :=
    (jKernel_continuous hA hAS ha hab hb).intervalIntegrable
  have he : IntervalIntegrable (errorDensity (A+1)) volume a b :=
    (errorDensity_continuous (S := A+1) (by linarith) (by linarith) hab).intervalIntegrable
  have hs : IntervalIntegrable (secondError S A) volume a b :=
    (secondError_continuous hA hAS ha hab hb).intervalIntegrable
  unfold kernel
  rw [intervalIntegral.integral_add (hj.add he) hs,
    intervalIntegral.integral_add hj he,jKernel_integral hA hAS ha hab hb,
    error_integral (by linarith) (by linarith) hab,second_integral hA hAS ha hab hb]
  unfold fullPrimitive
  ring

def jRest (z : Fin 9 → ℝ) (s S : ℝ) : ℝ :=
  tail z (S-2)*log ((S-1)/(s-1))+
    ∑ k : Fin 9,z k*(fullPrimitive S (jStart s S) (right (jStart s S-1) (S-2) k)-
      fullPrimitive S (jStart s S) (left (jStart s S-1) (S-2) k))

def jTerm (z : Fin 9 → ℝ) (s S : ℝ) : ℝ :=
  aProfile (nineProfile z)*log ((S-1)/(s-1))+jRest z s S

theorem jTerm_le (z : Fin 9 → ℝ) (hz : ∀ k,0 ≤ z k) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5) (hsS : s ≤ S) (hr : 2 ≤ S-S/s) :
    jTerm z s S  ≤  profileJ z s S := by
  have hA : 2 ≤ jStart s S := hr
  have hAS : jStart s S ≤ S-1 := by
    have hd := (one_le_div (by linarith : 0<s)).mpr hsS
    unfold jStart
    linarith
  have hab : jStart s S-1 ≤ S-2 := by linarith
  have ha : 1 ≤ jStart s S-1 := by linarith
  have hb : S-2 ≤ 3 := by linarith
  have hip : IntervalIntegrable (nineProfile z) volume (jStart s S-1) (S-2) := by
    apply (profile_subinterval (nineProfile_integrable z) ha (hab.trans hb)).mono_set
    rw [uIcc_of_le hab,uIcc_of_le (hab.trans hb)]
    exact Icc_subset_Icc le_rfl hb
  have hj := kernel_continuous hA hAS le_rfl hab le_rfl
  have ho : ContinuousOn (fun u => odds S (jStart s S) (u+1)/u)
      (uIcc (jStart s S-1) (S-2)) := by
    rw [uIcc_of_le hab]
    intro u hu
    have hu0 : u≠0 := by linarith [hu.1]
    have hA0 : jStart s S≠0 := by linarith
    have hden : S-(u+1)≠0 := by linarith [hu.2]
    have harg1 : (u+1)/jStart s S≠0 := div_ne_zero (by linarith [hu.1]) hA0
    have harg2 : (S-jStart s S)/(S-(u+1))≠0 := div_ne_zero (by linarith) hden
    apply ContinuousAt.continuousWithinAt
    unfold odds
    fun_prop (disch := assumption)
  have hm := intervalIntegral.integral_mono_on hab (hip.mul_continuousOn hj)
    (hip.mul_continuousOn ho) (fun u hu =>
      mul_le_mul_of_nonneg_left (kernel_le hA hAS hS5 hu) (nineProfile_nonneg hz u))
  rw [integral_cells z ha hab hb (hip.mul_continuousOn hj)] at hm
  have hsum : (∑ k : Fin 9,z k*(∫ t in left (jStart s S-1) (S-2) k..
      right (jStart s S-1) (S-2) k,kernel S (jStart s S) t)) =
      ∑ k : Fin 9,z k*(fullPrimitive S (jStart s S) (right (jStart s S-1) (S-2) k)-
        fullPrimitive S (jStart s S) (left (jStart s S-1) (S-2) k)) := by
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun x => z k*x)
      (kernel_integral hA hAS (clip_bounds hab).1 (cell_order _ _ k) (clip_bounds hab).2)
  rw [hsum] at hm
  rw [profileJ_original_log z hs hS hS5 hsS hr,g_tail_eq z hS hS5]
  unfold jTerm jRest
  have hc := intervalIntegral.integral_comp_add_right
    (a := jStart s S-1) (b := S-2)
    (fun t => nineProfile z (t-1)/(t-1)*odds S (jStart s S) t) 1
  simp only [sub_add_cancel,show S-2+1=S-1 by ring,add_sub_cancel_right] at hc
  have he : (∫ u in (jStart s S-1)..(S-2),nineProfile z u*(odds S (jStart s S) (u+1)/u)) =
      ∫ t in (jStart s S)..(S-1),nineProfile z (t-1)/(t-1)*odds S (jStart s S) t := by
    rw [← hc]
    congr 1
    funext t
    ring
  rw [he] at hm
  linarith only [hm]

end
end CoupledJLogRecovery
