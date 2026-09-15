import FiniteEndpointPrimitive

namespace FiniteEndpointPayment
open Wu2008DoubleSieve NodeExtension ActualNineFeedback Real Set MeasureTheory
open SharpLogRecurrence CoupledIntegralRecovery
open scoped Interval BigOperators
noncomputable section

def jKernel (S A u : ℝ) : ℝ :=
  rationalKernel (1+A) (2*A) u-rationalKernel (-(2*S-A-1)) (-2*(S-A)) u

def jPrimitive (S A u : ℝ) : ℝ :=
  primitive (1+A) (2*A) u-primitive (-(2*S-A-1)) (-2*(S-A)) u

theorem jKernel_eq {S A u : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S-1)
    (hu : u∈Icc (A-1) (S-2)) :
    jKernel S A u=(lowerLog ((u+1)/A)+lowerLog ((S-A)/(S-1-u)))/u := by
  rw [jKernel,first_rational_eq (by linarith) (by linarith [hu.1]),
    second_rational_eq (by linarith [hu.2]) (by linarith [hu.2])]
  ring

theorem jKernel_le {S A u : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S-1)
    (hu : u∈Icc (A-1) (S-2)) : jKernel S A u ≤ odds S A (u+1)/u := by
  rw [jKernel_eq hA hAS hu]
  apply div_le_div_of_nonneg_right _ (by linarith [hu.1])
  unfold odds
  have h1 := log_lower (t := (u+1)/A)
    ((one_le_div (by linarith : 0<A)).mpr (by linarith [hu.1]))
  have h2 := log_lower (t := (S-A)/(S-1-u))
    ((one_le_div (by linarith [hu.2] : 0<S-1-u)).mpr (by linarith [hu.1]))
  have he : S-(u+1)=S-1-u := by ring
  rw [he]
  exact add_le_add h1 h2

theorem jKernel_continuous {S A a b : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S-1)
    (ha : A-1 ≤ a) (hab : a ≤ b) (hb : b ≤ S-2) :
    ContinuousOn (jKernel S A) (uIcc a b) := by
  apply ContinuousOn.sub
  · apply rational_continuous hab
    · intro t ht; linarith [ht.1]
    · intro t ht; linarith [ht.1]
  · apply rational_continuous hab
    · intro t ht; linarith [ht.1]
    · intro t ht; linarith [ht.2]

theorem jKernel_integral {S A a b : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S-1)
    (ha : A-1 ≤ a) (hab : a ≤ b) (hb : b ≤ S-2) :
    (∫ t in a..b,jKernel S A t)=jPrimitive S A b-jPrimitive S A a := by
  have h1 := rational_continuous (q := 1+A) (v := 2*A) hab
    (fun t ht => by linarith [ht.1]) (fun t ht => by linarith [ht.1])
  have h2 := rational_continuous (q := -(2*S-A-1)) (v := -2*(S-A)) hab
    (fun t ht => by linarith [ht.1]) (fun t ht => by linarith [ht.2])
  unfold jKernel
  rw [intervalIntegral.integral_sub h1.intervalIntegrable h2.intervalIntegrable,
    rational_integral (by linarith : 1+A≠0) hab
      (fun t ht => by linarith [ht.1]) (fun t ht => by linarith [ht.1]),
    rational_integral (by linarith : -(2*S-A-1)≠0) hab
      (fun t ht => by linarith [ht.1]) (fun t ht => by linarith [ht.2])]
  unfold jPrimitive
  ring

/-- Complete finite original-cell payment, retaining the true terminal tail. -/
def j (z : Fin 9 → ℝ) (s S : ℝ) : ℝ :=
  (aProfile (nineProfile z)+tail z (S-2))*log ((S-1)/(s-1))+
    ∑ k : Fin 9,z k*(jPrimitive S (jStart s S) (right (jStart s S-1) (S-2) k)-
      jPrimitive S (jStart s S) (left (jStart s S-1) (S-2) k))

theorem j_le (z : Fin 9 → ℝ) (hz : ∀ k,0 ≤ z k) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5) (hsS : s ≤ S) (hr : 2 ≤ S-S/s) :
    j z s S ≤ profileJ z s S := by
  have hA : 2 ≤ jStart s S := hr
  have hAS : jStart s S ≤ S-1 := by
    have hd := (one_le_div (by linarith : 0<s)).mpr hsS
    unfold jStart
    linarith
  have hab : jStart s S-1 ≤ S-2 := by linarith
  have ha : 1 ≤ jStart s S-1 := by linarith
  have hb : S-2 ≤ 3 := by linarith
  have hp := profile_subinterval (nineProfile_integrable z) ha (hab.trans hb)
  have hip : IntervalIntegrable (nineProfile z) volume (jStart s S-1) (S-2) := by
    apply hp.mono_set
    rw [uIcc_of_le hab,uIcc_of_le (hab.trans hb)]
    exact Icc_subset_Icc le_rfl hb
  have hj := jKernel_continuous hA hAS le_rfl hab le_rfl
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
      mul_le_mul_of_nonneg_left (jKernel_le hA hAS hu) (nineProfile_nonneg hz u))
  have he := integral_cells z ha hab hb (hip.mul_continuousOn hj)
  rw [he] at hm
  have hsum : (∑ k : Fin 9,z k*(∫ t in left (jStart s S-1) (S-2) k..
      right (jStart s S-1) (S-2) k,jKernel S (jStart s S) t)) =
      ∑ k : Fin 9,z k*(jPrimitive S (jStart s S) (right (jStart s S-1) (S-2) k)-
        jPrimitive S (jStart s S) (left (jStart s S-1) (S-2) k)) := by
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun x => z k*x)
      (jKernel_integral hA hAS (clip_bounds hab).1 (cell_order _ _ k) (clip_bounds hab).2)
  rw [hsum] at hm
  rw [profileJ_original_log z hs hS hS5 hsS hr,g_tail_eq z hS hS5]
  unfold j
  apply add_le_add le_rfl
  refine hm.trans_eq ?_
  have hc := intervalIntegral.integral_comp_add_right
    (a := jStart s S-1) (b := S-2)
    (fun t => nineProfile z (t-1)/(t-1)*odds S (jStart s S) t) 1
  simp only [sub_add_cancel,show S-2+1=S-1 by ring,add_sub_cancel_right] at hc
  rw [← hc]
  congr 1
  funext t
  ring

end
end FiniteEndpointPayment
