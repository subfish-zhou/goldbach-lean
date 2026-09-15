import FirstFeedbackTail

namespace FirstFeedbackIntegrals
open Wu2008DoubleSieve NodeExtension ActualNineFeedback Real Set MeasureTheory
open Wu04WholeCollection Wu04FactorJPrimitive SharpLogRecurrence
open scoped Interval BigOperators
noncomputable section

def jCurveDensity (S u : ℝ) : ℝ := lowerLog ((S-2)/(S*u-1))/(u*(1-u))
def jCurvePrimitive (S u : ℝ) : ℝ := mobiusPrim (-1) (2*(S-2)) S (S-3) u
def jCurvePaid (s S : ℝ) : ℝ :=
  let l := 1-1/s
  let r := 1-1/S
  let y := fun t => S*t+(S-3)
  let c := c0 (-1) (2*(S-2)) (S-3)
  let d := c1 (-1) (2*(S-2)) S (S-3)
  signedLow c (r/l)+signedLow (-d) ((1-r)/(1-l))+
    signedLow (d-c) (y r/y l)-
    h2 (-1) (2*(S-2)) S (S-3)*(1/y r-1/y l)-
    h3 (2*(S-2)) S (S-3)/2*(1/(y r)^2-1/(y l)^2)

theorem jCurve_deriv {S u : ℝ} (hS : 3<S) (hu0 : 0<u) (hu1 : u<1)
    (hSu : 2≤S*u) : HasDerivAt (jCurvePrimitive S) (jCurveDensity S u) u := by
  have hv : S-3≠0 := by linarith
  have hw : S+(S-3)≠0 := by linarith
  have hy : S*u+(S-3)≠0 := by linarith
  have h := mobius_deriv (k := -1) (h := 2*(S-2)) (u := S) (v := S-3)
    hv hw hu0.ne' (by linarith) hy
  convert h using 1 <;> first | rfl | skip
  unfold jCurveDensity lowerLog cubic
  rw [cayley_div (by linarith : S*u-1≠0) (by linarith : S-2+(S*u-1)≠0)]
  have he : (S-2-(S*u-1))/(S-2+(S*u-1))= -1+2*(S-2)/(S*u+(S-3)) := by
    have hden : S-2+(S*u-1)=S*u+(S-3) := by ring
    rw [hden]
    field_simp [hy]
    ring
  rw [he]

theorem jCurve_integrable {s S : ℝ} (hs : 2 ≤ s) (hS : 3<S) (hS5 : S≤5)
    (hsS : s≤S) (hr : 2≤S-S/s) :
    IntervalIntegrable (jCurveDensity S) volume (1-1/s) (1-1/S) := by
  have hg := J_geometry hs hS.le hS5 hsS hr
  apply ContinuousOn.intervalIntegrable_of_Icc (h := hg.1)
  intro u hu
  have h := hg.2 u hu
  have hSu : 0<S*u-1 := by linarith [h.2.2.1]
  have hS2 : 0<S-2 := by linarith
  have hu1 : 0<1-u := by linarith [h.2.1]
  have hu0 := h.1
  unfold jCurveDensity lowerLog
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := positivity)

theorem jCurvePaid_le_integral {s S : ℝ} (hs : 2 ≤ s) (hS : 3<S) (hS5 : S≤5)
    (hsS : s≤S) (hr : 2≤S-S/s) :
    jCurvePaid s S≤∫ u in (1-1/s)..(1-1/S),jCurveDensity S u := by
  have hg := J_geometry hs hS.le hS5 hsS hr
  have hl := hg.2 _ ⟨le_rfl,hg.1⟩
  have hu := hg.2 _ ⟨hg.1,le_rfl⟩
  have hs0 : 0<s := by linarith
  have hS0 : 0<S := by linarith
  have hyl : 0<S*(1-1/s)+(S-3) := by linarith [hl.2.2.1]
  have hyu : 0<S*(1-1/S)+(S-3) := by linarith [hu.2.2.1]
  have hll : 0<1-(1-1/s) := by linarith [hl.2.1]
  have huu : 0<1-(1-1/S) := by linarith [hu.2.1]
  have he : (∫ u in (1-1/s)..(1-1/S),jCurveDensity S u)=
      jCurvePrimitive S (1-1/S)-jCurvePrimitive S (1-1/s) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u hu
      rw [uIcc_of_le hg.1] at hu
      have h := hg.2 u hu
      exact jCurve_deriv hS h.1 h.2.1 h.2.2.1
    · exact jCurve_integrable hs hS hS5 hsS hr
  rw [he]
  have h0 := signed_bound (c0 (-1) (2*(S-2)) (S-3)) (div_pos hu.1 hl.1)
  have h1 := signed_bound (-c1 (-1) (2*(S-2)) S (S-3)) (div_pos huu hll)
  have h2 := signed_bound (c1 (-1) (2*(S-2)) S (S-3)-c0 (-1) (2*(S-2)) (S-3))
    (div_pos hyu hyl)
  rw [log_div hu.1.ne' hl.1.ne'] at h0
  rw [log_div huu.ne' hll.ne'] at h1
  rw [log_div hyu.ne' hyl.ne'] at h2
  dsimp [jCurvePaid,jCurvePrimitive,mobiusPrim]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring_nf at h0 h1 h2 ⊢
  linarith only [h0,h1,h2]

def jWeight (s S : ℝ) : ℝ := low ((S-1)/(s-1))

theorem weight_integral {s S : ℝ} (hs : 2 ≤ s) (hS : 3≤S) (hS5 : S≤5)
    (hsS : s≤S) (hr : 2≤S-S/s) :
    (∫ u in (1-1/s)..(1-1/S),(1:ℝ)/(u*(1-u)))=log ((S-1)/(s-1)) := by
  have hg := J_geometry hs hS hS5 hsS hr
  have hs0 : 0<s := by linarith
  have hS0 : 0<S := by linarith
  have hl := hg.2 _ ⟨le_rfl,hg.1⟩
  have hu := hg.2 _ ⟨hg.1,le_rfl⟩
  have he : (∫ u in (1-1/s)..(1-1/S),(1:ℝ)/(u*(1-u)))=
      (log (1-1/S)-log (1-(1-1/S)))-(log (1-1/s)-log (1-(1-1/s))) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => log u-log (1-u))
    · intro u hu
      rw [uIcc_of_le hg.1] at hu
      have h := hg.2 u hu
      have h1 : 1-u≠0 := by linarith [h.2.1]
      have hd := (hasDerivAt_log h.1.ne').sub
        (((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u)).log h1)
      convert hd using 1 <;> first | rfl | skip
      dsimp
      field_simp [h.1.ne', h1]
      ring
    · apply ContinuousOn.intervalIntegrable_of_Icc (h := hg.1)
      intro u hu
      have h := hg.2 u hu
      have hu0 := h.1
      have hu1 : 0<1-u := by linarith [h.2.1]
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := positivity)
  rw [he]
  have hp := (Wu04WholeCollection.logs (by linarith : 1<s) (by linarith : 1<S))
  linarith only [hp.1,hp.2]

end
end FirstFeedbackIntegrals
