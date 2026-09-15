import CoupledCorrectedE

namespace CoupledJLogRecovery
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open SharpLogRecurrence CoupledIntegralRecovery FiniteEndpointPayment FirstErrorFullPayment
open scoped Interval BigOperators
noncomputable section

theorem second_lower_error {x : ℝ} (hx : 1≤x) (hx3 : x≤3) :
    (9/17)*(upperLog x-lowerLog x) ≤ log x-lowerLog x := by
  have hx0 : 0<x := by linarith
  have hq : 0<x^2+8*x+1 := by positivity
  have hc : (9:ℝ)/17≤6*x/(x^2+8*x+1) := by
    apply (le_div_iff₀ hq).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hx3) (show 0≤3*x-1 by linarith)]
  have hg : 0≤upperLog x-lowerLog x := by
    rw [OriginalFirstErrorRecovery.envelope_gap hx0]
    positivity
  exact (mul_le_mul_of_nonneg_right hc hg).trans (F1FullRecoveryPayment.lowerGapPayment_le hx)

def secondError (S A u : ℝ) : ℝ :=
  (9/17)*(upperLog ((S-A)/(S-1-u))-lowerLog ((S-A)/(S-1-u)))/u

def kernel (S A u : ℝ) : ℝ :=
  jKernel S A u+errorDensity (A+1) u+secondError S A u

theorem second_argument_bounds {S A u : ℝ} (hA : 2≤A) (_hAS : A≤S-1)
    (hS5 : S≤5) (hu : u∈Icc (A-1) (S-2)) :
    1≤(S-A)/(S-1-u) ∧ (S-A)/(S-1-u)≤3 := by
  have hd : 0<S-1-u := by linarith [hu.2]
  constructor
  · exact (one_le_div hd).mpr (by linarith [hu.1])
  · apply (div_le_iff₀ hd).mpr
    linarith [hu.2]

theorem kernel_le {S A u : ℝ} (hA : 2≤A) (hAS : A≤S-1)
    (hS5 : S≤5) (hu : u∈Icc (A-1) (S-2)) :
    kernel S A u ≤ odds S A (u+1)/u := by
  have h1 := corrected_le (S := A+1) (by linarith) (by linarith [hu.1])
    (by linarith [hu.2] : u≤3)
  have hx := second_argument_bounds hA hAS hS5 hu
  have h2 := div_le_div_of_nonneg_right (second_lower_error hx.1 hx.2)
    (show 0≤u by linarith [hu.1])
  simp only [add_sub_cancel_right] at h1
  unfold kernel secondError
  rw [jKernel_eq hA hAS hu]
  unfold odds
  rw [show S-(u+1)=S-1-u by ring]
  simp only [sub_div,add_div] at h1 h2 ⊢
  linarith only [h1,h2]

theorem secondError_nonneg {S A u : ℝ} (hA : 2≤A) (hAS : A≤S-1)
    (hu : u∈Icc (A-1) (S-2)) : 0 ≤ secondError S A u := by
  have hd : 0<S-1-u := by linarith [hu.2]
  have hx0 : 0<(S-A)/(S-1-u) := div_pos (by linarith) hd
  have hx : 1≤(S-A)/(S-1-u) := (one_le_div hd).mpr (by linarith [hu.1])
  unfold secondError
  rw [OriginalFirstErrorRecovery.envelope_gap hx0]
  have : 0≤(S-A)/(S-1-u)-1 := sub_nonneg.mpr hx
  have : 0≤u := by linarith [hu.1]
  positivity

end
end CoupledJLogRecovery
