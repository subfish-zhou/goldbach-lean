import WR2ClassicalBTrapezoid
import WR2ClassicalQuotient

noncomputable section
namespace WuPaper.ClassicalB
open Real Set MeasureTheory Wu08OriginalFirstSteps
open scoped Interval

def firstValue (s : ℝ) : ℝ := ClassicalC.left (s-1)
def deriv2 (s : ℝ) : ℝ := ClassicalC.leftD1 (s-1)

theorem B_deriv {s : ℝ} (hs : 3 ≤ s) : HasDerivAt B (firstValue s) s := by
  have h := FirstIntegralRecovery.B_hasDerivAt s
  simpa only [k_literal (by linarith : 2 ≤ s-1),firstValue,ClassicalC.left] using h

theorem deriv_deriv {s : ℝ} (hs : 3 ≤ s) : HasDerivAt firstValue (deriv2 s) s := by
  have h := (ClassicalC.left_deriv (by linarith : 2 ≤ s-1)).comp s ((hasDerivAt_id s).sub_const 1)
  convert h using 1 <;> first | rfl | (dsimp [firstValue,deriv2]; ring)

theorem B_bounds {s : ℝ} (hs : 3 ≤ s) (hs6 : s ≤ 6) : 0 ≤ B s ∧ B s ≤ 6 := by
  have hinterval : (2:ℝ) ≤ s-1 := by linarith
  have hi := k_continuous.intervalIntegrable (μ := volume) 2 (s-1)
  have hk (u : ℝ) (hu : u ∈ Icc (2:ℝ) (s-1)) : 0 ≤ k u ∧ k u ≤ 2 := by
    have hb := ClassicalC.left_bounds hu.1 (by linarith [hu.2])
    rw [k_literal hu.1]
    exact ⟨hb.1,(le_abs_self _).trans hb.2.1⟩
  have hl := intervalIntegral.integral_mono_on hinterval
    (intervalIntegrable_const (c := (0:ℝ)) (μ := volume)) hi (fun u hu => (hk u hu).1)
  have hh := intervalIntegral.integral_mono_on hinterval hi
    (intervalIntegrable_const (c := (2:ℝ)) (μ := volume)) (fun u hu => (hk u hu).2)
  simp only [intervalIntegral.integral_const,smul_eq_mul,mul_zero] at hl hh
  change 0 ≤ B s at hl
  change B s ≤ _ at hh
  exact ⟨hl,by linarith only [hh,hs6]⟩

theorem weighted_second_bound {s : ℝ} (hs : 3 ≤ s) (hs6 : s ≤ 6) :
    |ClassicalQuotient.second B firstValue deriv2 s| ≤ 2 := by
  have hb := B_bounds hs hs6
  have hk := ClassicalC.left_bounds (by linarith : 2 ≤ s-1) (by linarith : s-1 ≤ 5)
  have h := ClassicalQuotient.second_bound (f := B) (f' := firstValue) (f'' := deriv2)
    (F0 := 6) (by norm_num : (0:ℝ) < 3) hs (by rw [abs_of_nonneg hb.1]; exact hb.2) hk.2.1 hk.2.2.1
  norm_num at h
  linarith only [h]

end WuPaper.ClassicalB
#print axioms WuPaper.ClassicalB.B_bounds
#print axioms WuPaper.ClassicalB.weighted_second_bound
