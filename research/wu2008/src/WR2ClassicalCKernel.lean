import FirstIntegralFlat

noncomputable section
namespace WuPaper.ClassicalC
open Real Set MeasureTheory Wu08OriginalFirstSteps
open scoped Interval

def left (u : ℝ) : ℝ := log (u-1)/u
def leftD1 (u : ℝ) : ℝ := 1/(u-1)/u-log (u-1)/u^2
def leftD2 (u : ℝ) : ℝ := -1/(u-1)^2/u-2/(u-1)/u^2+2*log (u-1)/u^3

def right (s u : ℝ) : ℝ := log (s-1)-log (u+1)
def kernel (s u : ℝ) : ℝ := left u*right s u

def kernelD1 (s u : ℝ) : ℝ := leftD1 u*right s u-left u/(u+1)
def kernelD2 (s u : ℝ) : ℝ :=
  leftD2 u*right s u-2*leftD1 u/(u+1)+left u/(u+1)^2

theorem left_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt left (leftD1 u) u := by
  have h0 : u ≠ 0 := by linarith
  have h1 : u-1 ≠ 0 := by linarith
  have h := (((hasDerivAt_id u).sub_const 1).log h1).div (hasDerivAt_id u) h0
  change HasDerivAt left _ u at h
  apply h.congr_deriv
  dsimp [leftD1]
  field_simp

theorem leftD1_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt leftD1 (leftD2 u) u := by
  have h0 : u ≠ 0 := by linarith
  have h1 : u-1 ≠ 0 := by linarith
  have h := (((hasDerivAt_const u (1:ℝ)).div ((hasDerivAt_id u).sub_const 1) h1).div
    (hasDerivAt_id u) h0).sub ((((hasDerivAt_id u).sub_const 1).log h1).div
      ((hasDerivAt_id u).pow 2) (pow_ne_zero 2 h0))
  change HasDerivAt leftD1 _ u at h
  apply h.congr_deriv
  dsimp [leftD2]
  field_simp
  ring

theorem right_deriv (s : ℝ) {u : ℝ} (hu : 2 ≤ u) :
    HasDerivAt (right s) (-1/(u+1)) u := by
  have h := (hasDerivAt_const u (log (s-1))).sub
    (((hasDerivAt_id u).add_const 1).log (by linarith : u+1 ≠ 0))
  change HasDerivAt (right s) _ u at h
  apply h.congr_deriv
  dsimp
  ring

theorem kernel_deriv (s : ℝ) {u : ℝ} (hu : 2 ≤ u) :
    HasDerivAt (kernel s) (kernelD1 s u) u := by
  have h := (left_deriv hu).mul (right_deriv s hu)
  change HasDerivAt (kernel s) _ u at h
  apply h.congr_deriv
  dsimp [kernelD1]
  ring

theorem kernelD1_deriv (s : ℝ) {u : ℝ} (hu : 2 ≤ u) :
    HasDerivAt (kernelD1 s) (kernelD2 s u) u := by
  have h := ((leftD1_deriv hu).mul (right_deriv s hu)).sub
    ((left_deriv hu).div ((hasDerivAt_id u).add_const 1) (by linarith : u+1 ≠ 0))
  change HasDerivAt (kernelD1 s) _ u at h
  apply h.congr_deriv
  dsimp [kernelD2]
  field_simp
  ring

theorem C_integral {s : ℝ} (hs : 4 ≤ s) : C s = ∫ u in 2..s-2, kernel s u := by
  rw [FirstIntegralRecovery.C_flat hs]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (by linarith : (2:ℝ) ≤ s-2)] at hu
  dsimp only
  rw [log_div (by linarith : s-1 ≠ 0) (by linarith [hu.1] : u+1 ≠ 0)]
  rfl

end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.kernelD1_deriv
#print axioms WuPaper.ClassicalC.C_integral
