import WR2ClassicalFourthWeight
import WR2ClassicalDAnalytic

noncomputable section
namespace WuPaper.ClassicalFourth
open Real Set Wu08OriginalFirstSteps

def kernel (f : ℝ → ℝ) (s : ℝ) : ℝ := weight s*f s
def kernelD1 (f f' : ℝ → ℝ) (s : ℝ) : ℝ := weightD1 s*f s+weight s*f' s
def kernelD2 (f f' f'' : ℝ → ℝ) (s : ℝ) : ℝ :=
  weightD2 s*f s+2*weightD1 s*f' s+weight s*f'' s

theorem kernel_deriv {f f' : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (hr : R-s ≠ 0)
    (hf : HasDerivAt f (f' s) s) : HasDerivAt (kernel f) (kernelD1 f f' s) s := by
  exact (weight_deriv hs hr).mul hf

theorem kernelD1_deriv {f f' f'' : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (hr : R-s ≠ 0)
    (hf : HasDerivAt f (f' s) s) (hf' : HasDerivAt f' (f'' s) s) :
    HasDerivAt (kernelD1 f f') (kernelD2 f f' f'' s) s := by
  have h := ((weightD1_deriv hs hr).mul hf).add ((weight_deriv hs hr).mul hf')
  change HasDerivAt (kernelD1 f f') _ s at h
  apply h.congr_deriv
  dsimp [kernelD2]
  ring

theorem kernel_second_bound {f f' f'' : ℝ → ℝ} {s : ℝ} (hs : 3 ≤ s) (hr : s ≤ R-1)
    (hf : |f s| ≤ 8) (hf' : |f' s| ≤ 3) (hf'' : |f'' s| ≤ 3) :
    |kernelD2 f f' f'' s| ≤ 56 := by
  obtain ⟨hw,hw1,hw2⟩ := weight_bounds hs hr
  have h0 := mul_le_mul hw2 hf (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 112/27)
  have h1 := mul_le_mul hw1 hf' (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 20/9)
  have h2 := mul_le_mul hw hf'' (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 8/3)
  have hh := abs_add_le (weightD2 s*f s+2*weightD1 s*f' s) (weight s*f'' s)
  have hh' := abs_add_le (weightD2 s*f s) (2*weightD1 s*f' s)
  simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)] at hh hh'
  unfold kernelD2
  nlinarith only [h0,h1,h2,hh,hh']

def initial (s : ℝ) : ℝ := 1+B s
def terminal (s : ℝ) : ℝ := 1+B s+D s
def terminalD1 (s : ℝ) : ℝ := ClassicalB.firstValue s+ClassicalD.firstValue s
def terminalD2 (s : ℝ) : ℝ := ClassicalB.deriv2 s+ClassicalD.secondValue s

theorem initial_bounds {s : ℝ} (hs : 3 ≤ s) (hs6 : s ≤ 6) :
    |initial s| ≤ 8 ∧ |ClassicalB.firstValue s| ≤ 3 ∧ |ClassicalB.deriv2 s| ≤ 3 := by
  have hb := ClassicalB.B_bounds hs hs6
  have hk := ClassicalC.left_bounds (by linarith : 2 ≤ s-1) (by linarith : s-1 ≤ 5)
  refine ⟨?_,?_,?_⟩
  · unfold initial
    rw [abs_of_nonneg (by linarith [hb.1])]
    linarith only [hb.2]
  · exact hk.2.1.trans (by norm_num)
  · exact hk.2.2.1.trans (by norm_num)

theorem terminal_bounds {s : ℝ} (hs : 5 ≤ s) (hs6 : s ≤ 6) :
    |terminal s| ≤ 8 ∧ |terminalD1 s| ≤ 3 ∧ |terminalD2 s| ≤ 3 := by
  have hb := ClassicalB.B_bounds (by linarith) hs6
  have hk := ClassicalC.left_bounds (by linarith : 2 ≤ s-1) (by linarith : s-1 ≤ 5)
  have hd := ClassicalD.D_bounds hs hs6
  have hd' := ClassicalD.derivative_bounds hs hs6
  refine ⟨?_,?_,?_⟩
  · unfold terminal
    rw [abs_of_nonneg (by linarith [hb.1,hd.1])]
    linarith only [hb.2,hd.2]
  · exact (abs_add_le _ _).trans (by dsimp [ClassicalB.firstValue]; linarith only [hk.2.1,hd'.1])
  · exact (abs_add_le _ _).trans (by dsimp [ClassicalB.deriv2]; linarith only [hk.2.2.1,hd'.2])

end WuPaper.ClassicalFourth
#print axioms WuPaper.ClassicalFourth.kernel_second_bound
#print axioms WuPaper.ClassicalFourth.terminal_bounds
