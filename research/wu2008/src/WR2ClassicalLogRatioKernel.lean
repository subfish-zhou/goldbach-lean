import WR2ClassicalMidpointPanels

noncomputable section
namespace WuPaper.ClassicalLogRatio
open Real

def weight (t : ℝ) : ℝ := 1/t+1/(1-t)
def weightD1 (t : ℝ) : ℝ := -1/t^2+1/(1-t)^2
def weightD2 (t : ℝ) : ℝ := 2/t^3+2/(1-t)^3

def logarithm (a b c d t : ℝ) : ℝ := log (a+b*t)-log (c+d*t)
def logD1 (a b c d t : ℝ) : ℝ := b/(a+b*t)-d/(c+d*t)
def logD2 (a b c d t : ℝ) : ℝ := -b^2/(a+b*t)^2+d^2/(c+d*t)^2

def kernel (a b c d t : ℝ) : ℝ := weight t*logarithm a b c d t
def kernelD1 (a b c d t : ℝ) : ℝ :=
  weightD1 t*logarithm a b c d t+weight t*logD1 a b c d t
def kernelD2 (a b c d t : ℝ) : ℝ :=
  weightD2 t*logarithm a b c d t+2*weightD1 t*logD1 a b c d t+weight t*logD2 a b c d t

theorem weight_deriv {t : ℝ} (h0 : t ≠ 0) (h1 : 1-t ≠ 0) :
    HasDerivAt weight (weightD1 t) t := by
  have h := ((hasDerivAt_const t (1:ℝ)).div (hasDerivAt_id t) h0).add
    ((hasDerivAt_const t (1:ℝ)).div ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)) h1)
  change HasDerivAt weight _ t at h
  apply h.congr_deriv
  dsimp [weightD1]
  ring

theorem weightD1_deriv {t : ℝ} (h0 : t ≠ 0) (h1 : 1-t ≠ 0) :
    HasDerivAt weightD1 (weightD2 t) t := by
  have h := ((hasDerivAt_const t (-1:ℝ)).div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 h0)).add
    ((hasDerivAt_const t (1:ℝ)).div (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow 2)
      (pow_ne_zero 2 h1))
  change HasDerivAt weightD1 _ t at h
  apply h.congr_deriv
  dsimp [weightD2]
  field_simp
  ring

theorem logarithm_deriv (a b c d : ℝ) {t : ℝ} (ha : a+b*t ≠ 0) (hc : c+d*t ≠ 0) :
    HasDerivAt (logarithm a b c d) (logD1 a b c d t) t := by
  have h := ((((hasDerivAt_id t).const_mul b).const_add a).log ha).sub
    ((((hasDerivAt_id t).const_mul d).const_add c).log hc)
  change HasDerivAt (logarithm a b c d) _ t at h
  apply h.congr_deriv
  dsimp [logD1]
  ring

theorem logD1_deriv (a b c d : ℝ) {t : ℝ} (ha : a+b*t ≠ 0) (hc : c+d*t ≠ 0) :
    HasDerivAt (logD1 a b c d) (logD2 a b c d t) t := by
  have h := ((hasDerivAt_const t b).div (((hasDerivAt_id t).const_mul b).const_add a) ha).sub
    ((hasDerivAt_const t d).div (((hasDerivAt_id t).const_mul d).const_add c) hc)
  change HasDerivAt (logD1 a b c d) _ t at h
  apply h.congr_deriv
  dsimp [logD2]
  ring

theorem kernel_deriv (a b c d : ℝ) {t : ℝ}
    (h0 : t ≠ 0) (h1 : 1-t ≠ 0) (ha : a+b*t ≠ 0) (hc : c+d*t ≠ 0) :
    HasDerivAt (kernel a b c d) (kernelD1 a b c d t) t := by
  exact (weight_deriv h0 h1).mul (logarithm_deriv a b c d ha hc)

theorem kernelD1_deriv (a b c d : ℝ) {t : ℝ}
    (h0 : t ≠ 0) (h1 : 1-t ≠ 0) (ha : a+b*t ≠ 0) (hc : c+d*t ≠ 0) :
    HasDerivAt (kernelD1 a b c d) (kernelD2 a b c d t) t := by
  have h := ((weightD1_deriv h0 h1).mul (logarithm_deriv a b c d ha hc)).add
    ((weight_deriv h0 h1).mul (logD1_deriv a b c d ha hc))
  change HasDerivAt (kernelD1 a b c d) _ t at h
  apply h.congr_deriv
  dsimp [kernelD2]
  ring


theorem kernel_literal (a b c d : ℝ) {t : ℝ}
    (h0 : t ≠ 0) (h1 : 1-t ≠ 0) (ha : a+b*t ≠ 0) (hc : c+d*t ≠ 0) :
    kernel a b c d t = log ((a+b*t)/(c+d*t))/(t*(1-t)) := by
  rw [log_div ha hc]
  unfold kernel weight logarithm
  field_simp
  ring

/-- Componentwise bounds keep the three classical applications independent of calculus. -/
theorem second_derivative_bound {a b c d t W0 W1 W2 L0 L1 L2 : ℝ}
    (hw0 : |weight t| ≤ W0) (hw1 : |weightD1 t| ≤ W1) (hw2 : |weightD2 t| ≤ W2)
    (hl0 : |logarithm a b c d t| ≤ L0) (hl1 : |logD1 a b c d t| ≤ L1)
    (hl2 : |logD2 a b c d t| ≤ L2) :
    |kernelD2 a b c d t| ≤ W2*L0+2*W1*L1+W0*L2 := by
  have h0 := mul_le_mul hw2 hl0 (abs_nonneg _) ((abs_nonneg _).trans hw2)
  have h1 := mul_le_mul hw1 hl1 (abs_nonneg _) ((abs_nonneg _).trans hw1)
  have h2 := mul_le_mul hw0 hl2 (abs_nonneg _) ((abs_nonneg _).trans hw0)
  unfold kernelD2
  calc
    _ ≤ |weightD2 t*logarithm a b c d t+2*weightD1 t*logD1 a b c d t|+
        |weight t*logD2 a b c d t| := abs_add_le _ _
    _ ≤ |weightD2 t*logarithm a b c d t|+|2*weightD1 t*logD1 a b c d t|+
        |weight t*logD2 a b c d t| := add_le_add_left (abs_add_le _ _) _
    _ ≤ _ := by
      simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      nlinarith only [h0,h1,h2]

end WuPaper.ClassicalLogRatio
#print axioms WuPaper.ClassicalLogRatio.kernelD1_deriv

#print axioms WuPaper.ClassicalLogRatio.second_derivative_bound
