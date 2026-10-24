import WR2ClassicalCPolynomialDerivatives
import WR2ClassicalLowerLog

noncomputable section
namespace WuPaper.ClassicalFifthProfile
open Real Wu2008DoubleSieve Wu08OriginalFirstSteps
open ClassicalSixthKernel ClassicalCPolynomial

def initial : ℝ → ℝ := logFactor
def initialD1 : ℝ → ℝ := logFirst
def initialD2 : ℝ → ℝ := logSecond
def terminal (s : ℝ) : ℝ := initial s+cPoly (s-4)
def terminalD1 (s : ℝ) : ℝ := initialD1 s+cFirst (s-4)
def terminalD2 (s : ℝ) : ℝ := initialD2 s+cSecond (s-4)

theorem initial_deriv {s : ℝ} (hs : 2 ≤ s) : HasDerivAt initial (initialD1 s) s := log_deriv hs
theorem initialD1_deriv {s : ℝ} (hs : 2 ≤ s) : HasDerivAt initialD1 (initialD2 s) s := logFirst_deriv hs

theorem terminal_deriv {s : ℝ} (hs : 4 ≤ s) : HasDerivAt terminal (terminalD1 s) s := by
  have h := (initial_deriv (by linarith : 2 ≤ s)).add
    ((cPoly_deriv (s-4)).comp s ((hasDerivAt_id s).sub_const 4))
  convert h using 1 <;> first | rfl | (simp only [mul_one]; rfl)

theorem terminalD1_deriv {s : ℝ} (hs : 4 ≤ s) : HasDerivAt terminalD1 (terminalD2 s) s := by
  have h := (initialD1_deriv (by linarith : 2 ≤ s)).add
    ((cFirst_deriv (s-4)).comp s ((hasDerivAt_id s).sub_const 4))
  convert h using 1 <;> first | rfl | (simp only [mul_one]; rfl)

theorem initial_bounds {s : ℝ} (hs : 2 ≤ s) (he : s ≤ 5) :
    |initial s| ≤ 2 ∧ |initialD1 s| ≤ 1 ∧ |initialD2 s| ≤ 1 := by
  have hx : 0 < s-1 := by linarith
  have ha0 : 0 ≤ (s-1)⁻¹ := (inv_pos.mpr hx).le
  have ha : (s-1)⁻¹ ≤ 1 := by rw [← one_div]; apply (div_le_iff₀ hx).mpr; linarith
  have ha2 := pow_le_pow_left₀ ha0 ha 2
  refine ⟨?_,?_,?_⟩
  · rw [initial,logFactor,abs_of_nonneg (log_nonneg (by linarith))]
    have h := log_le_sub_one_of_pos (div_pos hx (by norm_num : (0:ℝ)<2))
    rw [log_div hx.ne' (by norm_num : (2:ℝ) ≠ 0)] at h
    have h2 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  · simpa [initialD1,logFirst,one_div,abs_of_nonneg ha0] using ha
  · simpa [initialD2,logSecond,neg_div,one_div,← inv_pow,abs_neg,abs_of_nonneg (sq_nonneg ((s-1)⁻¹))] using ha2

theorem terminal_bounds {s : ℝ} (hs : 4 ≤ s) (he : s ≤ 5) :
    |terminal s| ≤ 3 ∧ |terminalD1 s| ≤ 2 ∧ |terminalD2 s| ≤ 2 := by
  have hx : 0 ≤ s-4 := by linarith
  have hx1 : s-4 ≤ 1 := by linarith
  obtain ⟨hi,hi1,hi2⟩ := initial_bounds (by linarith : 2 ≤ s) he
  have hc : |cPoly (s-4)| ≤ 1 := by
    rw [abs_of_nonneg (cPoly_nonneg hx hx1)]
    exact cPoly_upper hx hx1
  have hc1 : |cFirst (s-4)| ≤ 1 := by
    rw [abs_of_nonneg (cFirst_bounds hx hx1).1]
    exact (cFirst_bounds hx hx1).2
  have hc2 := cSecond_bound hx hx1
  refine ⟨?_,?_,?_⟩
  · exact (abs_add_le _ _).trans ((add_le_add hi hc).trans (by norm_num))
  · exact (abs_add_le _ _).trans ((add_le_add hi1 hc1).trans (by norm_num))
  · exact (abs_add_le _ _).trans ((add_le_add hi2 hc2).trans (by norm_num))

theorem initial_le_lower {s : ℝ} (hs : 2 ≤ s) (he : s ≤ 5) : initial s ≤ wuLowerCoefficient s := by
  have h := ClassicalLowerLog.profile_le_lower (he.trans (by norm_num : (5:ℝ) ≤ 6))
  rw [ClassicalLowerLog.profile_literal hs] at h
  exact h

theorem terminal_le_lower {s : ℝ} (hs : 4 ≤ s) (he : s ≤ 5) : terminal s ≤ wuLowerCoefficient s := by
  have hc := cPoly_le_C (show 0 ≤ s-4 by linarith) (show s-4 ≤ 1 by linarith)
  rw [show (4:ℝ)+(s-4)=s by ring] at hc
  rw [lower_middle hs (by linarith)]
  change log (s-1)+cPoly (s-4) ≤ log (s-1)+C s
  linarith only [hc]

end WuPaper.ClassicalFifthProfile
#print axioms WuPaper.ClassicalFifthProfile.terminal_bounds
#print axioms WuPaper.ClassicalFifthProfile.terminal_le_lower
