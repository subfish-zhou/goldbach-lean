import WR2ClassicalSixthWeight
import WR2ClassicalSixthBranch

noncomputable section
namespace WuPaper.ClassicalSixthKernel
open Real
open WuSource.SrcSixthGain
open ClassicalSixthWeight

def logFactor (s : ℝ) : ℝ := log (s-1)
def logFirst (s : ℝ) : ℝ := 1/(s-1)
def logSecond (s : ℝ) : ℝ := -1/(s-1)^2

theorem log_deriv {s : ℝ} (hs : 2 ≤ s) :
    HasDerivAt logFactor (logFirst s) s := by
  exact ((hasDerivAt_id s).sub_const 1).log (by change s-1 ≠ 0; linarith)

theorem logFirst_deriv {s : ℝ} (hs : 2 ≤ s) :
    HasDerivAt logFirst (logSecond s) s := by
  have h := (hasDerivAt_const s (1:ℝ)).div ((hasDerivAt_id s).sub_const 1) (by change s-1 ≠ 0; linarith)
  change HasDerivAt logFirst _ s at h
  apply h.congr_deriv
  dsimp [logSecond]
  ring

theorem log_bounds {s : ℝ} (hs : 2 ≤ s) (he : s ≤ endpoint) :
    |logFactor s| ≤ 2 ∧ |logFirst s| ≤ 1 ∧ |logSecond s| ≤ 1 := by
  have hx : 0 < s-1 := by linarith
  have hs5 : s ≤ 5 := he.trans (by norm_num [endpoint,QuarterTrim.alpha,QuarterTrim.beta])
  have ha0 : 0 ≤ (s-1)⁻¹ := (inv_pos.mpr hx).le
  have ha : (s-1)⁻¹ ≤ 1 := by rw [← one_div]; apply (div_le_iff₀ hx).mpr; linarith
  have ha2 := pow_le_pow_left₀ ha0 ha 2
  refine ⟨?_,?_,?_⟩
  · rw [logFactor,abs_of_nonneg (log_nonneg (by linarith))]
    have h := log_le_sub_one_of_pos (div_pos hx (by norm_num : (0:ℝ)<2))
    rw [log_div hx.ne' (by norm_num : (2:ℝ) ≠ 0)] at h
    have h2 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  · simpa [logFirst,one_div,abs_of_nonneg ha0] using ha
  · simpa [logSecond,neg_div,one_div,← inv_pow,abs_neg,abs_of_nonneg (sq_nonneg ((s-1)⁻¹))] using ha2

/-- Absolute bounds for the derivative of a product, independent of the functions. -/
theorem first_bound {a b c d A B C D : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) (hd : |d| ≤ D) :
    |a*b+c*d| ≤ A*B+C*D := by
  calc
    _ ≤ |a*b|+|c*d| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha))
        (mul_le_mul hc hd (abs_nonneg _) ((abs_nonneg _).trans hc))

theorem second_bound {a b c d e f A B C D E F : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (he : |e| ≤ E) (hf : |f| ≤ F) :
    |a*b+2*c*d+e*f| ≤ A*B+2*C*D+E*F := by
  have h0 := mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
  have h1 := mul_le_mul hc hd (abs_nonneg _) ((abs_nonneg _).trans hc)
  have h2 := mul_le_mul he hf (abs_nonneg _) ((abs_nonneg _).trans he)
  calc
    _ ≤ |a*b+2*c*d|+|e*f| := abs_add_le _ _
    _ ≤ |a*b|+|2*c*d|+|e*f| := add_le_add_left (abs_add_le _ _) _
    _ ≤ _ := by
      simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith only [h0,h1,h2]

def inner (L : ℝ → ℝ) (s : ℝ) : ℝ := L s*weight s
def innerFirst (L L1 : ℝ → ℝ) (s : ℝ) : ℝ := L1 s*weight s+L s*weightD1 s
def innerSecond (L L1 L2 : ℝ → ℝ) (s : ℝ) : ℝ :=
  L2 s*weight s+2*L1 s*weightD1 s+L s*weightD2 s

def kernel (L : ℝ → ℝ) (s : ℝ) : ℝ := logFactor s*inner L s
def first (L L1 : ℝ → ℝ) (s : ℝ) : ℝ :=
  logFirst s*inner L s+logFactor s*innerFirst L L1 s
def second (L L1 L2 : ℝ → ℝ) (s : ℝ) : ℝ :=
  logSecond s*inner L s+2*logFirst s*innerFirst L L1 s+logFactor s*innerSecond L L1 L2 s

theorem second_abs_le {L L1 L2 : ℝ → ℝ} {s : ℝ} (hs : 2 ≤ s) (he : s ≤ endpoint)
    (hL : |L s| ≤ 2) (hL1 : |L1 s| ≤ 2) (hL2 : |L2 s| ≤ 2) :
    |second L L1 L2 s| ≤ 26 := by
  obtain ⟨hw,hw1,hw2⟩ := weight_bounds hs he
  obtain ⟨hl,hl1,hl2⟩ := log_bounds hs he
  have hi : |inner L s| ≤ 2 := by
    unfold inner
    rw [abs_mul]
    simpa using mul_le_mul hL hw (abs_nonneg _) ((abs_nonneg _).trans hL)
  have hi1 : |innerFirst L L1 s| ≤ 4 := by
    exact (first_bound hL1 hw hL hw1).trans (by norm_num)
  have hi2 : |innerSecond L L1 L2 s| ≤ 8 := by
    exact (second_bound hL2 hw hL1 hw1 hL hw2).trans (by norm_num)
  exact (second_bound hl2 hi hl1 hi1 hl hi2).trans (by norm_num)

theorem inner_deriv {L L1 : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (hr : ClassicalSixthWeight.R-s ≠ 0)
    (hL : HasDerivAt L (L1 s) s) : HasDerivAt (inner L) (innerFirst L L1 s) s :=
  hL.mul (weight_deriv hs hr)

theorem innerFirst_deriv {L L1 L2 : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (hr : ClassicalSixthWeight.R-s ≠ 0)
    (hL : HasDerivAt L (L1 s) s) (hL1 : HasDerivAt L1 (L2 s) s) :
    HasDerivAt (innerFirst L L1) (innerSecond L L1 L2 s) s := by
  have h := (hL1.mul (weight_deriv hs hr)).add (hL.mul (weightD1_deriv hs hr))
  change HasDerivAt (innerFirst L L1) _ s at h
  apply h.congr_deriv
  dsimp [innerSecond]
  ring

theorem kernel_deriv {L L1 : ℝ → ℝ} {s : ℝ} (hs : 2 ≤ s) (hr : ClassicalSixthWeight.R-s ≠ 0)
    (hL : HasDerivAt L (L1 s) s) : HasDerivAt (kernel L) (first L L1 s) s :=
  (log_deriv hs).mul (inner_deriv (by linarith) hr hL)

theorem first_deriv {L L1 L2 : ℝ → ℝ} {s : ℝ} (hs : 2 ≤ s) (hr : ClassicalSixthWeight.R-s ≠ 0)
    (hL : HasDerivAt L (L1 s) s) (hL1 : HasDerivAt L1 (L2 s) s) :
    HasDerivAt (first L L1) (second L L1 L2 s) s := by
  have h := ((logFirst_deriv hs).mul (inner_deriv (by linarith) hr hL)).add
    ((log_deriv hs).mul (innerFirst_deriv (by linarith) hr hL hL1))
  change HasDerivAt (first L L1) _ s at h
  apply h.congr_deriv
  dsimp [second]
  ring

end WuPaper.ClassicalSixthKernel
#print axioms WuPaper.ClassicalSixthKernel.second_abs_le

#print axioms WuPaper.ClassicalSixthKernel.first_deriv
