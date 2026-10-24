import WR2ClassicalSixthBranch
import WR2ClassicalFourthWeight

noncomputable section
namespace WuPaper.ClassicalFifthBranch
open Real Set ClassicalSixthBranch
open WuSource.SrcSixthGain

def endpoint : ℝ := ClassicalSixthBranch.R-2
def lower (s : ℝ) : ℝ := log (r/v s)
def upper (s : ℝ) : ℝ := log (u s)
def lowerD1 (s : ℝ) : ℝ := 1/v s
def upperD1 (s : ℝ) : ℝ := -1/u s
def lowerD2 (s : ℝ) : ℝ := 1/(v s)^2
def upperD2 (s : ℝ) : ℝ := -1/(u s)^2

theorem lower_geometry {s : ℝ} (hs : split ≤ s) (he : s ≤ WuSource.SrcSixthGain.endpoint) :
    1 ≤ v s ∧ v s ≤ r := by
  refine ⟨(geometry he).2,?_⟩
  norm_num [v,ClassicalSixthBranch.R,r,split,QuarterTrim.alpha,QuarterTrim.beta] at hs ⊢
  linarith

theorem upper_geometry {s : ℝ} (hs : WuSource.SrcSixthGain.endpoint ≤ s) (he : s ≤ endpoint) :
    1 ≤ u s ∧ u s ≤ r := by
  norm_num [u,ClassicalSixthBranch.R,r,endpoint,WuSource.SrcSixthGain.endpoint,QuarterTrim.alpha,QuarterTrim.beta] at hs he ⊢
  constructor <;> linarith

theorem lower_bounds {s : ℝ} (hs : split ≤ s) (he : s ≤ WuSource.SrcSixthGain.endpoint) :
    0 ≤ lower s ∧ |lower s| ≤ 1 := by
  have h := lower_geometry hs he
  have hv : 0 < v s := by linarith
  have hq : 1 ≤ r/v s := (le_div_iff₀ hv).mpr (by linarith [h.2])
  have hq2 : r/v s ≤ 2 := (div_le_iff₀ hv).mpr (by norm_num [r] at h ⊢; linarith [h.1])
  have hn := log_nonneg hq
  refine ⟨hn,?_⟩
  rw [lower,abs_of_nonneg hn]
  exact (log_le_sub_one_of_pos (by linarith : 0 < r/v s)).trans (by linarith)

theorem upper_bounds {s : ℝ} (hs : WuSource.SrcSixthGain.endpoint ≤ s) (he : s ≤ endpoint) :
    0 ≤ upper s ∧ |upper s| ≤ 1 := by
  have h := upper_geometry hs he
  have hn := log_nonneg h.1
  refine ⟨hn,?_⟩
  rw [upper,abs_of_nonneg hn]
  have hp : 0 < u s := by linarith [h.1]
  have hr : r ≤ 2 := by norm_num [r]
  exact (log_le_sub_one_of_pos hp).trans (by linarith [h.2])

theorem lower_deriv {s : ℝ} (he : s ≤ WuSource.SrcSixthGain.endpoint) :
    HasDerivAt lower (lowerD1 s) s := by
  have hv : v s ≠ 0 := by linarith [(geometry he).2]
  have hr : r ≠ 0 := by norm_num [r]
  have h := ((hasDerivAt_const s r).div (v_deriv s) hv).log (div_ne_zero hr hv)
  change HasDerivAt lower _ s at h
  apply h.congr_deriv
  dsimp [lowerD1,Pi.div_apply]
  field_simp [hv,hr]
  ring

theorem upper_deriv {s : ℝ} (he : s ≤ endpoint) : HasDerivAt upper (upperD1 s) s := by
  have hu : u s ≠ 0 := by dsimp [u,endpoint] at he ⊢; linarith
  exact (u_deriv s).log hu

theorem lowerD1_deriv {s : ℝ} (he : s ≤ WuSource.SrcSixthGain.endpoint) :
    HasDerivAt lowerD1 (lowerD2 s) s := by
  have hv : v s ≠ 0 := by linarith [(geometry he).2]
  have h := (hasDerivAt_const s (1:ℝ)).div (v_deriv s) hv
  change HasDerivAt lowerD1 _ s at h
  apply h.congr_deriv
  dsimp [lowerD2]
  ring

theorem upperD1_deriv {s : ℝ} (he : s ≤ endpoint) : HasDerivAt upperD1 (upperD2 s) s := by
  have hu : u s ≠ 0 := by dsimp [u,endpoint] at he ⊢; linarith
  have h := (hasDerivAt_const s (-1:ℝ)).div (u_deriv s) hu
  change HasDerivAt upperD1 _ s at h
  apply h.congr_deriv
  dsimp [upperD2]
  ring

private theorem inv_bounds {x : ℝ} (hx : 1 ≤ x) : |1/x| ≤ 1 ∧ |1/x^2| ≤ 1 := by
  have hp : 0 < x := by linarith
  have hi0 : 0 ≤ x⁻¹ := (inv_pos.mpr hp).le
  have hi : x⁻¹ ≤ 1 := by rw [← one_div]; exact (div_le_iff₀ hp).mpr (by linarith)
  constructor
  · simpa [one_div,abs_of_nonneg hi0] using hi
  · simpa [one_div,← inv_pow,abs_of_nonneg (sq_nonneg (x⁻¹))] using pow_le_pow_left₀ hi0 hi 2

theorem lower_derivative_bounds {s : ℝ} (he : s ≤ WuSource.SrcSixthGain.endpoint) :
    |lowerD1 s| ≤ 1 ∧ |lowerD2 s| ≤ 1 := inv_bounds (geometry he).2

theorem upper_derivative_bounds {s : ℝ} (he : s ≤ endpoint) : |upperD1 s| ≤ 1 ∧ |upperD2 s| ≤ 1 := by
  have hu : 1 ≤ u s := by dsimp [u,endpoint] at he ⊢; linarith
  simpa [upperD1,upperD2,neg_div,abs_neg] using inv_bounds hu

end WuPaper.ClassicalFifthBranch
#print axioms WuPaper.ClassicalFifthBranch.lower_bounds
#print axioms WuPaper.ClassicalFifthBranch.upper_bounds
#print axioms WuPaper.ClassicalFifthBranch.lowerD1_deriv
#print axioms WuPaper.ClassicalFifthBranch.upper_derivative_bounds
