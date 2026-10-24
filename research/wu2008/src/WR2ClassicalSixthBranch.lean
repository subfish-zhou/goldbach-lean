import WR2ClassicalSixthLogLower

noncomputable section
namespace WuPaper.ClassicalSixthBranch
open Real Set
open WuSource.SrcSixthGain

def R : ℝ := 1327/200
def r : ℝ := 1327/824
def u (s : ℝ) : ℝ := R-1-s
def v (s : ℝ) : ℝ := R-r-s
def lower (s : ℝ) : ℝ := log (r*u s/v s)
def upper (s : ℝ) : ℝ := log (u s*v s/r)
def lowerD1 (s : ℝ) : ℝ := -1/u s+1/v s
def upperD1 (s : ℝ) : ℝ := -1/u s-1/v s
def lowerD2 (s : ℝ) : ℝ := -1/(u s)^2+1/(v s)^2
def upperD2 (s : ℝ) : ℝ := -1/(u s)^2-1/(v s)^2

theorem geometry {s : ℝ} (hs : s ≤ endpoint) : r ≤ u s ∧ 1 ≤ v s := by
  norm_num [u,v,R,r,endpoint,QuarterTrim.alpha,QuarterTrim.beta] at hs ⊢
  constructor <;> linarith

theorem lower_literal {s : ℝ} (hs : s ≤ endpoint) :
    lower s = log r+log (u s)-log (v s) := by
  have h := geometry hs
  have hr : 0 < r := by norm_num [r]
  rw [lower,log_div (mul_pos hr (hr.trans_le h.1)).ne' (by linarith : v s ≠ 0),
    log_mul hr.ne' (hr.trans_le h.1).ne']

theorem upper_literal {s : ℝ} (hs : s ≤ endpoint) :
    upper s = log (u s)+log (v s)-log r := by
  have h := geometry hs
  have hr : 0 < r := by norm_num [r]
  have hu := hr.trans_le h.1
  have hv : 0 < v s := by linarith
  rw [upper,log_div (mul_pos hu hv).ne' hr.ne',log_mul hu.ne' hv.ne']

theorem lower_bounds {s : ℝ} (hs : s ≤ split) : |lower s| ≤ 2 := by
  have he : s ≤ endpoint := hs.trans (by norm_num [split,endpoint,QuarterTrim.alpha,QuarterTrim.beta])
  have h := geometry he
  have hv : 0 < v s := by linarith
  have hr : 1 ≤ r := by norm_num [r]
  have huv : v s ≤ u s := by dsimp [u,v]; linarith
  have hq1 : 1 ≤ r*u s/v s := by
    apply (le_div_iff₀ hv).mpr
    nlinarith [mul_le_mul_of_nonneg_right hr (show 0 ≤ u s by linarith [h.1])]
  have hq3 : r*u s/v s ≤ 3 := by
    apply (div_le_iff₀ hv).mpr
    norm_num [u,v,R,r,split,QuarterTrim.alpha,QuarterTrim.beta] at hs ⊢
    linarith
  rw [lower,abs_of_nonneg (log_nonneg hq1)]
  exact (log_le_sub_one_of_pos (by linarith : 0 < r*u s/v s)).trans (by linarith)

theorem upper_bounds {s : ℝ} (hs : split ≤ s) (he : s ≤ endpoint) : |upper s| ≤ 2 := by
  have h := geometry he
  have hr : 0 < r := by norm_num [r]
  have hv : 0 ≤ v s := by linarith
  have hu : u s ≤ 2*r-1 := by
    norm_num [u,R,r,split,QuarterTrim.alpha,QuarterTrim.beta] at hs ⊢
    linarith
  have hvhi : v s ≤ r := by
    norm_num [v,R,r,split,QuarterTrim.alpha,QuarterTrim.beta] at hs ⊢
    linarith
  have hq1 : 1 ≤ u s*v s/r := by
    apply (le_div_iff₀ hr).mpr
    nlinarith [mul_le_mul h.1 h.2 (by norm_num : (0:ℝ) ≤ 1) (by linarith : 0 ≤ u s)]
  have hq3 : u s*v s/r ≤ 3 := by
    apply (div_le_iff₀ hr).mpr
    have hh := mul_le_mul hu hvhi hv (by norm_num [r] : 0 ≤ 2*r-1)
    norm_num [r] at hh ⊢
    linarith
  rw [upper,abs_of_nonneg (log_nonneg hq1)]
  exact (log_le_sub_one_of_pos (by linarith : 0 < u s*v s/r)).trans (by linarith)

theorem derivative_bounds {s : ℝ} (hs : s ≤ endpoint) :
    |lowerD1 s| ≤ 2 ∧ |upperD1 s| ≤ 2 ∧ |lowerD2 s| ≤ 2 ∧ |upperD2 s| ≤ 2 := by
  have h := geometry hs
  have hr : 1 ≤ r := by norm_num [r]
  have hu : 0 < u s := by linarith [h.1]
  have hv : 0 < v s := by linarith [h.2]
  have ha0 : 0 ≤ (u s)⁻¹ := (inv_pos.mpr hu).le
  have hb0 : 0 ≤ (v s)⁻¹ := (inv_pos.mpr hv).le
  have ha : (u s)⁻¹ ≤ 1 := by rw [← one_div]; apply (div_le_iff₀ hu).mpr; linarith [h.1]
  have hb : (v s)⁻¹ ≤ 1 := by rw [← one_div]; apply (div_le_iff₀ hv).mpr; linarith [h.2]
  have ha2 := pow_le_pow_left₀ ha0 ha 2
  have hb2 := pow_le_pow_left₀ hb0 hb 2
  simp only [lowerD1,upperD1,lowerD2,upperD2,neg_div,one_div,← inv_pow]
  repeat' constructor
  all_goals apply abs_le.mpr
  all_goals constructor <;> nlinarith only [ha,hb,ha0,hb0,ha2,hb2,sq_nonneg ((u s)⁻¹),sq_nonneg ((v s)⁻¹)]

theorem u_deriv (s : ℝ) : HasDerivAt u (-1) s :=
  (hasDerivAt_id s).const_sub (R-1)
theorem v_deriv (s : ℝ) : HasDerivAt v (-1) s :=
  (hasDerivAt_id s).const_sub (R-r)

theorem lower_deriv {s : ℝ} (hs : s ≤ endpoint) : HasDerivAt lower (lowerD1 s) s := by
  have hg := geometry hs
  have hr : 0 < r := by norm_num [r]
  have hu : u s ≠ 0 := (hr.trans_le hg.1).ne'
  have hv : v s ≠ 0 := by linarith [hg.2]
  have h := (((u_deriv s).const_mul r).div (v_deriv s) hv).log
    (div_ne_zero (mul_ne_zero hr.ne' hu) hv)
  change HasDerivAt lower _ s at h
  apply h.congr_deriv
  unfold lowerD1
  dsimp only [Pi.div_apply,Pi.mul_apply]
  field_simp [hu,hv,hr.ne']
  ring

theorem upper_deriv {s : ℝ} (hs : s ≤ endpoint) : HasDerivAt upper (upperD1 s) s := by
  have hg := geometry hs
  have hr : 0 < r := by norm_num [r]
  have hu : u s ≠ 0 := (hr.trans_le hg.1).ne'
  have hv : v s ≠ 0 := by linarith [hg.2]
  have h := (((u_deriv s).mul (v_deriv s)).div_const r).log
    (div_ne_zero (mul_ne_zero hu hv) hr.ne')
  change HasDerivAt upper _ s at h
  apply h.congr_deriv
  unfold upperD1
  dsimp only [Pi.div_apply,Pi.mul_apply]
  field_simp [hu,hv,hr.ne']
  ring

theorem lowerD1_deriv {s : ℝ} (hs : s ≤ endpoint) : HasDerivAt lowerD1 (lowerD2 s) s := by
  have hg := geometry hs
  have hr : 0 < r := by norm_num [r]
  have hu : u s ≠ 0 := (hr.trans_le hg.1).ne'
  have hv : v s ≠ 0 := by linarith [hg.2]
  have h := ((hasDerivAt_const s (-1:ℝ)).div (u_deriv s) hu).add
    ((hasDerivAt_const s (1:ℝ)).div (v_deriv s) hv)
  change HasDerivAt lowerD1 _ s at h
  apply h.congr_deriv
  dsimp [lowerD2]
  ring

theorem upperD1_deriv {s : ℝ} (hs : s ≤ endpoint) : HasDerivAt upperD1 (upperD2 s) s := by
  have hg := geometry hs
  have hr : 0 < r := by norm_num [r]
  have hu : u s ≠ 0 := (hr.trans_le hg.1).ne'
  have hv : v s ≠ 0 := by linarith [hg.2]
  have h := ((hasDerivAt_const s (-1:ℝ)).div (u_deriv s) hu).sub
    ((hasDerivAt_const s (1:ℝ)).div (v_deriv s) hv)
  change HasDerivAt upperD1 _ s at h
  apply h.congr_deriv
  dsimp [upperD2]
  ring

end WuPaper.ClassicalSixthBranch
#print axioms WuPaper.ClassicalSixthBranch.lower_bounds
#print axioms WuPaper.ClassicalSixthBranch.upper_bounds
#print axioms WuPaper.ClassicalSixthBranch.derivative_bounds

#print axioms WuPaper.ClassicalSixthBranch.lower_deriv
#print axioms WuPaper.ClassicalSixthBranch.upperD1_deriv
