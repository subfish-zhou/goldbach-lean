import MathlibNt.SieveTheory.LiLiuGoldbachG67Analytic

open Set MeasureTheory G67SumCoordinate
open scoped Interval
noncomputable section
namespace G67Analytic

/-- The original sum-fiber logarithm argument, with no deleted branches. -/
def weightArg (a b c d s : ℝ) : ℝ :=
  upper b c s * (s-lower a d s) / (lower a d s * (s-upper b c s))

theorem weightArg_ge_one {a b c d s : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hab : a ≤ b) (hcd : c ≤ d) (hs : s ∈ Icc (a+c) (b+d)) :
    1 ≤ weightArg a b c d s := by
  obtain ⟨hL,hLU,hU⟩ := fiber_bounds ha hc hab hcd hs
  have hS : 0 < s := by linarith [hs.1]
  apply (le_div_iff₀ (mul_pos hL hU)).2
  nlinarith [mul_nonneg hS.le (sub_nonneg.mpr hLU)]

theorem weightArg_continuousOn {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hab : a ≤ b) (hcd : c ≤ d) :
    ContinuousOn (weightArg a b c d) (Icc (a+c) (b+d)) := by
  have hL : Continuous (lower a d) := continuous_const.max (continuous_id.sub continuous_const)
  have hU : Continuous (upper b c) := continuous_const.min (continuous_id.sub continuous_const)
  exact (hU.mul (continuous_id.sub hL)).continuousOn.div
    (hL.mul (continuous_id.sub hU)).continuousOn (fun s hs => by
      obtain ⟨hp,_,hq⟩ := fiber_bounds ha hc hab hcd hs
      exact (mul_pos hp hq).ne')

/-- Log-free lower density of the entire original sum fiber. -/
def weightLower (n : ℕ) (a b c d s : ℝ) : ℝ := logLower n (weightArg a b c d s) / s

theorem weightLower_nonneg {a b c d s : ℝ} (n : ℕ) (ha : 0 < a) (hc : 0 < c)
    (hab : a ≤ b) (hcd : c ≤ d) (hs : s ∈ Icc (a+c) (b+d)) :
    0 ≤ weightLower n a b c d s := by
  exact div_nonneg (logLower_nonneg n (weightArg_ge_one ha hc hab hcd hs))
    (by linarith [hs.1])

theorem weightLower_le {a b c d s : ℝ} (n : ℕ) (ha : 0 < a) (hc : 0 < c)
    (hab : a ≤ b) (hcd : c ≤ d) (hs : s ∈ Icc (a+c) (b+d)) :
    weightLower n a b c d s ≤ weight a b c d s := by
  exact div_le_div_of_nonneg_right (logLower_le_log n (weightArg_ge_one ha hc hab hcd hs))
    (by linarith [hs.1])

theorem weightLower_continuousOn {a b c d : ℝ} (n : ℕ) (ha : 0 < a) (hc : 0 < c)
    (hab : a ≤ b) (hcd : c ≤ d) :
    ContinuousOn (weightLower n a b c d) (Icc (a+c) (b+d)) := by
  exact ((logLower_continuousOn n).comp (weightArg_continuousOn ha hc hab hcd)
    (fun s hs => weightArg_ge_one ha hc hab hcd hs)).div continuousOn_id
    (fun s hs => (show 0 < s by linarith [hs.1]).ne')

theorem profileLower_continuousOn (n : ℕ) :
    ContinuousOn (profileLower n) (Iic ((1/2 : ℝ)-2*(4/53 : ℝ))) := by
  have hc : Continuous (fun s : ℝ => ((1/2-s)-(4/53 : ℝ))/(4/53 : ℝ)) := by fun_prop
  exact ((logLower_continuousOn n).comp hc.continuousOn (fun s hs => by
    change 1 ≤ ((1/2-s)-(4/53 : ℝ))/(4/53 : ℝ)
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 4/53)).2
    have hh : s ≤ (1/2 : ℝ)-2*(4/53 : ℝ) := hs
    linarith)).div (continuousOn_const.sub continuousOn_id) (fun s hs => by
      change (1/2 : ℝ)-s ≠ 0
      have hh : s ≤ (1/2 : ℝ)-2*(4/53 : ℝ) := hs
      linarith)

/-- Pointwise product comparison has both multiplier signs justified. -/
theorem densityLower_le {a b c d s : ℝ} (n : ℕ) (ha : 0 < a) (hc : 0 < c)
    (hab : a ≤ b) (hcd : c ≤ d) (hs : s ∈ Icc (a+c) (b+d))
    (hcut : s ≤ (1/2 : ℝ)-2*(4/53 : ℝ)) :
    profileLower n s * weightLower n a b c d s ≤ profile s * weight a b c d s := by
  exact mul_le_mul (profileLower_le n hcut) (weightLower_le n ha hc hab hcd hs)
    (weightLower_nonneg n ha hc hab hcd hs) (le_max_left _ _)

/-- Integral comparison on any certified subinterval; its hypotheses are geometry,
not a carried numerical estimate. -/
theorem integral_densityLower_le {a b c d l r : ℝ} (n : ℕ)
    (ha : 0 < a) (hc : 0 < c) (hab : a ≤ b) (hcd : c ≤ d)
    (hlr : l ≤ r) (hleft : a+c ≤ l) (hright : r ≤ b+d)
    (hcut : r ≤ (1/2 : ℝ)-2*(4/53 : ℝ))
    (hprofile : ContinuousOn profile (Icc l r)) :
    (∫ s in l..r, profileLower n s * weightLower n a b c d s) ≤
      ∫ s in l..r, profile s * weight a b c d s := by
  have hsub : Icc l r ⊆ Icc (a+c) (b+d) := Icc_subset_Icc hleft hright
  have hcp : ContinuousOn (profileLower n) (Icc l r) :=
    (profileLower_continuousOn n).mono (fun s hs => hs.2.trans hcut)
  have hcw := (weightLower_continuousOn n ha hc hab hcd).mono hsub
  have hco := (weight_continuousOn ha hc hab hcd).mono hsub
  exact intervalIntegral.integral_mono_on hlr
    ((hcp.mul hcw).intervalIntegrable_of_Icc hlr)
    ((hprofile.mul hco).intervalIntegrable_of_Icc hlr)
    (fun s hs => densityLower_le n ha hc hab hcd (hsub hs) (hs.2.trans hcut))

/-- The log-free approximation retains the original half-square and the full
rectangle up to the exact vanishing cutoff. This is a lower bound, not equality. -/
def rationalIntegral (n : ℕ) : ℝ :=
  (1/2 : ℝ) * (∫ s in ((4/53 : ℝ)+(4/53 : ℝ))..((4/33 : ℝ)+(4/33 : ℝ)),
    profileLower n s * weightLower n (4/53) (4/33) (4/53) (4/33) s) +
  (∫ s in ((4/53 : ℝ)+(4/33 : ℝ))..((1/2 : ℝ)-2*(4/53 : ℝ)),
    profileLower n s * weightLower n (4/53) (4/33) (4/33) (3/11) s)

/-- Unconditional lower bound for the exact five-branch production object. -/
theorem rationalIntegral_le_piecewise (n : ℕ) :
    rationalIntegral n ≤ piecewiseIntegral := by
  have h6 := integral_densityLower_le (a := (4/53:ℝ)) (b := 4/33) (c := 4/53)
    (d := 4/33) (l := (4/53:ℝ)+4/53) (r := (4/33:ℝ)+4/33) n
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (profile_continuousOn.mono (Icc_subset_Icc le_rfl (by norm_num)))
  have h7 := integral_densityLower_le (a := (4/53:ℝ)) (b := 4/33) (c := 4/33)
    (d := 3/11) (l := (4/53:ℝ)+4/33) (r := (1/2:ℝ)-2*(4/53:ℝ)) n
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (profile_continuousOn.mono (Icc_subset_Icc (by norm_num) (by norm_num)))
  rw [← elementaryIntegral_eq_piecewise, elementaryIntegral_eq_truncated]
  exact add_le_add (mul_le_mul_of_nonneg_left h6 (by norm_num)) h7

/-- The early-branch formula for the lower fiber uses the same original argument. -/
theorem weightLower_first {a b c d s : ℝ} (n : ℕ)
    (hL : s ≤ a+d) (hU : s ≤ b+c) :
    weightLower n a b c d s = logLower n ((s-c)*(s-a)/(a*c))/s := by
  have hl : lower a d s = a := max_eq_left (by linarith)
  have hu : upper b c s = s-c := min_eq_right (by linarith)
  simp only [weightLower, weightArg, hl, hu, sub_sub_cancel]

/-- The middle branch is retained, not replaced by an early-branch surrogate. -/
theorem weightLower_middle {a b c d s : ℝ} (n : ℕ)
    (hL : s ≤ a+d) (hU : b+c ≤ s) :
    weightLower n a b c d s = logLower n (b*(s-a)/(a*(s-b)))/s := by
  have hl : lower a d s = a := max_eq_left (by linarith)
  have hu : upper b c s = b := min_eq_left (by linarith)
  simp only [weightLower, weightArg, hl, hu]

/-- The late branch remains present through the exact profile cutoff. -/
theorem weightLower_last {a b c d s : ℝ} (n : ℕ)
    (hL : a+d ≤ s) (hU : b+c ≤ s) :
    weightLower n a b c d s = logLower n (b*d/((s-d)*(s-b)))/s := by
  have hl : lower a d s = s-d := max_eq_right (by linarith)
  have hu : upper b c s = b := min_eq_left (by linarith)
  simp only [weightLower, weightArg, hl, hu, sub_sub_cancel]

end G67Analytic
