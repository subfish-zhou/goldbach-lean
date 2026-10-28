import MathlibNt.SieveTheory.LiLiuGoldbachG67SumFubini

open Set MeasureTheory
open scoped Interval
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section
namespace G67SumCoordinate

/-- The actual elementary kernel as a function of the sum coordinate. -/
def profile (s : ℝ) : ℝ :=
  max 0 (Real.log (((1/2-s)-(4/53 : ℝ))/(4/53 : ℝ))/(1/2-s))

/-- Strict denominator and logarithm-domain bounds on both actual sum ranges. -/
theorem profile_domain {s : ℝ} (hs : s ≤ (4/33 : ℝ)+(3/11 : ℝ)) :
    0 < (1/2 : ℝ)-s ∧ 0 < ((1/2-s)-(4/53 : ℝ))/(4/53 : ℝ) := by
  constructor
  · linarith
  · apply div_pos _ (by norm_num)
    linarith

/-- Continuity of the actual profile on the whole compact sum range. -/
theorem profile_continuousOn :
    ContinuousOn profile (Icc ((4/53 : ℝ)+(4/53 : ℝ)) ((4/33 : ℝ)+(3/11 : ℝ))) := by
  have hD : Continuous (fun s : ℝ => (1/2 : ℝ)-s) := continuous_const.sub continuous_id
  have hA : Continuous (fun s : ℝ => ((1/2-s)-(4/53 : ℝ))/(4/53 : ℝ)) :=
    (hD.sub continuous_const).div_const _
  exact ContinuousOn.sup continuousOn_const
    ((hA.continuousOn.log (fun s hs => (profile_domain hs.2).2.ne')).div
      hD.continuousOn (fun s hs => (profile_domain hs.2).1.ne'))

/-- Literal equality to the imported original elementary kernel, not a replacement definition. -/
theorem profile_add (u v : ℝ) :
    profile (u+v) = G67ElementaryIntegral.elementaryKernel (u,v) := by
  unfold profile G67ElementaryIntegral.elementaryKernel
  rw [show (1/2 : ℝ)-(u+v) = 1/2-u-v by ring]

/-- The elementary logarithm vanishes above the exact cutoff, within the actual domain. -/
theorem profile_zero {s : ℝ} (hs : (1/2 : ℝ)-2*(4/53 : ℝ) ≤ s)
    (hupper : s ≤ (4/33 : ℝ)+(3/11 : ℝ)) : profile s = 0 := by
  have hd := profile_domain hupper
  have harg : ((1/2-s)-(4/53 : ℝ))/(4/53 : ℝ) ≤ 1 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4/53)).mpr
    linarith
  apply max_eq_left
  exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hd.2.le harg) hd.1.le

/-- A genuine one-dimensional expression for the original half-square plus rectangle. -/
def oneDimensionalIntegral : ℝ :=
  (1/2 : ℝ) * (∫ s in ((4/53 : ℝ)+(4/53 : ℝ))..((4/33 : ℝ)+(4/33 : ℝ)),
    profile s * weight (4/53) (4/33) (4/53) (4/33) s) +
  (∫ s in ((4/53 : ℝ)+(4/33 : ℝ))..((4/33 : ℝ)+(3/11 : ℝ)),
    profile s * weight (4/53) (4/33) (4/33) (3/11) s)

/-- Exact specialization: both original rectangles and the half-square factor are preserved. -/
theorem elementaryIntegral_eq_oneDimensional :
    G67ElementaryIntegral.elementaryIntegral = oneDimensionalIntegral := by
  have h6 := rectangle_sum_formula (φ := profile) (a := (4/53 : ℝ)) (b := 4/33)
    (c := 4/53) (d := 4/33) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (profile_continuousOn.mono (by intro s hs; constructor <;> linarith [hs.1,hs.2]))
  have h7 := rectangle_sum_formula (φ := profile) (a := (4/53 : ℝ)) (b := 4/33)
    (c := 4/33) (d := 3/11) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (profile_continuousOn.mono (by intro s hs; constructor <;> linarith [hs.1,hs.2]))
  simp_rw [profile_add] at h6 h7
  unfold G67ElementaryIntegral.elementaryIntegral oneDimensionalIntegral
  rw [h6,h7]


end G67SumCoordinate
