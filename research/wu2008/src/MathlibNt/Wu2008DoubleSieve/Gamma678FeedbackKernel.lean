import MathlibNt.Wu2008DoubleSieve.Gamma678FeedbackGeometry

/-! Guarded explicit logarithmic kernels and their genuine geometric slices. -/
namespace Wu2008DoubleSieve.Gamma678Feedback
open Real Set MeasureTheory
open scoped Classical Topology Interval

noncomputable def density (j : Kind) (v t : ℝ) : ℝ := 1 / (v * t * invU j v t)
noncomputable def masked (j : Kind) (v t : ℝ) : ℝ :=
  if slice j v t then density j v t else 0
noncomputable def pref : Kind → ℝ → ℝ
  | .six, v => 1 / (v * gamma5FeedbackW v)
  | .seven, v => 1 / v
  | .eight, v => 1 / v
noncomputable def Q (j : Kind) (v : ℝ) : ℝ :=
  pref j v * log (U j v * invU j v (L j v) / (L j v * invU j v (U j v)))
noncomputable def K (j : Kind) (v : ℝ) : ℝ :=
  if 1 ≤ v ∧ v ≤ 3 ∧ L j v < U j v then Q j v else 0
noncomputable def K6 := K .six
noncomputable def K7 := K .seven
noncomputable def K8 := K .eight

theorem positive_endpoints (j : Kind) {v : ℝ} (hv : v ∈ Icc (1 : ℝ) 3)
    (h : L j v ≤ U j v) :
    0 < L j v ∧ 0 < U j v ∧ 0 < invU j v (L j v) ∧ 0 < invU j v (U j v) := by
  have hL := slice_bounds ((slice_iff j hv (L j v)).mpr ⟨le_rfl, h⟩)
  have hU := slice_bounds ((slice_iff j hv (U j v)).mpr ⟨h, le_rfl⟩)
  exact ⟨constants.1.trans_le hL.2.1.1, constants.1.trans_le hU.2.1.1,
    constants.1.trans_le hL.2.2.1, constants.1.trans_le hU.2.2.1⟩

theorem log_argument_pos (j : Kind) {v : ℝ} (hv : v ∈ Icc (1 : ℝ) 3)
    (h : L j v ≤ U j v) :
    0 < U j v * invU j v (L j v) / (L j v * invU j v (U j v)) := by
  obtain ⟨hL, hU, huL, huU⟩ := positive_endpoints j hv h
  exact div_pos (mul_pos hU huL) (mul_pos hL huU)

/-- The ratio primitive has coefficient 1/v, with no additional v+1 factor. -/
theorem ratio_primitive {v A B : ℝ} (hv : 0 < v + 1)
    (hA : 0 < A) (hAB : A ≤ B) (hB : 0 < 1 - (v + 1) * B) :
    (∫ t in A..B, 1 / (v * t * (1 - (v + 1) * t))) =
      (1 / v) * log (B * (1 - (v + 1) * A) / (A * (1 - (v + 1) * B))) := by
  have hc : B < 1 / (v + 1) := (lt_div_iff₀ hv).mpr (by nlinarith)
  have he (t : ℝ) : 1 / (v * t * (1 - (v + 1) * t)) =
      (1 / v) * firstFeedbackWeightedKernel (1 / (v + 1)) t := by
    dsimp [firstFeedbackWeightedKernel]
    field_simp
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, firstFeedbackWeightedKernel_integral hA hAB hc]
  congr 2
  field_simp

theorem slice_primitive (j : Kind) {v : ℝ} (hv : v ∈ Icc (1 : ℝ) 3)
    (h : L j v ≤ U j v) : (∫ t in L j v..U j v, density j v t) = Q j v := by
  obtain ⟨hL, _, _, huU⟩ := positive_endpoints j hv h
  have hq : 0 < v + 1 := by linarith [hv.1]
  cases j
  · exact gamma5Feedback_density_integral hL h (by
      change 0 < gamma5FeedbackW v - U .six v at huU
      linarith)
  · exact ratio_primitive hq hL h huU
  · exact ratio_primitive hq hL h huU

theorem masked_outside (j : Kind) {v : ℝ} (hv : v ∉ Icc (1 : ℝ) 3) (t : ℝ) :
    masked j v t = 0 := if_neg (fun h => hv (slice_unit h))

theorem slice_integral (j : Kind) (v : ℝ) : (∫ t : ℝ, masked j v t) = K j v := by
  by_cases hv : v ∈ Icc (1 : ℝ) 3
  · have he (t : ℝ) : masked j v t =
        if L j v ≤ t ∧ t ≤ U j v then density j v t else 0 := by
      simp only [masked, slice_iff j hv]
    simp_rw [he]
    by_cases h : L j v < U j v
    · rw [gamma5Feedback_mask_interval _ h.le, slice_primitive j hv h.le,
        K, if_pos ⟨hv.1, hv.2, h⟩]
    · rw [gamma5Feedback_mask_zero _ (le_of_not_gt h), K,
        if_neg (fun hh => h hh.2.2)]
  · have hn : ¬(1 ≤ v ∧ v ≤ 3 ∧ L j v < U j v) := fun h => hv ⟨h.1, h.2.1⟩
    simp only [masked_outside j hv, integral_zero, K, if_neg hn]

theorem kernel_outside (j : Kind) {v : ℝ} (hv : v ∉ Icc (1 : ℝ) 3) : K j v = 0 :=
  if_neg (fun h => hv ⟨h.1, h.2.1⟩)

theorem kernel_zero_width (j : Kind) {v : ℝ} (h : U j v ≤ L j v) : K j v = 0 :=
  if_neg (fun hh => not_lt_of_ge h hh.2.2)

end Wu2008DoubleSieve.Gamma678Feedback
