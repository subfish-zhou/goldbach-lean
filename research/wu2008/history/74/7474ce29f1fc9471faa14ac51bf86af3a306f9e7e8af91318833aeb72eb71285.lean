import SrcFifthGainStaircase

namespace WuSource.SrcFifthGain
open Wu2008DoubleSieve WuTarget.Wu08FifthSource SharpMassBalance
open MeasureTheory Set Real
open scoped Interval
noncomputable section

private def coreClip (s : ℝ) : ℝ := max 2 (min 10 s)

private theorem core_clip_mem (s : ℝ) : coreClip s ∈ Icc (2 : ℝ) 10 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private theorem core_clip_eq {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 10) : coreClip s = s := by
  rw [coreClip, min_eq_right hs.2, max_eq_right hs.1]

private theorem clipped_antitone {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000) :
    Antitone (fun s => wuImprovementLimit false δ (coreClip s)) := by
  intro s t hst
  exact wuImprovementLimit_lower_antitone hδ (by linarith) (core_clip_mem s) (core_clip_mem t)
    (max_le_max le_rfl (min_le_min le_rfl hst))

private theorem clipped_bound {δ s : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000) :
    |wuImprovementLimit false δ (coreClip s)| ≤ wuImprovementLimit false δ 2 := by
  have hs := core_clip_mem s
  have hn := wuImprovementLimit_nonneg false hδ (by linarith) (by linarith [hs.1]) hs.2
  rw [abs_of_nonneg hn]
  exact wuImprovementLimit_lower_antitone hδ (by linarith) ⟨le_rfl, by norm_num⟩ hs hs.1

theorem actual_kernel_integrable {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000) :
    Integrable (profileKernel (wuImprovementLimit false δ)) := by
  have hi := profile_kernel_integrable (clipped_antitone hδ hd).measurable
    (fun _s _hs => clipped_bound hδ hd)
  have he : profileKernel (fun s => wuImprovementLimit false δ (coreClip s)) =
      profileKernel (wuImprovementLimit false δ) := by
    funext v
    by_cases hv : v ∈ fifthPairRegion
    · rw [profileKernel, profileKernel, indicator_of_mem hv, indicator_of_mem hv,
        core_clip_eq (parameter_in_core (triangle_parameter hv))]
    · simp [profileKernel, hv]
  rw [he] at hi
  exact hi

theorem actual_source_scalar {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000) :
    sourceGain (wuImprovementLimit false δ) =
      8*∫ s in s0..FifthClassicalShape.q, wuImprovementLimit false δ s*weight s :=
  source_eq_scalar (actual_kernel_integrable hδ hd)

theorem actual_source_le_moving {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000) :
    sourceGain (wuImprovementLimit false δ) ≤ fifthHOnlyIntegral δ := by
  rw [source_eq_triangle (actual_kernel_integrable hδ hd)]
  apply triangle_gain_uniform (actual_kernel_integrable hδ hd) hδ hd
  · intro s hs
    have hp := parameter_in_core hs
    exact wuImprovementLimit_nonneg false hδ (by linarith) (by linarith [hp.1]) hp.2
  · intro _s _hs
    exact le_rfl

theorem grid_le_actual_source {h : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000)
    (hc : ∀ j < 13, h (15+j) ≤ wuImprovementLimit false δ (node (15+j))) :
    gridGain h ≤ sourceGain (wuImprovementLimit false δ) := by
  rw [← source_staircase_eq_grid, source_eq_triangle (staircase_kernel_integrable h),
    source_eq_triangle (actual_kernel_integrable hδ hd)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply integral_mono (staircase_kernel_integrable h) (actual_kernel_integrable hδ hd)
  intro v
  by_cases hv : v ∈ fifthPairRegion
  · simp only [profileKernel, indicator_of_mem hv]
    exact div_le_div_of_nonneg_right (staircase_le_actual hδ hd hc (triangle_parameter hv))
      (zero_denominator_pos hv).le
  · simp [profileKernel, hv]

theorem original_h_thirteen_nodes {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000) :
    (8*∑ j ∈ Finset.range 13,
      cellWeight j*wuImprovementLimit false δ (node (15+j))) ≤
        sourceGain (wuImprovementLimit false δ) :=
  grid_le_actual_source hδ hd (fun _j _hj => le_rfl)

theorem actual_source_count {δ ε : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFdelta δ+sourceGain (wuImprovementLimit false δ)-ε)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤ (fifthPairCount N : ℝ) := by
  obtain ⟨T, hT, hcount⟩ := fifthH_actual_Fdelta_lower hδ hd hε
  have hg := actual_source_le_moving hδ hd
  have hsplit := fifthH_actual_integral_split hδ hd
  have hcoef : fifthPairFdelta δ+sourceGain (wuImprovementLimit false δ)-ε ≤
      fifthHFdelta δ-ε := by linarith only [hg, hsplit]
  refine ⟨T, hT, fun N hN he => ?_⟩
  have hm := (mul_le_mul_of_nonneg_right hcoef
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (hcount N hN he)
  simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hm

theorem replacement_quarter (base g : ℝ) :
    (base+PositiveCoreResume.fifthGain)/4+
      (g-PositiveCoreResume.fifthGain)/4 = (base+g)/4 := by ring

theorem suggested_threshold_count {h w : ℕ → ℝ}
    (hn : ∀ j < 13, 0 ≤ h (15+j))
    (hc : ∀ δ : ℝ, 0 < δ → δ ≤ 1/1000 →
      ∀ j < 13, h (15+j) ≤ wuImprovementLimit false δ (node (15+j)))
    (hw : ∀ j < 13, w j ≤ cellWeight j)
    (hg : (1/1000 : ℝ) ≤ directedGain h w)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin+1/1000-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (fifthPairCount N : ℝ) :=
  directed_threshold_count hn hc hw hg hε

end
end WuSource.SrcFifthGain
