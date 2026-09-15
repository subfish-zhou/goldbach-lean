import PositiveCoreFullCross

namespace PositiveCoreResume
open Wu2008DoubleSieve Set MeasureTheory Real
noncomputable section

/-- The fixed original exponent, capped only at the proved cross endpoint 4. -/
def fifthProfile (v : ℝ × ℝ) : ℝ :=
  (11/2 - max 4 (truncatedSixthLowerS 0 v.1 v.2))^3/70875

def fullSeed : ℝ := (11/2-5)^3/70875

def fifthMinorant (v : ℝ × ℝ) : ℝ :=
  fifthPairRegion.indicator (fun v => fifthProfile v /
    (v.1*v.2*(truncatedSixthLowerC 0-v.1-v.2))) v

/-- Original full triangle and original delta-zero reciprocal weight. No new mesh or cut. -/
def fifthGain : ℝ := 4 * ∫ v : ℝ × ℝ, fifthMinorant v

 theorem profile_seed {v : ℝ × ℝ} (hv : v ∈ fifthPairRegion) :
    fullSeed ≤ fifthProfile v := by
  have hb := fifthPair_region_bounds (δ := 0) le_rfl (by norm_num) hv
  have hm : max 4 (truncatedSixthLowerS 0 v.1 v.2) ≤ 5 :=
    max_le (by norm_num) hb.2.2.2.2
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 11/2-5)
    (show 11/2-5 ≤ 11/2-max 4 (truncatedSixthLowerS 0 v.1 v.2) by linarith) 3
  exact div_le_div_of_nonneg_right hh (by norm_num)

theorem fullSeed_pos : 0 < fullSeed := by norm_num [fullSeed]

theorem profile_lower {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000)
    {v : ℝ × ℝ} (hv : v ∈ fifthPairRegion) :
    fifthProfile v ≤ wuImprovementLimit false δ (truncatedSixthLowerS δ v.1 v.2) := by
  have hb := fifthPair_region_bounds hδ.le hd hv
  have h0 := fifthPair_region_bounds (δ := 0) le_rfl (by norm_num) hv
  have hs : truncatedSixthLowerS δ v.1 v.2 ≤ truncatedSixthLowerS 0 v.1 v.2 := by
    unfold truncatedSixthLowerS truncatedSixthLowerC
    apply div_le_div_of_nonneg_right _ truncatedSixthLower_parameters.1.le
    linarith
  have ht : max 4 (truncatedSixthLowerS 0 v.1 v.2) ≤ 5 := max_le (by norm_num) h0.2.2.2.2
  have hl := h_full_cross hδ hd (le_max_left 4 (truncatedSixthLowerS 0 v.1 v.2))
    (ht.trans (by norm_num))
  exact hl.trans (wuImprovementLimit_lower_antitone hδ (by linarith)
    ⟨hb.2.2.2.1, hb.2.2.2.2.trans (by norm_num)⟩
    ⟨(by norm_num : (2 : ℝ) ≤ 4).trans (le_max_left _ _), ht.trans (by norm_num)⟩
    (hs.trans (le_max_right _ _)))

theorem minorant_integrable : Integrable fifthMinorant := by
  have hc : Continuous fifthProfile := by
    unfold fifthProfile truncatedSixthLowerS truncatedSixthLowerC
    fun_prop
  have hd : ContinuousOn (fun v : ℝ × ℝ =>
      v.1*v.2*(truncatedSixthLowerC 0-v.1-v.2)) fifthPairRegion := by fun_prop
  have hz : ∀ v ∈ fifthPairRegion,
      v.1*v.2*(truncatedSixthLowerC 0-v.1-v.2) ≠ 0 := by
    intro v hv
    have hb := fifthPair_region_bounds (δ := 0) le_rfl (by norm_num) hv
    exact (mul_pos (mul_pos hb.1 hb.2.1) (by linarith [hb.2.2.1, truncatedSixthLower_parameters.1])).ne'
  exact (ContinuousOn.integrableOn_compact fifthPair_region_compact
    (hc.continuousOn.div hd hz)).integrable_indicator fifthPair_region_compact.measurableSet

theorem minorant_le_actual {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000) (v : ℝ × ℝ) :
    fifthMinorant v ≤ fifthHOnlyKernel δ v := by
  by_cases hv : v ∈ fifthPairRegion
  · rw [fifthMinorant, indicator_of_mem hv, fifthHOnlyKernel, if_pos hv]
    have hb := fifthH_denominator_bounds hδ hd hv
    have h0 := fifthPair_region_bounds (δ := 0) le_rfl (by norm_num) hv
    have hn := fullSeed_pos.le.trans (profile_seed hv)
    have hden : v.1*v.2*(truncatedSixthLowerC δ-v.1-v.2) ≤
        v.1*v.2*(truncatedSixthLowerC 0-v.1-v.2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg h0.1.le h0.2.1.le)
      unfold truncatedSixthLowerC; linarith
    exact (div_le_div_of_nonneg_left hn hb.1 hden).trans
      (div_le_div_of_nonneg_right (profile_lower hδ hd hv) hb.1.le)
  · simp [fifthMinorant, fifthHOnlyKernel, hv]

/-- This genuinely improves the positive fifth input, not an upper enclosure of Q. -/
theorem fifth_gain_uniform {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000) :
    fifthGain ≤ fifthHOnlyIntegral δ := by
  have h := integral_mono minorant_integrable (fifthH_only_integrable hδ hd)
    (minorant_le_actual hδ hd)
  unfold fifthGain fifthHOnlyIntegral
  linarith

/-- A coarse rational certificate only for strictness; fifthGain itself keeps the full weight. -/
theorem fifth_gain_seed_lower :
    4*fullSeed*(truncatedSixthLowerBeta-truncatedSixthLowerAlpha)^2 ≤ fifthGain := by
  have hi : Integrable (fifthPairRegion.indicator (fun _ : ℝ × ℝ => 2*fullSeed)) :=
    (integrableOn_const fifthPair_region_compact.measure_lt_top.ne).integrable_indicator
      fifthPair_region_compact.measurableSet
  have hm := integral_mono hi minorant_integrable (fun v => by
    by_cases hv : v ∈ fifthPairRegion
    · rw [indicator_of_mem hv, fifthMinorant, indicator_of_mem hv]
      have hb := fifthPair_region_bounds (δ := 0) le_rfl (by norm_num) hv
      have hxy : v.1*v.2 ≤ 1 := by
        have hx : v.1 ≤ 1 := by
          have hh := hv.2.1.trans hv.2.2
          norm_num [truncatedSixthLowerBeta] at hh ⊢; linarith
        have hy : v.2 ≤ 1 := by
          have hh := hv.2.2
          norm_num [truncatedSixthLowerBeta] at hh ⊢; linarith
        exact (mul_le_mul hx hy hb.2.1.le (by norm_num)).trans_eq (by ring)
      have hz : 0 < truncatedSixthLowerC 0-v.1-v.2 := by linarith [hb.2.2.1, truncatedSixthLower_parameters.1]
      have hden : v.1*v.2*(truncatedSixthLowerC 0-v.1-v.2) ≤ 1/2 := by
        have hm := mul_le_mul_of_nonneg_right hxy hz.le
        norm_num [truncatedSixthLowerC] at hm ⊢
        nlinarith [hb.1,hb.2.1]
      apply (le_div_iff₀ (mul_pos (mul_pos hb.1 hb.2.1) hz)).mpr
      have hm := mul_le_mul_of_nonneg_left hden (show 0 ≤ 2*fullSeed from mul_nonneg (by norm_num) fullSeed_pos.le)
      linarith [profile_seed hv]
    · simp [fifthMinorant, hv])
  rw [fifthH_triangle_constant] at hm
  unfold fifthGain
  linarith

theorem gain_strict : fifthHGain < fifthGain := by
  have hs : fifthHSeed < fullSeed := by norm_num [fifthHSeed,fullSeed]
  have hh := mul_lt_mul_of_pos_right hs
    (sq_pos_of_pos (sub_pos.mpr truncatedSixthLower_parameters.2.1))
  have hl := fifth_gain_seed_lower
  unfold fifthHGain
  linarith

/-- Only the classical Fdelta uses continuity in delta. The full new h gain is uniform. -/
theorem fifth_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin+fifthGain-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (fifthPairCount N : ℝ) := by
  obtain ⟨δ,hδ,hd,hclose⟩ := fifthPair_Fdelta_close (half_pos hε)
  obtain ⟨T,hT,hcount⟩ := fifthH_actual_Fdelta_lower hδ hd (half_pos hε)
  have hc := (abs_lt.mp hclose).1
  have hg := fifth_gain_uniform hδ hd
  have hsplit := fifthH_actual_integral_split hδ hd
  have hcoef : fifthPairFlin+fifthGain-ε ≤ fifthHFdelta δ-ε/2 := by linarith
  refine ⟨T,hT,fun N hN he => ?_⟩
  have hm := (mul_le_mul_of_nonneg_right hcoef
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (hcount N hN he)
  simpa only [truncatedSixthMassScale,mul_div_assoc,mul_assoc] using hm

end
end PositiveCoreResume
