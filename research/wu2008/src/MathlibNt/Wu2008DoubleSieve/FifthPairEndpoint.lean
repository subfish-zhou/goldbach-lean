import MathlibNt.Wu2008DoubleSieve.FifthPairLower
namespace Wu2008DoubleSieve
open Set Real Filter MeasureTheory
open scoped Classical Topology

noncomputable def fifthPairExtension (δ : ℝ) : ℝ :=
  4 * ∫ v in fifthPairRegion, fifthPairRegular δ v

theorem fifthPair_extension_continuous : Continuous fifthPairExtension :=
  (continuous_parametric_integral_of_continuous fifthPair_regular_continuous
    fifthPair_region_compact).const_mul 4

theorem fifthPair_extension_eq {δ : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 1000) :
    fifthPairExtension δ = fifthPairFdelta δ := by
  rw [fifthPair_literal_integral hδ hδhi, fifthPair_kernel_regular hδ hδhi,
    integral_indicator fifthPair_region_compact.isClosed.measurableSet]
  rfl

/-- Only the classical continuous coefficient is varied with delta. -/
theorem fifthPair_Fdelta_right_limit :
    Tendsto fifthPairFdelta (𝓝[>] (0 : ℝ)) (𝓝 fifthPairFlin) := by
  have hlim : Tendsto fifthPairExtension (𝓝[>] (0 : ℝ)) (𝓝 (fifthPairExtension 0)) :=
    fifthPair_extension_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [fifthPair_extension_eq (le_refl 0) (by norm_num)] at hlim
  change Tendsto fifthPairExtension (𝓝[>] (0 : ℝ)) (𝓝 fifthPairFlin) at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < 1 / 1000 from
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 1000)))] with δ hδ hhi
  exact fifthPair_extension_eq hδ.le hhi.le

theorem fifthPair_Fdelta_close {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 1000 ∧ |fifthPairFdelta δ - fifthPairFlin| < ε := by
  obtain ⟨r, hr, hclose⟩ := Metric.tendsto_nhdsWithin_nhds.mp fifthPair_Fdelta_right_limit ε hε
  let δ := min (r / 2) (1 / 1000)
  have hδ : 0 < δ := lt_min (half_pos hr) (by norm_num)
  have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨δ, hδ, min_le_right _ _, ?_⟩
  have hd : dist δ 0 < r := by simpa only [Real.dist_eq, sub_zero, abs_of_pos hδ] using hδr
  exact hclose hδ hd

/-- Full original term five, with the classical delta-zero coefficient. -/
theorem fifthPair_actual_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin - ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) ≤ (fifthPairCount N : ℝ) := by
  obtain ⟨δ, hδ, hδhi, hclose⟩ := fifthPair_Fdelta_close (half_pos hε)
  obtain ⟨T, hT, h⟩ := fifthPair_actual_Fdelta_lower hδ hδhi (half_pos hε)
  refine ⟨T, hT, ?_⟩
  intro N hN he
  have hcoeff : fifthPairFlin - ε ≤ fifthPairFdelta δ - ε / 2 := by
    have hh := (abs_lt.mp hclose).1
    linarith
  have hm := (mul_le_mul_of_nonneg_right hcoeff
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (h N hN he)
  simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hm

end Wu2008DoubleSieve
