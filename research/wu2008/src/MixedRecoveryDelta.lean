import MixedPaymentDomain

namespace MixedRecovery
open Set Filter MeasureTheory Real Wu2008DoubleSieve MixedPayment
open scoped Topology
noncomputable section

theorem highRegion_subset_zero {δ : ℝ} (hδ : 0 ≤ δ) :
    highRegion δ ⊆ highRegion 0 := by
  intro v hv
  refine ⟨⟨hv.1.1,hv.1.2.1,hv.1.2.2.1,hv.1.2.2.2.1,?_⟩,hv.2⟩
  have h := hv.1.2.2.2.2
  dsimp [truncatedSixthLowerC] at h ⊢
  linarith

/-- A full right-neighbourhood, not a selected delta sequence. -/
theorem highRegion_delta_eventually {v : ℝ × ℝ}
    (hv : v ∈ interior (highRegion 0)) :
    ∀ᶠ δ : ℝ in 𝓝[Set.Ici 0] 0, v ∈ highRegion δ := by
  have hr := (interior_subset hv).1
  have ht : Tendsto (fun δ : ℝ => (v.1+δ,v.2)) (𝓝 0) (𝓝 v) := by
    simpa only [add_zero,Prod.eta] using
      ((tendsto_const_nhds (x := v.1)).add
        (show Tendsto (fun δ : ℝ => δ) (𝓝 0) (𝓝 0) from tendsto_id)).prodMk_nhds
          (tendsto_const_nhds (x := v.2))
  have he := ht.eventually (mem_of_superset (isOpen_interior.mem_nhds hv) interior_subset)
  filter_upwards [he.filter_mono nhdsWithin_le_nhds] with δ h
  refine ⟨⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,?_⟩,(interior_subset hv).2⟩
  have hh := h.1.2.2.2.2
  dsimp [truncatedSixthLowerC] at hh ⊢
  linarith

/-- Signed dominated convergence on every sufficiently small nonnegative delta. -/
theorem highRegion_integral_delta {f : ℝ × ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun δ => ∫ v, (highRegion δ).indicator f v) (𝓝[Set.Ici 0] 0)
      (𝓝 (∫ v, (highRegion 0).indicator f v)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun v => ‖f v‖)
  · exact Eventually.of_forall (fun δ =>
      (hf.indicator (highRegion_closed δ).measurableSet).aestronglyMeasurable)
  · exact Eventually.of_forall (fun _ =>
      Eventually.of_forall (fun _ => norm_indicator_le_norm_self _ _))
  · exact hf.norm
  · filter_upwards [compl_mem_ae_iff.mpr (highRegion_frontier 0)] with v hv
    by_cases hmem : v ∈ highRegion 0
    · have hin : v ∈ interior (highRegion 0) := by
        by_contra h
        exact hv ⟨subset_closure hmem,h⟩
      apply tendsto_const_nhds.congr'
      filter_upwards [highRegion_delta_eventually hin] with δ hδ
      simp only [indicator_of_mem hδ,indicator_of_mem hmem]
    · apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hnot : v ∉ highRegion δ := fun h => hmem (highRegion_subset_zero hδ h)
      simp only [indicator_of_notMem hnot,indicator_of_notMem hmem]

theorem original_high_subset_zero : Wu08G6High.highDomain ⊆ highRegion 0 := by
  intro v hv
  have h := (Wu08G6High.high_iff v.1 v.2).mp hv
  refine ⟨⟨h.1.1,?_,?_,?_,?_⟩,h.2.1.le⟩
  · have hb := h.1.2
    norm_num [QuarterTrim.alpha,truncatedSixthLowerBeta] at hb ⊢
    linarith
  · have hb := h.2.1
    norm_num [truncatedSixthLowerBeta] at hb ⊢
    linarith
  · change v.2 ≤ 1/2-3*QuarterTrim.alpha
    linarith [h.1.1,h.2.2]
  · change v.1+v.2 ≤ 1/2-0-2*QuarterTrim.alpha
    linarith [h.2.2]

theorem highGain_indicator_zero :
    (highRegion 0).indicator HighConsumer.highGainKernel = HighConsumer.highGainKernel := by
  funext v
  by_cases hv : v ∈ highRegion 0
  · exact indicator_of_mem hv _
  · rw [indicator_of_notMem hv]
    have hn : v ∉ Wu08G6High.highDomain := fun h => hv (original_high_subset_zero h)
    simp [HighConsumer.highGainKernel,hn]

theorem original_highGain_delta :
    Tendsto (fun δ => 4*∫ v, (highRegion δ).indicator HighConsumer.highGainKernel v)
      (𝓝[Set.Ici 0] 0) (𝓝 HighConsumer.highGain) := by
  have h := (highRegion_integral_delta HighConsumer.highGain_integrable).const_mul 4
  simpa only [highGain_indicator_zero,HighConsumer.highGain] using h

/-- Simultaneous delta cap usable by a later existential PairUpper producer. -/
theorem original_highGain_small_delta {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 ≤ δ → δ < d →
      HighConsumer.highGain-ε < 4*∫ v, (highRegion δ).indicator HighConsumer.highGainKernel v := by
  have h := original_highGain_delta.eventually_const_lt (sub_lt_self _ hε)
  obtain ⟨U,hU,hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨d,hd,?_⟩
  intro δ hδ hdδ
  apply hsub
  refine ⟨hball ?_,hδ⟩
  simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hδ] using hdδ

/-- The already-proved actual cells exhaust the original integrable gain kernel. -/
theorem original_highGain_cells (δ : ℝ) :
    Tendsto (fun n => 4*∫ v, (highCover δ n).indicator HighConsumer.highGainKernel v) atTop
      (𝓝 (4*∫ v, (highRegion δ).indicator HighConsumer.highGainKernel v)) :=
  (highCover_integral_tendsto δ HighConsumer.highGain_integrable).const_mul 4

end
end MixedRecovery
