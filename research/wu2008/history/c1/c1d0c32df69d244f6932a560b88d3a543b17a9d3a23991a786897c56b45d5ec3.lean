import MathlibNt.Wu2008DoubleSieve.TruncatedSixthMassContinuity

/-!
# Coarse Riemann approximation of the literal fixed-delta integrals

This uses the existing upper-tag unit partitions and the existing
almost-everywhere-continuous box-integral theorem. No continuity of
the improvement coefficient is assumed.
-/

namespace Wu2008DoubleSieve

open Set Real Filter MeasureTheory BoxIntegral
open scoped Classical Topology

noncomputable def truncatedSixthMassUnitBox : Box (Fin 2) :=
  ⟨fun _ => 0, fun _ => 1, fun _ => zero_lt_one⟩

noncomputable def truncatedSixthMassCoarseSum (f : (ℝ × ℝ) → ℝ) (n : ℕ) : ℝ :=
  integralSum (fun v : Fin 2 → ℝ => f (v 0, v 1))
    (volume : Measure (Fin 2 → ℝ)).toBoxAdditive.toSMul
    (unitPartition.prepartition (n + 1) truncatedSixthMassUnitBox)

theorem truncatedSixthMass_unit_vertices : hasIntegralVertices truncatedSixthMassUnitBox :=
  ⟨fun _ => 0, fun _ => 1, fun _ => by norm_num [truncatedSixthMassUnitBox],
    fun _ => by norm_num [truncatedSixthMassUnitBox]⟩

theorem truncatedSixthMass_coarse_tendsto {f : (ℝ × ℝ) → ℝ}
    (hb : ∃ M, ∀ v, ‖f v‖ ≤ M)
    (hc : ∀ᵐ v : ℝ × ℝ, ContinuousAt f v)
    (hs : ∀ v : ℝ × ℝ, f v ≠ 0 → 0 < v.1 ∧ v.1 ≤ 1 ∧ 0 < v.2 ∧ v.2 ≤ 1) :
    Tendsto (truncatedSixthMassCoarseSum f) atTop (𝓝 (∫ v : ℝ × ℝ, f v)) := by
  have hcont : Continuous (fun v : Fin 2 → ℝ => (v 0, v 1)) := by fun_prop
  have hcae : ∀ᵐ v : Fin 2 → ℝ, ContinuousAt (fun v : Fin 2 → ℝ => f (v 0, v 1)) v := by
    filter_upwards [(volume_preserving_finTwoArrow ℝ).quasiMeasurePreserving.ae hc] with v hv
    exact hv.comp (f := fun w : Fin 2 → ℝ => (w 0, w 1)) hcont.continuousAt
  have hbb : ∃ M, ∀ v ∈ Box.Icc truncatedSixthMassUnitBox,
      ‖f (v 0, v 1)‖ ≤ M := by
    obtain ⟨M, hM⟩ := hb
    exact ⟨M, fun v _ => hM (v 0, v 1)⟩
  have hint : (∫ v : Fin 2 → ℝ in (truncatedSixthMassUnitBox : Set (Fin 2 → ℝ)),
      f (v 0, v 1)) = ∫ v : ℝ × ℝ, f v := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact (volume_preserving_finTwoArrow ℝ).integral_comp
        MeasurableEquiv.finTwoArrow.measurableEmbedding f
    · intro v hv
      by_contra h
      have hmem := hs (v 0, v 1) h
      apply hv
      intro i
      fin_cases i
      · exact ⟨hmem.1, hmem.2.1⟩
      · exact ⟨hmem.2.2.1, hmem.2.2.2⟩
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨r, hr1, hr2⟩ := (hasIntegral_iff.mp <|
    AEContinuous.hasBoxIntegral (volume : Measure (Fin 2 → ℝ)) hbb hcae
      IntegrationParams.Riemann) (ε / 2) (half_pos hε)
  refine ⟨⌈(r 0 0 : ℝ)⁻¹⌉₊, fun n hn => ?_⟩
  have hmesh : 1 / ((n + 1 : ℕ) : ℝ) ≤ (r 0 0 : ℝ) := by
    rw [one_div, inv_le_comm₀ (by positivity) (r 0 0).prop]
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (hn.trans (Nat.le_succ n)))
  have hbound := hr2 0 (unitPartition.prepartition (n + 1) truncatedSixthMassUnitBox)
    (show IntegrationParams.Riemann.MemBaseSet truncatedSixthMassUnitBox 0 (r 0)
      (unitPartition.prepartition (n + 1) truncatedSixthMassUnitBox) from ⟨by
        rw [show r 0 = fun _ => r 0 0 from funext_iff.mpr (hr1 0 rfl)]
        exact unitPartition.prepartition_isSubordinate _ _ (r 0 0).prop hmesh,
      fun _ => unitPartition.prepartition_isHenstock _ _,
      by simp [IntegrationParams.Riemann],
      by simp [IntegrationParams.Riemann]⟩)
    (unitPartition.prepartition_isPartition _ truncatedSixthMass_unit_vertices)
  rw [hint] at hbound
  exact hbound.trans_lt (half_lt_self hε)

theorem truncatedSixthMass_disjoint_support (δ : ℝ) (v : ℝ × ℝ) :
    (truncatedSixthMassWedgeKernel δ v ≠ 0 ∨ truncatedSixthMassAdmissibleKernel δ v ≠ 0) →
      0 < v.1 ∧ v.1 ≤ 1 ∧ 0 < v.2 ∧ v.2 ≤ 1 := by
  intro h
  have hr : truncatedSixthLowerRegion δ v.1 v.2 := by
    by_contra hn
    have hw : ¬truncatedSixthLowerWedge δ v.1 v.2 := fun hv => hn hv.1
    have hd : ¬truncatedSixthLowerAdmissibleRegion δ v.1 v.2 := fun hv => hn hv.1
    rcases h with h | h
    · exact h (by simp [truncatedSixthMassWedgeKernel, hw])
    · exact h (by simp [truncatedSixthMassAdmissibleKernel, hd])
  have hp := truncatedSixthLower_parameters
  refine ⟨hp.1.trans_le hr.1, ?_, (hp.1.trans hp.2.1).trans_le hr.2.2.1, ?_⟩
  · linarith [hr.2.1, hp.2.2.1, hp.2.2.2.1]
  · linarith [hr.2.2.2.1, hp.2.2.2.1]

theorem truncatedSixthMass_disjoint_bounds {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (v : ℝ × ℝ) :
    ‖truncatedSixthMassWedgeKernel δ v‖ ≤ 2 * truncatedSixthMassKernelBound ∧
      ‖truncatedSixthMassAdmissibleKernel δ v‖ ≤ 2 * truncatedSixthMassKernelBound := by
  have hb := truncatedSixthMass_kernels_bounds hδ hδhi v
  have hK : 0 ≤ truncatedSixthMassKernelBound := hb.1.1.trans hb.1.2
  have ha : ‖truncatedSixthMassAKernel δ v‖ ≤ truncatedSixthMassKernelBound := by
    simpa only [norm_eq_abs, abs_of_nonneg hb.1.1] using hb.1.2
  have hh : ‖truncatedSixthMassHKernel δ v‖ ≤ truncatedSixthMassKernelBound := by
    simpa only [norm_eq_abs, abs_of_nonneg hb.2.1] using hb.2.2
  constructor
  · by_cases hw : truncatedSixthLowerWedge δ v.1 v.2
    · simpa [truncatedSixthMassWedgeKernel, hw] using ha.trans (by linarith)
    · simp [truncatedSixthMassWedgeKernel, hw, hK]
  · by_cases hd : truncatedSixthLowerAdmissibleRegion δ v.1 v.2
    · simp only [truncatedSixthMassAdmissibleKernel, indicator_apply, mem_ofPred_eq, if_pos hd]
      exact (norm_add_le _ _).trans (by linarith)
    · simp [truncatedSixthMassAdmissibleKernel, hd, hK]

theorem truncatedSixthMass_disjoint_coarse_tendsto {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) :
    Tendsto (truncatedSixthMassCoarseSum (truncatedSixthMassWedgeKernel δ))
      atTop (𝓝 (∫ v : ℝ × ℝ, truncatedSixthMassWedgeKernel δ v)) ∧
    Tendsto (truncatedSixthMassCoarseSum (truncatedSixthMassAdmissibleKernel δ))
      atTop (𝓝 (∫ v : ℝ × ℝ, truncatedSixthMassAdmissibleKernel δ v)) := by
  constructor
  · exact truncatedSixthMass_coarse_tendsto
      ⟨2 * truncatedSixthMassKernelBound, fun v => (truncatedSixthMass_disjoint_bounds hδ hδhi v).1⟩
      (truncatedSixthMass_other_kernels_ae_continuous hδ hδhi).1
      (fun v hv => truncatedSixthMass_disjoint_support δ v (Or.inl hv))
  · exact truncatedSixthMass_coarse_tendsto
      ⟨2 * truncatedSixthMassKernelBound, fun v => (truncatedSixthMass_disjoint_bounds hδ hδhi v).2⟩
      (truncatedSixthMass_kernels_ae_continuous hδ hδhi).2
      (fun v hv => truncatedSixthMass_disjoint_support δ v (Or.inr hv))

theorem truncatedSixthMass_literal_coarse_tendsto {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) :
    Tendsto (fun n => 4 * truncatedSixthMassCoarseSum (truncatedSixthMassWedgeKernel δ) n +
      4 * truncatedSixthMassCoarseSum (truncatedSixthMassAdmissibleKernel δ) n)
      atTop (𝓝 (truncatedSixthLowerFdelta δ + truncatedSixthLowerHadmdelta δ)) := by
  rw [truncatedSixthMass_literal_disjoint_integral hδ hδhi]
  exact ((truncatedSixthMass_disjoint_coarse_tendsto hδ hδhi).1.const_mul 4).add
    ((truncatedSixthMass_disjoint_coarse_tendsto hδ hδhi).2.const_mul 4)

end Wu2008DoubleSieve
