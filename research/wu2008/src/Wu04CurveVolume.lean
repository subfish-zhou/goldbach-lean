import Wu04CurveGeometry

namespace Wu04CurveVolume
open Wu2008DoubleSieve Set MeasureTheory Real
open SecondFunctionalParameters Wu04RecoverRectangle Wu04CurveGeometry
noncomputable section
open Classical

/-- Literal planar slice with the original open v face. -/
def P : Set (ℝ × ℝ) := {p | r<p.1 ∧ p.1≤rc ∧ c≤p.2 ∧ p.2≤2-b-4*p.1}

theorem P_measurable : MeasurableSet P := by
  exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
    ((measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd
      ((measurable_const.sub measurable_const).sub (measurable_const.mul measurable_fst)))))

theorem split3_preserving : MeasurePreserving
    (fun t : Fin 3 → ℝ => (t 0,(t 1,t 2))) volume volume := by
  have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_preserving_finTwoArrow ℝ)).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)
  convert h using 1 <;> rfl

/-- Each section is the full original z interval, not a rectangular surrogate. -/
theorem P_section (v : ℝ) : volume (Prod.mk v ⁻¹' P) =
    (Ioc r rc).indicator (fun v => ENNReal.ofReal (2-b-4*v-c)) v := by
  by_cases hv : v∈Ioc r rc
  · have he : Prod.mk v ⁻¹' P = Icc c (2-b-4*v) := by
      ext z
      simp only [mem_preimage,P,mem_ofPred_eq,mem_Icc]
      exact ⟨fun h => h.2.2, fun h => ⟨hv.1,hv.2,h⟩⟩
    rw [he,Real.volume_Icc,indicator_of_mem hv]
  · have he : Prod.mk v ⁻¹' P = ∅ := by
      ext z
      simp only [mem_preimage,P,mem_ofPred_eq,mem_empty_iff_false,iff_false]
      intro hz
      exact hv ⟨hz.1,hz.2.1⟩
    rw [he,measure_empty,indicator_of_notMem hv]

theorem height_integral : (∫ v in Ioc r rc, (2-b-4*v-c)) = (f-c)^2/8 := by
  rw [← intervalIntegral.integral_of_le geometry.2.2.2.1.le]
  have h : IntervalIntegrable (fun v : ℝ => 2-b-4*v-c) volume r rc :=
    (by fun_prop : Continuous (fun v : ℝ => 2-b-4*v-c)).intervalIntegrable _ _
  have hd (v : ℝ) : HasDerivAt (fun x : ℝ => (2-b-c)*x-2*x^2) (2-b-4*v-c) v := by
    convert (((hasDerivAt_id v).const_mul (2-b-c)).sub
      (((hasDerivAt_id v).pow 2).const_mul 2)) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v) h]
  unfold r rc
  ring

theorem P_volume : volume P = ENNReal.ofReal ((f-c)^2/8) := by
  change (volume.prod volume) P = _
  rw [Measure.prod_apply P_measurable]
  simp_rw [P_section]
  rw [lintegral_indicator measurableSet_Ioc]
  have hi : IntegrableOn (fun v : ℝ => 2-b-4*v-c) (Ioc r rc) :=
    (by fun_prop : Continuous (fun v : ℝ => 2-b-4*v-c)).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hn : 0≤ᵐ[volume.restrict (Ioc r rc)] (fun v : ℝ => 2-b-4*v-c) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    change 0 ≤ 2-b-4*v-c
    have hh := hv.2
    unfold rc at hh
    linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,height_integral]

theorem T_preimage : T = (fun t : Fin 3 → ℝ => (t 0,(t 1,t 2))) ⁻¹' (Icc a b ×ˢ P) := by
  ext t
  simp only [T,P,mem_ofPred_eq,mem_preimage,mem_prod,mem_Icc]
  tauto

/-- Actual Fin3 product volume of the curved remainder. -/
theorem T_volume : volume T = ENNReal.ofReal ((b-a)*(f-c)^2/8) := by
  rw [T_preimage,split3_preserving.measure_preimage
    (measurableSet_Icc.prod P_measurable).nullMeasurableSet]
  change (volume.prod volume) (Icc a b ×ˢ P) = _
  rw [Measure.prod_prod,Real.volume_Icc,P_volume,← ENNReal.ofReal_mul (sub_nonneg.mpr geometry.2.1)]
  congr 1
  ring

theorem T_volume_real : volume.real T = (b-a)*(f-c)^2/8 := by
  rw [Measure.real,T_volume,ENNReal.toReal_ofReal]
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr geometry.2.1) (sq_nonneg _)) (by norm_num)

end
end Wu04CurveVolume
