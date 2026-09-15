import Wu04RemainingStrongFourth

namespace Wu04RemainingStrongFourthVolume
open Wu2008DoubleSieve Set MeasureTheory Real Wu04RemainingStrongFourth
noncomputable section

def P (i : Fin 3) : Set (ℝ×ℝ) := {p | r i<p.1 ∧ p.1≤v i ∧ c i≤p.2 ∧ p.2≤2-b i-4*p.1}
def area (i : Fin 3) : ℝ := (v i-r i)*(2-b i-c i-2*(v i+r i))

theorem P_measurable (i : Fin 3) : MeasurableSet (P i) := by
  exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
    ((measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd
      ((measurable_const.sub measurable_const).sub (measurable_const.mul measurable_fst)))))

theorem section_volume (i : Fin 3) (x : ℝ) : volume (Prod.mk x ⁻¹' P i)=
    (Ioc (r i) (v i)).indicator (fun x => ENNReal.ofReal (2-b i-4*x-c i)) x := by
  by_cases hx : x∈Ioc (r i) (v i)
  · have he : Prod.mk x ⁻¹' P i=Icc (c i) (2-b i-4*x) := by
      ext z
      simp only [mem_preimage,P,mem_ofPred_eq,mem_Icc]
      exact ⟨fun h => h.2.2,fun h => ⟨hx.1,hx.2,h⟩⟩
    rw [he,Real.volume_Icc,indicator_of_mem hx]
  · have he : Prod.mk x ⁻¹' P i=∅ := by
      ext z
      simp only [mem_preimage,P,mem_ofPred_eq,mem_empty_iff_false,iff_false]
      intro h
      exact hx ⟨h.1,h.2.1⟩
    rw [he,measure_empty,indicator_of_notMem hx]

theorem height_integral (i : Fin 3) :
    (∫ x in Ioc (r i) (v i),(2-b i-4*x-c i))=area i := by
  rw [← intervalIntegral.integral_of_le (geometry i).2.2.2.1.le]
  have hi : IntervalIntegrable (fun x : ℝ => 2-b i-4*x-c i) volume (r i) (v i) :=
    (by fun_prop : Continuous (fun x : ℝ => 2-b i-4*x-c i)).intervalIntegrable _ _
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => (2-b i-c i)*y-2*y^2) (2-b i-4*x-c i) x := by
    convert (((hasDerivAt_id x).const_mul (2-b i-c i)).sub
      (((hasDerivAt_id x).pow 2).const_mul 2)) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi]
  unfold area
  ring

theorem area_pos (i : Fin 3) : 0<area i := by
  have g := geometry i
  have hv := clip_le i
  unfold rc at hv
  unfold area
  apply mul_pos (sub_pos.mpr g.2.2.2.1)
  linarith only [hv,g.2.2.2.1]

theorem P_volume (i : Fin 3) : volume (P i)=ENNReal.ofReal (area i) := by
  change (volume.prod volume) (P i)=_
  rw [Measure.prod_apply (P_measurable i)]
  simp_rw [section_volume]
  rw [lintegral_indicator measurableSet_Ioc]
  have hi : IntegrableOn (fun x : ℝ => 2-b i-4*x-c i) (Ioc (r i) (v i)) :=
    (by fun_prop : Continuous (fun x : ℝ => 2-b i-4*x-c i)).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hn : 0≤ᵐ[volume.restrict (Ioc (r i) (v i))] (fun x : ℝ => 2-b i-4*x-c i) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    change 0≤2-b i-4*x-c i
    have hv := hx.2.trans (clip_le i)
    unfold rc at hv
    linarith only [hv]
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,height_integral]

theorem T_volume (i : Fin 3) : volume (T i)=ENNReal.ofReal ((b i-a i)*area i) := by
  have he : T i=(fun t : Fin 3 → ℝ => (t 0,(t 1,t 2))) ⁻¹' (Icc (a i) (b i) ×ˢ P i) := by
    ext t
    simp only [T,P,mem_ofPred_eq,mem_preimage,mem_prod,mem_Icc]
    tauto
  rw [he,Wu04CurveVolume.split3_preserving.measure_preimage
    (measurableSet_Icc.prod (P_measurable i)).nullMeasurableSet]
  change (volume.prod volume) (Icc (a i) (b i) ×ˢ P i)=_
  rw [Measure.prod_prod,Real.volume_Icc,P_volume,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr (geometry i).2.1.le)]

theorem T_volume_real (i : Fin 3) : volume.real (T i)=(b i-a i)*area i := by
  rw [Measure.real,T_volume,ENNReal.toReal_ofReal]
  exact mul_nonneg (sub_nonneg.mpr (geometry i).2.1.le) (area_pos i).le
end
end Wu04RemainingStrongFourthVolume
