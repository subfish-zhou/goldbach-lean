import FifthHDCT
import MathlibNt.Wu2008DoubleSieve.FifthPairLower
namespace Wu2008DoubleSieve
open Finset Set Real Filter MeasureTheory
open scoped Classical Topology

/-- The literal full original triangular fifth-term coefficient at fixed delta. -/
noncomputable def fifthHFdelta (δ : ℝ) : ℝ :=
  4 * ∫ y in truncatedSixthLowerAlpha..truncatedSixthLowerBeta,
    ∫ x in truncatedSixthLowerAlpha..y,
      (wuLowerCoefficient (truncatedSixthLowerS δ x y) +
        wuImprovementLimit false δ (truncatedSixthLowerS δ x y)) /
        (x * y * (truncatedSixthLowerC δ - x - y))

theorem fifthH_effective_weight_eq {δ : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 1000)
    {n : ℕ} {j : ℕ × ℕ} (hj : j ∈ fifthPairInner n) :
    fifthHEffectiveWeight δ n j = fifthHWeight δ n j := by
  have hg := fifthPair_inner_geometry hj
  have hb := fifthPair_region_bounds hδ hδhi
    (v := (truncatedSixthClosureHi n j.1, truncatedSixthClosureHi n j.2))
    ⟨hg.1.trans (truncatedSixthClosure_lo_lt_hi n j.1).le,
      hg.2.1.trans (truncatedSixthClosure_lo_lt_hi n j.2).le, hg.2.2⟩
  simp only [fifthHEffectiveWeight, fifthHWeight, truncatedSixthClosureCoefficient,
    if_true, truncatedSixthMassEffective, truncatedSixthMass_clip_eq hb.2.2.2]

theorem fifthH_kernel_original {δ : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 1000)
    {v : ℝ × ℝ} (hv : v ∈ fifthPairRegion) :
    fifthHKernel δ v =
      (wuLowerCoefficient (truncatedSixthLowerS δ v.1 v.2) +
        wuImprovementLimit false δ (truncatedSixthLowerS δ v.1 v.2)) /
      (v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2)) := by
  simp only [fifthHKernel, if_pos hv, truncatedSixthClosureCoefficient, if_true,
    truncatedSixthMassEffective,
    truncatedSixthMass_clip_eq (fifthPair_region_bounds hδ hδhi hv).2.2.2]

theorem fifthH_kernel_measurable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) :
    Measurable (fifthHKernel δ) := by
  have hs : Measurable (fun v : ℝ × ℝ => truncatedSixthLowerS δ v.1 v.2) := by
    unfold truncatedSixthLowerS
    fun_prop
  have hd : Measurable (fun v : ℝ × ℝ =>
      v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2)) := by fun_prop
  exact (((truncatedSixthMass_effective_monotone hδ (by linarith)).measurable.comp hs).div
    hd).ite fifthPair_region_compact.isClosed.measurableSet measurable_const

theorem fifthH_kernel_integrable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) :
    Integrable (fifthHKernel δ) := by
  have hsupp : Function.support (fifthHKernel δ) ⊆ fifthPairRegion := by
    intro v hv
    by_contra h
    exact hv (by simp [fifthHKernel, h])
  apply (integrableOn_iff_integrable_of_support_subset hsupp).mp
  apply Measure.integrableOn_of_bounded (M := fifthPairKernelBound)
    fifthPair_region_compact.measure_lt_top.ne
    (fifthH_kernel_measurable hδ hδhi).aestronglyMeasurable
  have hc : ∀ᵐ v : ℝ × ℝ, ContinuousAt (truncatedSixthClosureCoefficient true δ)
      (truncatedSixthLowerS δ v.1 v.2) :=
    truncatedSixthMass_effective_pullback_ae hδ (by linarith)
  filter_upwards [ae_restrict_of_ae hc,
    ae_restrict_of_ae (compl_mem_ae_iff.mpr fifthPair_region_frontier)] with v hc hf
  have hlim := (fifthH_step_tendsto hδ hδhi hf hc).norm
  apply le_of_tendsto hlim
  have hK : 0 ≤ fifthPairKernelBound := by
    have hα := truncatedSixthLower_parameters.1
    unfold fifthPairKernelBound
    positivity
  apply Eventually.of_forall
  intro n
  apply (fifthH_step_bound hδ hδhi n v).trans
  by_cases hv : v ∈ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
  · simp only [Set.indicator_of_mem hv, le_refl]
  · simpa only [Set.indicator_of_notMem hv] using hK

/-- Product-integral identity uses F5's triangle, not the F6 admissible region. -/
theorem fifthH_literal_integral {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) :
    fifthHFdelta δ = 4 * ∫ v : ℝ × ℝ, fifthHKernel δ v := by
  have hp := truncatedSixthLower_parameters
  have houter : Function.support (fun y => ∫ x, fifthHKernel δ (x,y)) ⊆
      Set.Icc truncatedSixthLowerAlpha truncatedSixthLowerBeta := by
    intro y hy
    by_contra h
    apply hy
    change (∫ x, fifthHKernel δ (x,y)) = 0
    have hz : (fun x => fifthHKernel δ (x,y)) = 0 := by
      funext x
      have hn : (x,y) ∉ fifthPairRegion := fun hv => h ⟨hv.1.trans hv.2.1, hv.2.2⟩
      simp [fifthHKernel, hn]
    rw [hz]
    simp
  rw [show (∫ v : ℝ × ℝ, fifthHKernel δ v) = ∫ y, ∫ x, fifthHKernel δ (x,y) from
      integral_prod_symm _ (fifthH_kernel_integrable hδ hδhi),
    truncatedSixthMass_integral_eq_interval hp.2.1.le houter]
  unfold fifthHFdelta
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le hp.2.1.le] at hy
  have hinner : Function.support (fun x => fifthHKernel δ (x,y)) ⊆
      Set.Icc truncatedSixthLowerAlpha y := by
    intro x hx
    by_cases hv : (x,y) ∈ fifthPairRegion
    · exact ⟨hv.1, hv.2.1⟩
    · exact False.elim (hx (by simp [fifthHKernel, hv]))
  dsimp only
  rw [truncatedSixthMass_integral_eq_interval hy.1 hinner]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le hy.1] at hx
  exact (fifthH_kernel_original hδ.le hδhi (v := (x,y)) ⟨hx.1, hx.2, hy.2⟩).symm

theorem fifthH_density_mass_le {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) {n : ℕ} {j : ℕ × ℕ}
    (hj : j ∈ fifthPairInner n) :
    4 * (volume.real (truncatedSixthClosureCell n j) *
      fifthHDensity δ n j) ≤
      fifthHEffectiveWeight δ n j * truncatedSixthClosureRcoef δ n j := by
  have hg := fifthPair_inner_geometry hj
  have hα := truncatedSixthLower_parameters.1
  have ha := hα.trans_le hg.1
  have hab := (truncatedSixthClosure_lo_lt_hi n j.1).le
  have hcd := (truncatedSixthClosure_lo_lt_hi n j.2).le
  have hac := hg.1.trans (hab.trans hg.2.1)
  have hc := hα.trans_le hac
  have hb := ha.trans_le hab
  have hd := hc.trans_le hcd
  have hden : 2 * truncatedSixthLowerAlpha ≤ truncatedSixthLowerC δ -
      truncatedSixthClosureLo n j.1 - truncatedSixthClosureLo n j.2 := by
    have hl := fifthPair_region_bounds hδ.le hδhi
      (v := (truncatedSixthClosureLo n j.1, truncatedSixthClosureLo n j.2))
      ⟨hg.1, hab.trans hg.2.1, hcd.trans hg.2.2⟩
    exact hl.2.2.1
  have hden0 : 0 < truncatedSixthLowerC δ -
      truncatedSixthClosureLo n j.1 - truncatedSixthClosureLo n j.2 := by linarith
  have hw := (truncatedSixthClosure_coefficient_bounds hδ (by linarith) true
    (truncatedSixthLowerS δ (truncatedSixthClosureHi n j.1) (truncatedSixthClosureHi n j.2))).1
  change 0 ≤ fifthHEffectiveWeight δ n j at hw
  have hlogs := mul_le_mul (truncatedSixthClosure_log_lower ha hab)
    (truncatedSixthClosure_log_lower hc hcd)
    (div_nonneg (sub_nonneg.mpr hcd) hd.le)
    (log_nonneg ((one_le_div ha).mpr hab))
  have hbound := mul_le_mul_of_nonneg_left hlogs
    (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hw) hden0.le)
  rw [truncatedSixthClosure_cell_volume]
  unfold fifthHDensity truncatedSixthClosureRcoef truncatedSixthMassRectangleCoefficient
  simp only [truncatedSixthClosureLower, truncatedSixthClosureUpper,
    max_eq_right (hg.1.trans hab), max_eq_right (hac.trans hcd), max_eq_right hden]
  convert hbound using 1
  · rfl
  · simp only [div_eq_mul_inv, mul_inv]
    ring
  · ring

theorem fifthH_step_integral (δ : ℝ) (n : ℕ) :
    (∫ v : ℝ × ℝ, fifthHStep δ n v) =
      ∑ j ∈ fifthPairInner n,
        volume.real (truncatedSixthClosureCell n j) * fifthHDensity δ n j := by
  unfold fifthHStep
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro j _
    rw [integral_indicator_const _ (truncatedSixthClosure_cell_measurable n j), smul_eq_mul]
  · intro j _
    apply IntegrableOn.integrable_indicator _ (truncatedSixthClosure_cell_measurable n j)
    exact integrableOn_const ((measure_mono (show truncatedSixthClosureCell n j ⊆
      Set.Icc (truncatedSixthClosureLower n j) (truncatedSixthClosureUpper n j) from
        fun _ hv => ⟨⟨hv.1.1, hv.2.1⟩, ⟨hv.1.2.le, hv.2.2.le⟩⟩)).trans_lt
      isCompact_Icc.measure_lt_top |>.ne)

theorem fifthH_sum_sufficient {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (hε : 0 < ε) :
    ∃ n : ℕ, fifthHFdelta δ - ε < fifthHCellSum δ n := by
  have hlim := (fifthH_integral_tendsto hδ hδhi).const_mul 4
  rw [← fifthH_literal_integral hδ hδhi] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds (sub_lt_self _ hε))).exists
  refine ⟨n, hn.trans_le ?_⟩
  rw [fifthH_step_integral, mul_sum]
  unfold fifthHCellSum
  apply sum_le_sum
  intro j hj
  have h := fifthH_density_mass_le hδ hδhi hj
  rwa [fifthH_effective_weight_eq hδ.le hδhi hj] at h

/-- Full original fifth-term integral lower bound, with a single uniform threshold. -/
theorem fifthH_actual_Fdelta_lower {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthHFdelta δ - ε) * truncatedSixthMassScale N ≤ (fifthPairCount N : ℝ) := by
  obtain ⟨n, hn⟩ := fifthH_sum_sufficient hδ hδhi (half_pos hε)
  obtain ⟨T, hT, h⟩ := fifthH_unperturbed_family_count hδ hδhi (half_pos hε) n
  refine ⟨T, hT, ?_⟩
  intro N hN he
  exact (mul_le_mul_of_nonneg_right (by linarith :
    fifthHFdelta δ - ε ≤ fifthHCellSum δ n - ε / 2)
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (h N hN he)

end Wu2008DoubleSieve
