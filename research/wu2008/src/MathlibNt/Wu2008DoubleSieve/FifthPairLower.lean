import MathlibNt.Wu2008DoubleSieve.FifthPairIntegral
namespace Wu2008DoubleSieve
open Finset Set Real Filter MeasureTheory
open scoped Classical Topology

theorem fifthPair_density_mass_le {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) {n : ℕ} {j : ℕ × ℕ}
    (hj : j ∈ fifthPairInner n) :
    4 * (volume.real (truncatedSixthClosureCell n j) *
      fifthPairDensity δ n j) ≤
      truncatedSixthClosureWeight false δ n j * truncatedSixthClosureRcoef δ n j := by
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
  have hw := (truncatedSixthClosure_weight_bounds hδ (by linarith) false n j).1
  have hlogs := mul_le_mul (truncatedSixthClosure_log_lower ha hab)
    (truncatedSixthClosure_log_lower hc hcd)
    (div_nonneg (sub_nonneg.mpr hcd) hd.le)
    (log_nonneg ((one_le_div ha).mpr hab))
  have hbound := mul_le_mul_of_nonneg_left hlogs
    (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hw) hden0.le)
  rw [truncatedSixthClosure_cell_volume]
  unfold fifthPairDensity truncatedSixthClosureRcoef truncatedSixthMassRectangleCoefficient
  simp only [truncatedSixthClosureLower, truncatedSixthClosureUpper,
    max_eq_right (hg.1.trans hab), max_eq_right (hac.trans hcd), max_eq_right hden]
  convert hbound using 1
  · rfl
  · simp only [div_eq_mul_inv, mul_inv]
    ring
  · ring

theorem fifthPair_step_integral (δ : ℝ) (n : ℕ) :
    (∫ v : ℝ × ℝ, fifthPairStep δ n v) =
      ∑ j ∈ fifthPairInner n,
        volume.real (truncatedSixthClosureCell n j) * fifthPairDensity δ n j := by
  unfold fifthPairStep
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

theorem fifthPair_sum_sufficient {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (hε : 0 < ε) :
    ∃ n : ℕ, fifthPairFdelta δ - ε < fifthPairCellSum δ n := by
  have hlim := (fifthPair_integral_tendsto hδ hδhi).const_mul 4
  rw [← fifthPair_literal_integral hδ.le hδhi] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds (sub_lt_self _ hε))).exists
  refine ⟨n, hn.trans_le ?_⟩
  rw [fifthPair_step_integral, mul_sum]
  exact sum_le_sum (fun j hj => fifthPair_density_mass_le hδ hδhi hj)

/-- Full original fifth-term integral lower bound, with a single uniform threshold. -/
theorem fifthPair_actual_Fdelta_lower {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFdelta δ - ε) * truncatedSixthMassScale N ≤ (fifthPairCount N : ℝ) := by
  obtain ⟨n, hn⟩ := fifthPair_sum_sufficient hδ hδhi (half_pos hε)
  obtain ⟨T, hT, h⟩ := fifthPair_unperturbed_family_count hδ hδhi (half_pos hε) n
  refine ⟨T, hT, ?_⟩
  intro N hN he
  exact (mul_le_mul_of_nonneg_right (by linarith :
    fifthPairFdelta δ - ε ≤ fifthPairCellSum δ n - ε / 2)
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (h N hN he)

end Wu2008DoubleSieve
