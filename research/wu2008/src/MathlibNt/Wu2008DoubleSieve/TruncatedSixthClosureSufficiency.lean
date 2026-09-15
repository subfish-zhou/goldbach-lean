import MathlibNt.Wu2008DoubleSieve.TruncatedSixthClosureDCT

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory
open scoped Classical Topology

noncomputable def truncatedSixthClosureRcoef (δ : ℝ) (n : ℕ) (j : ℕ × ℕ) : ℝ :=
  truncatedSixthMassRectangleCoefficient δ
    (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
    (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2)

noncomputable def truncatedSixthClosureSum (gain : Bool) (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ truncatedSixthClosureInner gain δ n,
    truncatedSixthClosureWeight gain δ n j * truncatedSixthClosureRcoef δ n j

theorem truncatedSixthClosure_inner_geometry {gain : Bool} {δ : ℝ} {n : ℕ} {j : ℕ × ℕ}
    (hj : j ∈ truncatedSixthClosureInner gain δ n) :
    truncatedSixthLowerAlpha ≤ truncatedSixthClosureLo n j.1 ∧
      truncatedSixthLowerBeta ≤ truncatedSixthClosureLo n j.2 ∧
      truncatedSixthLowerRegion δ (truncatedSixthClosureHi n j.1) (truncatedSixthClosureHi n j.2) := by
  have hl := truncatedSixthClosure_region_bounds (Finset.mem_filter.mp hj).2.1
  exact ⟨hl.1, hl.2.2.1, truncatedSixthClosure_region_bounds (Finset.mem_filter.mp hj).2.2⟩

theorem truncatedSixthClosure_rcoef_nonneg {gain : Bool} {δ : ℝ} {n : ℕ} {j : ℕ × ℕ}
    (hj : j ∈ truncatedSixthClosureInner gain δ n) :
    0 ≤ truncatedSixthClosureRcoef δ n j := by
  have hg := truncatedSixthClosure_inner_geometry hj
  have hα := truncatedSixthLower_parameters.1
  have ha := hα.trans_le hg.1
  have hc := (hα.trans truncatedSixthLower_parameters.2.1).trans_le hg.2.1
  have hab := (truncatedSixthClosure_lo_lt_hi n j.1).le
  have hcd := (truncatedSixthClosure_lo_lt_hi n j.2).le
  have hden : 0 < truncatedSixthLowerC δ - truncatedSixthClosureLo n j.1 -
      truncatedSixthClosureLo n j.2 := by linarith [hg.2.2.2.2.2.2]
  have hlog1 := log_nonneg ((one_le_div ha).mpr hab)
  have hlog2 := log_nonneg ((one_le_div hc).mpr hcd)
  unfold truncatedSixthClosureRcoef truncatedSixthMassRectangleCoefficient
  positivity

theorem truncatedSixthClosure_log_lower {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / b ≤ log (b / a) := by
  have hb := ha.trans_le hab
  have h := one_sub_inv_le_log_of_pos (div_pos hb ha)
  calc
    _ = 1 - (b / a)⁻¹ := by field_simp
    _ ≤ _ := h

theorem truncatedSixthClosure_density_mass_le {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) {gain : Bool} {n : ℕ} {j : ℕ × ℕ}
    (hj : j ∈ truncatedSixthClosureInner gain δ n) :
    4 * (volume.real (truncatedSixthClosureCell n j) *
      truncatedSixthClosureDensity gain δ n j) ≤
      truncatedSixthClosureWeight gain δ n j * truncatedSixthClosureRcoef δ n j := by
  have hg := truncatedSixthClosure_inner_geometry hj
  have hα := truncatedSixthLower_parameters.1
  have ha := hα.trans_le hg.1
  have hc := (hα.trans truncatedSixthLower_parameters.2.1).trans_le hg.2.1
  have hab := (truncatedSixthClosure_lo_lt_hi n j.1).le
  have hcd := (truncatedSixthClosure_lo_lt_hi n j.2).le
  have hb := ha.trans_le hab
  have hd := hc.trans_le hcd
  have hden : 2 * truncatedSixthLowerAlpha ≤ truncatedSixthLowerC δ -
      truncatedSixthClosureLo n j.1 - truncatedSixthClosureLo n j.2 := by
    linarith [hg.2.2.2.2.2.2]
  have hden0 : 0 < truncatedSixthLowerC δ -
      truncatedSixthClosureLo n j.1 - truncatedSixthClosureLo n j.2 := by linarith
  have hw := (truncatedSixthClosure_weight_bounds hδ hδhi gain n j).1
  have hlogs := mul_le_mul (truncatedSixthClosure_log_lower ha hab)
    (truncatedSixthClosure_log_lower hc hcd)
    (div_nonneg (sub_nonneg.mpr hcd) hd.le)
    (log_nonneg ((one_le_div ha).mpr hab))
  have hbound := mul_le_mul_of_nonneg_left hlogs
    (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hw) hden0.le)
  rw [truncatedSixthClosure_cell_volume]
  unfold truncatedSixthClosureDensity truncatedSixthClosureRcoef truncatedSixthMassRectangleCoefficient
  simp only [truncatedSixthClosureLower, truncatedSixthClosureUpper,
    max_eq_right (hg.1.trans hab), max_eq_right (hg.2.1.trans hcd), max_eq_right hden]
  convert hbound using 1
  · rfl
  · simp only [div_eq_mul_inv, mul_inv]
    ring
  · ring

theorem truncatedSixthClosure_step_integral (gain : Bool) (δ : ℝ) (n : ℕ) :
    (∫ v : ℝ × ℝ, truncatedSixthClosureStep gain δ n v) =
      ∑ j ∈ truncatedSixthClosureInner gain δ n,
        volume.real (truncatedSixthClosureCell n j) * truncatedSixthClosureDensity gain δ n j := by
  unfold truncatedSixthClosureStep
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

theorem truncatedSixthClosure_sum_sufficient {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (hε : 0 < ε) :
    ∃ n : ℕ, truncatedSixthLowerFdelta δ + truncatedSixthLowerHadmdelta δ - ε <
      truncatedSixthClosureSum false δ n + truncatedSixthClosureSum true δ n := by
  have hlim := ((truncatedSixthClosure_integral_tendsto hδ hδhi false).const_mul 4).add
    ((truncatedSixthClosure_integral_tendsto hδ hδhi true).const_mul 4)
  have hid : 4 * (∫ v : ℝ × ℝ, truncatedSixthClosureKernel false δ v) +
      4 * (∫ v : ℝ × ℝ, truncatedSixthClosureKernel true δ v) =
      truncatedSixthLowerFdelta δ + truncatedSixthLowerHadmdelta δ := by
    simp only [truncatedSixthClosure_kernel_eq hδ.le, Bool.false_eq_true, if_false, if_true]
    exact (truncatedSixthMass_literal_disjoint_integral hδ hδhi).symm
  rw [hid] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds (sub_lt_self _ hε))).exists
  refine ⟨n, hn.trans_le (add_le_add ?_ ?_)⟩
  all_goals
    rw [truncatedSixthClosure_step_integral, mul_sum]
    exact sum_le_sum (fun j hj => truncatedSixthClosure_density_mass_le hδ hδhi hj)

end Wu2008DoubleSieve
