import MathlibNt.Wu2008DoubleSieve.TruncatedSixthTableBoundary

/-!
# Zero-delta limits of the nine explicit integrals

The dominated-convergence argument varies only the explicit coefficient
map and admissible geometry, never the actual improvement functions.
-/

namespace Wu2008DoubleSieve

open Set Real Filter MeasureTheory
open scoped Classical Topology BigOperators

theorem truncatedSixthTable_beta_right_limit (j : Fin 9) :
    Tendsto (fun δ => truncatedSixthTableBeta δ j) (𝓝[>] (0 : ℝ))
      (𝓝 (truncatedSixthTableBeta 0 j)) := by
  obtain ⟨C, _, hi, hb⟩ := truncatedSixthTable_kernel_dominator j
  have hlim : Tendsto (fun δ => ∫ v : ℝ × ℝ, truncatedSixthTableKernel δ j v)
      (𝓝 (0 : ℝ)) (𝓝 (∫ v : ℝ × ℝ, truncatedSixthTableKernel 0 j v)) :=
    tendsto_integral_filter_of_dominated_convergence
      (truncatedSixthTableRectangle.indicator (fun _ => C))
      (Eventually.of_forall (fun δ => (truncatedSixthTable_kernel_measurable δ j).aestronglyMeasurable))
      (Eventually.of_forall (fun δ => Eventually.of_forall (hb δ))) hi
      (truncatedSixthTable_kernel_ae_limit j)
  have hscaled := (hlim.const_mul 4).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rw [← truncatedSixthTable_beta_integral (le_refl 0) j] at hscaled
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (truncatedSixthTable_beta_integral (le_of_lt hδ) j).symm

theorem truncatedSixthTable_beta_close {ε : ℝ} (hε : 0 < ε) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ < δ0 →
        ∀ j : Fin 9, |truncatedSixthTableBeta δ j - truncatedSixthTableBeta 0 j| < ε := by
  have hsum : Tendsto (fun δ => ∑ j : Fin 9,
      |truncatedSixthTableBeta δ j - truncatedSixthTableBeta 0 j|)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have ht := tendsto_finsetSum Finset.univ (fun j _ =>
      ((truncatedSixthTable_beta_right_limit j).sub_const (truncatedSixthTableBeta 0 j)).abs)
    simpa only [sub_self, abs_zero, Finset.sum_const_zero] using ht
  obtain ⟨r, hr, hc⟩ := Metric.tendsto_nhdsWithin_nhds.mp hsum ε hε
  refine ⟨min r (1 / 100), lt_min hr (by norm_num), min_le_right _ _, ?_⟩
  intro δ hδ hsmall j
  have hd : dist δ 0 < r := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hδ] using hsmall.trans_le (min_le_left _ _)
  have he := hc hδ hd
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (Finset.sum_nonneg (fun k _ => abs_nonneg
      (truncatedSixthTableBeta δ k - truncatedSixthTableBeta 0 k)))] at he
  exact (Finset.single_le_sum (fun k _ => abs_nonneg
    (truncatedSixthTableBeta δ k - truncatedSixthTableBeta 0 k)) (Finset.mem_univ j)).trans_lt he

end Wu2008DoubleSieve
