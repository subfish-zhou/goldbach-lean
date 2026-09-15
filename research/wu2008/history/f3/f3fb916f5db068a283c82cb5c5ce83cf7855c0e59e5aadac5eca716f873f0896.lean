import MathlibNt.Wu2008DoubleSieve.TruncatedSixthTableContinuous

/-!
# Nine literal admissible-region integrals

The regularized kernel is auxiliary. On the actual region it equals
the literal density, including at delta zero. The factor is four.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Classical Topology BigOperators

noncomputable def truncatedSixthTableBeta (δ : ℝ) (j : Fin 9) : ℝ :=
  4 * ∫ x in truncatedSixthLowerAlpha..truncatedSixthLowerBeta,
    ∫ y in truncatedSixthLowerBeta..truncatedSixthLowerSigma,
      if truncatedSixthLowerAdmissibleRegion δ x y then
        tableGainB (truncatedSixthLowerS δ x y) j /
          (x * y * (truncatedSixthLowerC δ - x - y)) else 0

noncomputable def truncatedSixthTableKernel (δ : ℝ) (j : Fin 9) (v : ℝ × ℝ) : ℝ :=
  if truncatedSixthLowerAdmissibleRegion δ v.1 v.2 then
    truncatedSixthTableRegular δ j v else 0

def truncatedSixthTableRectangle : Set (ℝ × ℝ) :=
  Icc truncatedSixthLowerAlpha truncatedSixthLowerBeta ×ˢ
    Icc truncatedSixthLowerBeta truncatedSixthLowerSigma

theorem truncatedSixthTable_kernel_measurable (δ : ℝ) (j : Fin 9) :
    Measurable (truncatedSixthTableKernel δ j) := by
  have hc : Continuous (truncatedSixthTableRegular δ j) :=
    (truncatedSixthTable_regular_continuous j).comp
      (f := fun v : ℝ × ℝ => (δ, v)) (continuous_const.prodMk continuous_id)
  exact hc.measurable.ite (truncatedSixthMass_regions_measurable δ).2 measurable_const

theorem truncatedSixthTable_kernel_nonneg (δ : ℝ) (j : Fin 9) (v : ℝ × ℝ) :
    0 ≤ truncatedSixthTableKernel δ j v := by
  unfold truncatedSixthTableKernel
  split_ifs
  · exact truncatedSixthTable_regular_nonneg δ j v
  · exact le_rfl

theorem truncatedSixthTable_kernel_support (δ : ℝ) (j : Fin 9) :
    Function.support (truncatedSixthTableKernel δ j) ⊆ truncatedSixthTableRectangle := by
  intro v hv
  by_cases hr : truncatedSixthLowerAdmissibleRegion δ v.1 v.2
  · exact ⟨⟨hr.1.1, hr.1.2.1⟩, ⟨hr.1.2.2.1, hr.1.2.2.2.1⟩⟩
  · exact False.elim (hv (by simp [truncatedSixthTableKernel, hr]))

theorem truncatedSixthTable_kernel_dominator (j : Fin 9) :
    ∃ C : ℝ, 0 ≤ C ∧
      Integrable (truncatedSixthTableRectangle.indicator (fun _ => C)) ∧
      ∀ δ v, ‖truncatedSixthTableKernel δ j v‖ ≤
        truncatedSixthTableRectangle.indicator (fun _ => C) v := by
  obtain ⟨C, hC, hb⟩ := truncatedSixthTable_regular_bound j
  have hm : MeasurableSet truncatedSixthTableRectangle :=
    measurableSet_Icc.prod measurableSet_Icc
  have hfin : volume truncatedSixthTableRectangle < ⊤ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  refine ⟨C, hC, (integrable_indicator_iff hm).mpr
    (integrableOn_const hfin.ne), ?_⟩
  intro δ v
  rw [Real.norm_eq_abs, abs_of_nonneg (truncatedSixthTable_kernel_nonneg δ j v)]
  by_cases hv : v ∈ truncatedSixthTableRectangle
  · rw [indicator_of_mem hv]
    unfold truncatedSixthTableKernel
    split_ifs
    · exact hb δ v
    · exact hC
  · rw [indicator_of_notMem hv]
    have he : truncatedSixthTableKernel δ j v = 0 := by
      by_contra hn
      exact hv (truncatedSixthTable_kernel_support δ j hn)
    rw [he]

theorem truncatedSixthTable_kernel_integrable (δ : ℝ) (j : Fin 9) :
    Integrable (truncatedSixthTableKernel δ j) := by
  obtain ⟨C, _, hi, hb⟩ := truncatedSixthTable_kernel_dominator j
  exact hi.mono' (truncatedSixthTable_kernel_measurable δ j).aestronglyMeasurable
    (Filter.Eventually.of_forall (hb δ))

theorem truncatedSixthTable_kernel_literal {δ : ℝ} (hδ : 0 ≤ δ)
    (j : Fin 9) (v : ℝ × ℝ) :
    truncatedSixthTableKernel δ j v =
      if truncatedSixthLowerAdmissibleRegion δ v.1 v.2 then
        tableGainB (truncatedSixthLowerS δ v.1 v.2) j /
          (v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2)) else 0 := by
  unfold truncatedSixthTableKernel
  split_ifs with hr
  · exact truncatedSixthTable_regular_eq hδ j hr.1
  · rfl

theorem truncatedSixthTable_beta_integral {δ : ℝ} (hδ : 0 ≤ δ) (j : Fin 9) :
    truncatedSixthTableBeta δ j =
      4 * ∫ v : ℝ × ℝ, truncatedSixthTableKernel δ j v := by
  have hp := truncatedSixthLower_parameters
  have hinner (x : ℝ) : Function.support (fun y => truncatedSixthTableKernel δ j (x, y)) ⊆
      Icc truncatedSixthLowerBeta truncatedSixthLowerSigma := by
    intro y hy
    exact (truncatedSixthTable_kernel_support δ j hy).2
  have houter : Function.support (fun x => ∫ y, truncatedSixthTableKernel δ j (x, y)) ⊆
      Icc truncatedSixthLowerAlpha truncatedSixthLowerBeta := by
    intro x hx
    by_contra hn
    apply hx
    change (∫ y, truncatedSixthTableKernel δ j (x, y)) = 0
    have hz : (fun y => truncatedSixthTableKernel δ j (x, y)) = 0 := by
      funext y
      by_contra h
      exact hn (truncatedSixthTable_kernel_support δ j h).1
    rw [hz]
    simp
  rw [show (∫ v : ℝ × ℝ, truncatedSixthTableKernel δ j v) =
      ∫ x, ∫ y, truncatedSixthTableKernel δ j (x, y) from
      integral_prod _ (truncatedSixthTable_kernel_integrable δ j),
    truncatedSixthMass_integral_eq_interval hp.2.1.le houter]
  simp_rw [truncatedSixthMass_integral_eq_interval hp.2.2.1.le (hinner _),
    truncatedSixthTable_kernel_literal hδ]
  rfl

theorem truncatedSixthTable_beta_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (j : Fin 9) :
    0 ≤ truncatedSixthTableBeta δ j := by
  rw [truncatedSixthTable_beta_integral hδ]
  exact mul_nonneg (by norm_num) (integral_nonneg (truncatedSixthTable_kernel_nonneg δ j))

end Wu2008DoubleSieve
