import MathlibNt.Wu2004MeanValue.GammaFiveLossBudgetGeneral

/-!
# Gamma₅ budgets for bounded measurable weights

The loss kernel is nonnegative and measurable. Its existing uniform bound
therefore gives interval integrability for every measurable weight taking
values in [0, 1] on the loss interval. The four rational row budgets can be
used without a separate integrability hypothesis.

Identifying these kernels with the actual count gains remains a separate
requirement; this module only discharges the analytic integrability step.
-/

open Real Set MeasureTheory
open scoped Interval
namespace Wu2004MeanValue.GammaFiveLossBudget

theorem generalKernel_nonneg {S B : ℝ} (hS : 0 < S) (hB : 1/3 ≤ B)
    (hBhi : B < 1/2) (v : ℝ) : 0 ≤ generalKernel S B v := by
  have hB0 : 0 < B := by linarith
  have hstart : 0 < S*(1-2*B) := mul_pos hS (by linarith)
  have hmid : S*(1-2*B) ≤ S*(1-B)/2 := by nlinarith
  have hend : S*(1-B)/2 ≤ S/3 := by nlinarith
  have hp {v : ℝ} (hv : 0 < v) (he : v ≤ S/3) : 0 ≤ 1/(v*(1-v/S)) := by
    have hh : v/S ≤ 1/3 := (div_le_iff₀ hS).mpr (by linarith)
    exact div_nonneg (by norm_num) (mul_nonneg hv.le (by linarith))
  unfold generalKernel
  split_ifs with h h
  · have hvS : v/S ≤ (1-B)/2 := (div_le_iff₀ hS).mpr (by nlinarith [h.2])
    have hd : 0 < 1-v/S-B := by linarith
    have hl : 1-2*B ≤ v/S := (le_div_iff₀ hS).mpr (by nlinarith [h.1])
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg (hp (hstart.trans_le h.1) (h.2.trans hend))
    exact Real.log_nonneg ((le_div_iff₀ hd).mpr (by linarith))
  · have hv : 0 < v := hstart.trans_le (hmid.trans h.1.le)
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg (hp hv h.2.le)
    exact Real.log_nonneg ((le_div_iff₀ hv).mpr (by linarith [h.2]))
  · exact le_rfl

theorem generalKernel_measurable (S B : ℝ) : Measurable (generalKernel S B) := by
  unfold generalKernel
  apply Measurable.ite (measurableSet_Icc) _ ?_
  · fun_prop
  · apply Measurable.ite (measurableSet_Ioo) _ measurable_const
    fun_prop

/-- Bounded measurable weights need no separate integrability certificate. -/
theorem general_weighted_intervalIntegrable {S B : ℝ}
    (hS : 0 < S) (hB : 1/3 ≤ B) (hBhi : B < 1/2)
    (hA : 5/4 ≤ S*(1-2*B)) (H : ℝ → ℝ) (hm : Measurable H)
    (hH : ∀ v ∈ Icc (S*(1-2*B)) (S/3), 0 ≤ H v ∧ H v ≤ 1) :
    IntervalIntegrable (fun v => H v * generalKernel S B v)
      volume (S*(1-2*B)) (S/3) := by
  have hab : S*(1-2*B) ≤ S/3 := by nlinarith
  apply (intervalIntegrable_const (c := (6/25 : ℝ)*((3*B-1)/(1-B)))).mono_fun'
    (hm.mul (generalKernel_measurable S B)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
  have hv' : v ∈ Icc (S*(1-2*B)) (S/3) := by
    rw [uIoc_of_le hab] at hv
    exact ⟨hv.1.le,hv.2⟩
  have hk := generalKernel_nonneg hS hB hBhi v
  rw [Real.norm_eq_abs, Pi.mul_apply, abs_of_nonneg (mul_nonneg (hH v hv').1 hk)]
  exact (mul_le_of_le_one_left hk (hH v hv').2).trans
    (generalKernel_upper hS hB hBhi hA v)

/-- Compact support upgrades interval integrability to integrability on ℝ.
No bound on H outside the loss interval is needed. -/
theorem general_weighted_integrable {S B : ℝ}
    (hS : 0 < S) (hB : 1/3 ≤ B) (hBhi : B < 1/2)
    (hA : 5/4 ≤ S*(1-2*B)) (H : ℝ → ℝ) (hm : Measurable H)
    (hH : ∀ v ∈ Icc (S*(1-2*B)) (S/3), 0 ≤ H v ∧ H v ≤ 1) :
    Integrable (fun v => H v * generalKernel S B v) := by
  have hs : Function.support (fun v => H v * generalKernel S B v) ⊆
      Ioc (S*(1-2*B)) (S/3) := by
    intro v hv
    apply generalKernel_support hS hB hBhi
    intro he
    exact hv (by simp only [he, mul_zero])
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  exact (general_weighted_intervalIntegrable hS hB hBhi hA H hm hH).1

/-- The four original budgets applied directly to measurable improvement functions. -/
theorem original_row_budget_of_measurable (i : Fin 4) (H : ℝ → ℝ)
    (hm : Measurable H)
    (hH : ∀ v ∈ Icc ((rowParameters i).1*(1-2*(rowParameters i).2))
      ((rowParameters i).1/3), 0 ≤ H v ∧ H v ≤ 1) :
    (∫ v in (1 : ℝ)..3, H v * generalKernel (rowParameters i).1
      (rowParameters i).2 v) < rowDebit i := by
  apply original_row_budget i H hH
  have hp : 0 < (rowParameters i).1 ∧ 1/3 ≤ (rowParameters i).2 ∧
      (rowParameters i).2 < 1/2 ∧ 5/4 ≤ (rowParameters i).1*(1-2*(rowParameters i).2) := by
    fin_cases i <;> norm_num [rowParameters]
  exact general_weighted_intervalIntegrable hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 H hm hH

end Wu2004MeanValue.GammaFiveLossBudget
