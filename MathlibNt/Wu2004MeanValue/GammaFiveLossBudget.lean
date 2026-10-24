import MathlibNt.Wu2004MeanValue.GammaFiveLossBudgetGeneral

/-!
# Fourth-row Gamma₅ loss budget

This is the fourth-row specialization of the common four-row estimate.
The explicit kernel formula is retained for identification with the research
kernel. It includes the second functional's factor 1/5. Supplying the actual
improvement function and proving the count bridge are separate steps.
-/

namespace Wu2004MeanValue.GammaFiveLossBudget

open Real Set MeasureTheory
open scoped Interval

noncomputable def kernel (v : ℝ) : ℝ :=
  if 9373/7275 ≤ v ∧ v ≤ 19673/14550 then
    (1 / (v * (1 - v / (103/25)))) *
      log ((103/25) / ((291/100)*(103/25) - (103/25) - (291/100)*v)) / 5
  else if 19673/14550 < v ∧ v < 103/75 then
    (1 / (v * (1 - v / (103/25)))) * log (((103/25) - 2*v) / v) / 5
  else 0


theorem kernel_eq_general : kernel = generalKernel (103/25) (100/291) := by
  funext v
  have hr : (103/25 : ℝ) / ((291/100)*(103/25)-(103/25)-(291/100)*v) =
      (100/291 : ℝ) / (1-v/(103/25)-100/291) := by
    have he : (291/100 : ℝ)*(103/25)-(103/25)-(291/100)*v =
        ((291/100)*(103/25))*(1-v/(103/25)-100/291) := by ring
    rw [he, div_mul_eq_div_div]
    norm_num
  unfold kernel generalKernel
  rw [hr]
  norm_num only [show (103/25 : ℝ)*(1-2*(100/291))=9373/7275 by norm_num,
    show (103/25 : ℝ)*(1-100/291)/2=19673/14550 by norm_num,
    show (103/25 : ℝ)/3=103/75 by norm_num]

theorem kernel_upper (v : ℝ) : kernel v ≤ 54/4775 := by
  rw [kernel_eq_general]
  have h := generalKernel_upper (S := 103/25) (B := 100/291)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) v
  norm_num at h ⊢
  exact h

theorem kernel_support : Function.support kernel ⊆ Ioc (9373/7275 : ℝ) (103/75) := by
  rw [kernel_eq_general]
  have h := generalKernel_support (S := 103/25) (B := 100/291)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem weighted_integral_bound (H : ℝ → ℝ)
    (hH : ∀ v ∈ Icc (9373/7275 : ℝ) (103/75), 0 ≤ H v ∧ H v ≤ 1)
    (hi : IntervalIntegrable (fun v => H v * kernel v) volume (9373/7275) (103/75)) :
    (∫ v in (1 : ℝ)..3, H v * kernel v) < 1/1000 := by
  rw [kernel_eq_general] at hi ⊢
  have h := original_row_budget (3 : Fin 4) H
  rw [show rowParameters (3 : Fin 4) = ((103/25 : ℝ), (100/291 : ℝ)) from rfl,
    show rowDebit (3 : Fin 4) = (1/1000 : ℝ) from rfl] at h
  norm_num only [Prod.fst, Prod.snd] at h
  exact h hH hi

end Wu2004MeanValue.GammaFiveLossBudget
