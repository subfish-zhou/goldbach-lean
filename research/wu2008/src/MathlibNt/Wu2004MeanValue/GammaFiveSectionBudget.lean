import MathlibNt.Wu2004MeanValue.GammaFiveLossKernelIdentity
import MathlibNt.Wu2004MeanValue.GammaFiveLossBudgetTriangle
import MathlibNt.Wu2004MeanValue.GammaFiveLossBudgetMeasurable

/-!
# Paid bounds for full versus legal Gamma₅ sections

The four exact section differences inherit the triangular scalar budgets.
These are bounds on logarithmic section integrals. Their use in the original
count inequalities additionally requires identifying the full and legal
section integrals with the corresponding two-dimensional gains.
-/

namespace Wu2004MeanValue.GammaFiveLossBudget
open Set MeasureTheory
open scoped Interval

/-- Four-row bound for the explicit full-minus-legal section expressions.
The factor five converts the normalized scalar debit back to a gain debit. -/
theorem original_row_section_budget (i : Fin 4) (H : ℝ → ℝ)
    (hm : Measurable H)
    (hH : ∀ v ∈ Icc ((rowParameters i).1*(1-2*(rowParameters i).2))
      ((rowParameters i).1/3), 0 ≤ H v ∧ H v ≤ 1) :
    (∫ v in (1 : ℝ)..3,
      H v * (1/(v*(1-v/(rowParameters i).1))) *
        (fullSectionLog (rowParameters i).1 (rowParameters i).2 v -
          legalSectionLog (rowParameters i).1 (rowParameters i).2 v)) <
      5*rowDebit i/2 := by
  have hp : 0 < (rowParameters i).1 ∧ 1/3 ≤ (rowParameters i).2 ∧
      (rowParameters i).2 < 1/2 ∧
      5/4 ≤ (rowParameters i).1*(1-2*(rowParameters i).2) := by
    fin_cases i <;> norm_num [rowParameters]
  rw [weighted_section_loss_identity hp.1 hp.2.1 hp.2.2.1 hp.2.2.2]
  have hi := general_weighted_intervalIntegrable hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 H hm hH
  have hb := original_row_triangle_budget i H hH hi
  linarith

/-- Integrability of the legal section already implies integrability of the
full section: their difference is the compactly supported loss kernel. -/
theorem full_section_intervalIntegrable {S B a b : ℝ}
    (hS : 0 < S) (hB : 1/3 ≤ B) (hBhi : B < 1/2)
    (hA : 5/4 ≤ S*(1-2*B)) (H : ℝ → ℝ) (hm : Measurable H)
    (hH : ∀ v ∈ Icc (S*(1-2*B)) (S/3), 0 ≤ H v ∧ H v ≤ 1)
    (hlegal : IntervalIntegrable (fun v => H v * (1/(v*(1-v/S))) *
      legalSectionLog S B v) volume a b) :
    IntervalIntegrable (fun v => H v * (1/(v*(1-v/S))) *
      fullSectionLog S B v) volume a b := by
  have hloss : IntervalIntegrable (fun v => H v * generalKernel S B v) volume a b :=
    (general_weighted_integrable hS hB hBhi hA H hm hH).intervalIntegrable
  apply (hlegal.add (hloss.const_mul 5)).congr
  intro v _
  dsimp only
  have hk := full_sub_legal_kernel hS hB hBhi hA v
  have hh := congrArg (fun x => H v * x) hk
  nlinarith only [hh]

/-- An integrable legal section suffices to pay the full gain's loss. -/
theorem original_row_full_sub_legal_budget (i : Fin 4) (H : ℝ → ℝ)
    (hm : Measurable H)
    (hH : ∀ v ∈ Icc ((rowParameters i).1*(1-2*(rowParameters i).2))
      ((rowParameters i).1/3), 0 ≤ H v ∧ H v ≤ 1)
    (hlegal : IntervalIntegrable (fun v => H v * (1/(v*(1-v/(rowParameters i).1))) *
      legalSectionLog (rowParameters i).1 (rowParameters i).2 v) volume 1 3) :
    (∫ v in (1 : ℝ)..3, H v * (1/(v*(1-v/(rowParameters i).1))) *
      fullSectionLog (rowParameters i).1 (rowParameters i).2 v) -
    (∫ v in (1 : ℝ)..3, H v * (1/(v*(1-v/(rowParameters i).1))) *
      legalSectionLog (rowParameters i).1 (rowParameters i).2 v) < 5*rowDebit i/2 := by
  have hp : 0 < (rowParameters i).1 ∧ 1/3 ≤ (rowParameters i).2 ∧
      (rowParameters i).2 < 1/2 ∧
      5/4 ≤ (rowParameters i).1*(1-2*(rowParameters i).2) := by
    fin_cases i <;> norm_num [rowParameters]
  have hfull := full_section_intervalIntegrable hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 H hm hH hlegal
  rw [← intervalIntegral.integral_sub hfull hlegal]
  simpa only [mul_sub] using original_row_section_budget i H hm hH

end Wu2004MeanValue.GammaFiveLossBudget
