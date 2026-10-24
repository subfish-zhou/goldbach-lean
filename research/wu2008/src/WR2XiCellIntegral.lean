import WR2XiMatrix

/-! Matrix entries are ordinary integrals over their original node cells. -/
noncomputable section
namespace WuPaper.R2Xi
open Set MeasureTheory NodeExtension Wu2008DoubleSieve
open scoped Interval

theorem basis_integral_eq_cell (k : Fin 9) (f : ℝ → ℝ) :
    (∫ t in (1:ℝ)..3, nineProfile (nodeBasis k) t * f t) =
      ∫ t in upperLeft k..upperNode k, f t := by
  have hb : 1 ≤ upperLeft k ∧ upperLeft k ≤ upperNode k ∧ upperNode k ≤ 3 := by
    fin_cases k <;> norm_num [upperLeft, upperNode]
  have he (t : ℝ) : nineProfile (nodeBasis k) t * f t =
      (Ioc (upperLeft k) (upperNode k)).indicator f t := by
    rw [nineProfile_basis]
    by_cases ht : t ∈ Ioc (upperLeft k) (upperNode k) <;> simp [ht]
  simp_rw [he]
  rw [intervalIntegral.integral_eq_integral_of_support_subset]
  · rw [MeasureTheory.integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_le hb.2.1]
  · intro t ht
    have hc : t ∈ Ioc (upperLeft k) (upperNode k) := by
      by_contra hn
      exact ht (indicator_of_notMem hn f)
    exact ⟨hb.1.trans_lt hc.1, hc.2.trans hb.2.2⟩

theorem Xi2Coefficient_eq_cell (p : SecondFunctionalParameters) (k : Fin 9) :
    Xi2Coefficient p k = ∫ t in upperLeft k..upperNode k, Xi2 p t :=
  basis_integral_eq_cell k (Xi2 p)

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.Xi2Coefficient_eq_cell
