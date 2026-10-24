import WR2XiPieces

/-! The original Xi2 sigma term uses the same aProfile as the first-functional certificates. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension WuPaper.RMapMSigma
open scoped Interval

theorem xi2Sigma_integrable (p : SecondFunctionalParameters) :
    IntervalIntegrable (xi2SigmaKernel p) volume 1 3 := by
  have h := (sigma_weight_integrable (intervalIntegrable_const (c := (1:ℝ)))).mul_const
    (log (1024 / xi2ParameterProduct p) / 5)
  apply h.congr
  intro t _
  unfold xi2SigmaKernel
  ring

theorem xi2Sigma_cell_integrable (p : SecondFunctionalParameters) (k : Fin 9) :
    IntervalIntegrable (xi2SigmaKernel p) volume (upperLeft k) (upperNode k) := by
  have hb : 1 ≤ upperLeft k ∧ upperLeft k ≤ upperNode k ∧ upperNode k ≤ 3 := by
    fin_cases k <;> norm_num [upperLeft, upperNode]
  apply (xi2Sigma_integrable p).mono_set
  rw [uIcc_of_le hb.2.1, uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)]
  exact fun t ht => ⟨hb.1.trans ht.1, ht.2.trans hb.2.2⟩

theorem xi2Sigma_cell_eq (p : SecondFunctionalParameters) (k : Fin 9) :
    (∫ t in upperLeft k..upperNode k, xi2SigmaKernel p t) =
      (log (1024 / xi2ParameterProduct p) / 5) * aProfile (nineProfile (nodeBasis k)) := by
  rw [← basis_integral_eq_cell k (xi2SigmaKernel p)]
  unfold aProfile
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  unfold xi2SigmaKernel
  ring

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.xi2Sigma_cell_integrable
#print axioms WuPaper.R2Xi.xi2Sigma_cell_eq
