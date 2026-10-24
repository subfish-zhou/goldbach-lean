import WR2XiCorrectedPositive

/-! The exact Gamma5 correction changes only the first column and preserves positivity. -/
noncomputable section
namespace WuPaper.R2Xi
open Set MeasureTheory NodeExtension Wu2008DoubleSieve MotherPair
open Wu2004MeanValue.GammaFiveLossBudget
open scoped Interval BigOperators

def Xi2CorrectedCoefficient (r : Fin 4) (k : Fin 9) : ℝ :=
  Xi2Coefficient (gamma5OriginalRow r) k - if k = 0 then gamma5CellLoss r else 0

theorem Xi2_corrected_profile_expansion (r : Fin 4) (z : Fin 9 → ℝ) :
    (∫ t in (1:ℝ)..3, nineProfile z t * Xi2 (gamma5OriginalRow r) t) -
      (∫ t in (1:ℝ)..3, nineProfile z t *
        generalKernel (rowParameters r).1 (rowParameters r).2 t) =
      ∑ k : Fin 9, Xi2CorrectedCoefficient r k * z k := by
  have hp : WuPaper.RMapMMatrix.PropositionFourGeometry (gamma5OriginalRow r) :=
    WuPaper.RMapMMatrix.original_four_rows_qualified r
  rw [Xi2_profile_expansion hp,
    gamma5_profile_loss]
  simp only [Xi2CorrectedCoefficient, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib]
  simp [mul_comm]

theorem Xi2CorrectedCoefficient_nonneg (r : Fin 4) (k : Fin 9) :
    0 ≤ Xi2CorrectedCoefficient r k := by
  have hm : Measurable (nineProfile (nodeBasis k)) := by
    have he : nineProfile (nodeBasis k) =
        (Ioc (upperLeft k) (upperNode k)).indicator (fun _ => (1:ℝ)) :=
      funext (nineProfile_basis k)
    rw [he]
    exact measurable_const.indicator measurableSet_Ioc
  have hb (t : ℝ) : |nineProfile (nodeBasis k) t| ≤ 1 := by
    rw [nineProfile_basis]
    by_cases ht : t ∈ Ioc (upperLeft k) (upperNode k) <;> simp [ht]
  have h := Xi2_corrected_integral_nonneg r (nineProfile_integrable _) hm hb
    (fun t _ => nineProfile_nonneg (nodeBasis_nonneg k) t)
  rw [Xi2_corrected_profile_expansion] at h
  simpa [nodeBasis] using h

end WuPaper.R2Xi
