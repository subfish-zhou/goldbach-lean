import WR2XiMatrix

/-! The omitted Gamma5 region affects only the first cell of the nine-node profile. -/
noncomputable section
namespace WuPaper.R2Xi
open Set NodeExtension
open Wu2004MeanValue.GammaFiveLossBudget
open scoped Interval

/-- Exact normalized missing mass in the original scalar coordinates. -/
def gamma5CellLoss (r : Fin 4) : ℝ :=
  ∫ v in (1:ℝ)..3, generalKernel (rowParameters r).1 (rowParameters r).2 v

theorem gamma5_kernel_support_first_cell (r : Fin 4) :
    Function.support (generalKernel (rowParameters r).1 (rowParameters r).2) ⊆
      Ioc (upperLeft 0) (upperNode 0) := by
  have hp : 0 < (rowParameters r).1 ∧ 1/3 ≤ (rowParameters r).2 ∧
      (rowParameters r).2 < 1/2 ∧
      1 ≤ (rowParameters r).1*(1-2*(rowParameters r).2) ∧
      (rowParameters r).1/3 ≤ 11/5 := by
    fin_cases r <;> norm_num [rowParameters]
  intro v hv
  have h := generalKernel_support hp.1 hp.2.1 hp.2.2.1 hv
  have hlo := hp.2.2.2.1.trans_lt h.1
  have hhi := h.2.trans hp.2.2.2.2
  norm_num [upperLeft, upperNode] at *
  exact ⟨hlo, hhi⟩

/-- Every later basis column has zero loss; the first column carries the whole correction. -/
theorem gamma5_profile_loss (r : Fin 4) (z : Fin 9 → ℝ) :
    (∫ v in (1:ℝ)..3, nineProfile z v *
      generalKernel (rowParameters r).1 (rowParameters r).2 v) =
      z 0 * gamma5CellLoss r := by
  unfold gamma5CellLoss
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  by_cases h : generalKernel (rowParameters r).1 (rowParameters r).2 v = 0
  · simp only [h, mul_zero]
  · rw [nineProfile_cell z (gamma5_kernel_support_first_cell r h)]

theorem gamma5_basis_loss (r : Fin 4) (k : Fin 9) :
    (∫ v in (1:ℝ)..3, nineProfile (nodeBasis k) v *
      generalKernel (rowParameters r).1 (rowParameters r).2 v) =
      if k = 0 then gamma5CellLoss r else 0 := by
  rw [gamma5_profile_loss]
  by_cases h : k = 0 <;> simp [nodeBasis, h, eq_comm]

end WuPaper.R2Xi
