import WR2ClassicalFifthIntegerData

/-! Natural-number domain bounds for the original Fifth grids. -/
namespace WuPaper.FifthIntegerPayment

theorem grid_domain (branch : Branch) {i : ℕ} (hi : i < 1024) :
    0 < gridDenominator branch ∧
    2*gridDenominator branch ≤ gridNumerator branch i ∧
    200*gridNumerator branch i < 1327*gridDenominator branch := by
  cases branch <;> simp only [gridDenominator, gridNumerator] <;> omega

theorem extra_domain (branch : Branch) (hb : branch ≠ .initial)
    {i : ℕ} (hi : i < 1024) :
    4*gridDenominator branch ≤ gridNumerator branch i ∧
    gridNumerator branch i-4*gridDenominator branch ≤ gridDenominator branch := by
  cases branch with
  | initial => exact (hb rfl).elim
  | middle => simp only [gridDenominator, gridNumerator]; omega
  | terminal => simp only [gridDenominator, gridNumerator]; omega

theorem initial_ratio_domain {i : ℕ} (hi : i < 1024) :
    164800*gridNumerator .initial i < 828048*gridDenominator .initial ∧
    ratioDenominator .initial i ≤ ratioNumerator .initial i := by
  simp only [ratioNumerator, ratioDenominator, gridDenominator, gridNumerator]
  omega

theorem middle_ratio_domain {i : ℕ} (hi : i < 1024) :
    164800*gridNumerator .middle i < 828048*gridDenominator .middle ∧
    ratioDenominator .middle i ≤ ratioNumerator .middle i := by
  simp only [ratioNumerator, ratioDenominator, gridDenominator, gridNumerator]
  omega

theorem terminal_ratio_domain {i : ℕ} (hi : i < 1024) :
    200*gridNumerator .terminal i ≤ 1127*gridDenominator .terminal ∧
    ratioDenominator .terminal i ≤ ratioNumerator .terminal i := by
  simp only [ratioNumerator, ratioDenominator, gridDenominator, gridNumerator]
  omega

theorem ratio_domain (branch : Branch) {i : ℕ} (hi : i < 1024) :
    0 < ratioDenominator branch i ∧
    ratioDenominator branch i ≤ ratioNumerator branch i := by
  cases branch <;>
    simp only [ratioNumerator, ratioDenominator, gridDenominator, gridNumerator] <;>
    omega

end WuPaper.FifthIntegerPayment
