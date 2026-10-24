import WR2XiSixthPayments
import WR2XiSixthPanels13
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_13 (j : Fin 32) : payment (32*13+j.val) ≤ panelBound (32*13+j.val) := by
  fin_cases j
  · convert panel_paid_416 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_417 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_418 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_419 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_420 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_421 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_422 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_423 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_424 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_425 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_426 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_427 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_428 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_429 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_430 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_431 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_432 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_433 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_434 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_435 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_436 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_437 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_438 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_439 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_440 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_441 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_442 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_443 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_444 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_445 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_446 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
  · convert panel_paid_447 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock13,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_13
