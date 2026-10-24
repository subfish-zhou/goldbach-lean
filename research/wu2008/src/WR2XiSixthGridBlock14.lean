import WR2XiSixthPayments
import WR2XiSixthPanels14
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_14 (j : Fin 32) : payment (32*14+j.val) ≤ panelBound (32*14+j.val) := by
  fin_cases j
  · convert panel_paid_448 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_449 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_450 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_451 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_452 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_453 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_454 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_455 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_456 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_457 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_458 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_459 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_460 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_461 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_462 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_463 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_464 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_465 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_466 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_467 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_468 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_469 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_470 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_471 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_472 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_473 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_474 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_475 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_476 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_477 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_478 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
  · convert panel_paid_479 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock14,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_14
