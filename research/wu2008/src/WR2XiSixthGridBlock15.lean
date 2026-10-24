import WR2XiSixthPayments
import WR2XiSixthPanels15
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_15 (j : Fin 32) : payment (32*15+j.val) ≤ panelBound (32*15+j.val) := by
  fin_cases j
  · convert panel_paid_480 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_481 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_482 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_483 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_484 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_485 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_486 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_487 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_488 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_489 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_490 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_491 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_492 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_493 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_494 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_495 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_496 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_497 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_498 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_499 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_500 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_501 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_502 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_503 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_504 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_505 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_506 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_507 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_508 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_509 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_510 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
  · convert panel_paid_511 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock15,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_15
