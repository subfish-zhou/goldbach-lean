import WR2XiSixthPayments
import WR2XiSixthPanels17
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_17 (j : Fin 32) : payment (32*17+j.val) ≤ panelBound (32*17+j.val) := by
  fin_cases j
  · convert panel_paid_544 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_545 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_546 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_547 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_548 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_549 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_550 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_551 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_552 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_553 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_554 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_555 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_556 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_557 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_558 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_559 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_560 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_561 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_562 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_563 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_564 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_565 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_566 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_567 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_568 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_569 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_570 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_571 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_572 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_573 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_574 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
  · convert panel_paid_575 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock17,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_17
