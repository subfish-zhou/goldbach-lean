import WR2XiSixthPayments
import WR2XiSixthPanels18
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_18 (j : Fin 32) : payment (32*18+j.val) ≤ panelBound (32*18+j.val) := by
  fin_cases j
  · convert panel_paid_576 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_577 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_578 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_579 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_580 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_581 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_582 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_583 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_584 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_585 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_586 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_587 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_588 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_589 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_590 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_591 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_592 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_593 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_594 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_595 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_596 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_597 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_598 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_599 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_600 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_601 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_602 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_603 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_604 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_605 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_606 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
  · convert panel_paid_607 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock18,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_18
