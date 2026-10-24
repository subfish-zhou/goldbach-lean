import WR2XiSixthPayments
import WR2XiSixthPanels20
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_20 (j : Fin 32) : payment (32*20+j.val) ≤ panelBound (32*20+j.val) := by
  fin_cases j
  · convert panel_paid_640 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_641 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_642 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_643 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_644 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_645 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_646 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_647 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_648 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_649 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_650 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_651 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_652 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_653 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_654 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_655 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_656 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_657 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_658 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_659 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_660 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_661 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_662 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_663 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_664 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_665 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_666 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_667 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_668 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_669 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_670 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
  · convert panel_paid_671 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock20,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_20
