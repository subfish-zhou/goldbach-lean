import WR2XiSixthPayments
import WR2XiSixthPanels23
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_23 (j : Fin 32) : payment (32*23+j.val) ≤ panelBound (32*23+j.val) := by
  fin_cases j
  · convert panel_paid_736 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_737 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_738 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_739 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_740 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_741 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_742 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_743 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_744 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_745 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_746 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_747 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_748 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_749 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_750 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_751 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_752 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_753 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_754 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_755 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_756 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_757 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_758 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_759 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_760 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_761 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_762 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_763 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_764 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_765 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_766 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
  · convert panel_paid_767 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock23,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_23
