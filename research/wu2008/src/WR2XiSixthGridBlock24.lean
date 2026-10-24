import WR2XiSixthPayments
import WR2XiSixthPanels24
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_24 (j : Fin 32) : payment (32*24+j.val) ≤ panelBound (32*24+j.val) := by
  fin_cases j
  · convert panel_paid_768 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_769 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_770 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_771 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_772 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_773 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_774 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_775 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_776 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_777 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_778 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_779 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_780 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_781 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_782 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_783 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_784 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_785 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_786 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_787 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_788 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_789 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_790 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_791 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_792 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_793 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_794 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_795 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_796 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_797 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_798 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
  · convert panel_paid_799 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock24,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_24
