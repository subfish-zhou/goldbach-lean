import WR2XiSixthPayments
import WR2XiSixthPanels22
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_22 (j : Fin 32) : payment (32*22+j.val) ≤ panelBound (32*22+j.val) := by
  fin_cases j
  · convert panel_paid_704 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_705 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_706 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_707 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_708 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_709 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_710 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_711 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_712 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_713 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_714 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_715 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_716 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_717 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_718 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_719 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_720 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_721 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_722 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_723 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_724 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_725 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_726 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_727 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_728 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_729 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_730 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_731 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_732 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_733 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_734 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
  · convert panel_paid_735 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock22,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_22
