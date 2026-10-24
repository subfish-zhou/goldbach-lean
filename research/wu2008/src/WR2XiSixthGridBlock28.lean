import WR2XiSixthPayments
import WR2XiSixthPanels28
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_28 (j : Fin 32) : payment (32*28+j.val) ≤ panelBound (32*28+j.val) := by
  fin_cases j
  · convert panel_paid_896 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_897 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_898 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_899 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_900 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_901 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_902 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_903 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_904 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_905 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_906 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_907 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_908 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_909 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_910 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_911 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_912 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_913 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_914 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_915 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_916 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_917 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_918 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_919 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_920 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_921 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_922 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_923 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_924 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_925 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_926 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
  · convert panel_paid_927 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock28,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_28
