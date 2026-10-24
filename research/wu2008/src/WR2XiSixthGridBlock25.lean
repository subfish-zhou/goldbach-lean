import WR2XiSixthPayments
import WR2XiSixthPanels25
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_25 (j : Fin 32) : payment (32*25+j.val) ≤ panelBound (32*25+j.val) := by
  fin_cases j
  · convert panel_paid_800 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_801 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_802 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_803 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_804 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_805 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_806 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_807 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_808 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_809 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_810 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_811 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_812 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_813 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_814 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_815 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_816 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_817 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_818 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_819 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_820 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_821 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_822 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_823 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_824 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_825 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_826 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_827 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_828 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_829 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_830 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
  · convert panel_paid_831 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock25,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_25
