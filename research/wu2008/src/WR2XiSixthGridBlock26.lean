import WR2XiSixthPayments
import WR2XiSixthPanels26
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_26 (j : Fin 32) : payment (32*26+j.val) ≤ panelBound (32*26+j.val) := by
  fin_cases j
  · convert panel_paid_832 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_833 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_834 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_835 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_836 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_837 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_838 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_839 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_840 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_841 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_842 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_843 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_844 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_845 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_846 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_847 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_848 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_849 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_850 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_851 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_852 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_853 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_854 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_855 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_856 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_857 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_858 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_859 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_860 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_861 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_862 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
  · convert panel_paid_863 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock26,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_26
