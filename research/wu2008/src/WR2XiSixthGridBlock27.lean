import WR2XiSixthPayments
import WR2XiSixthPanels27
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_27 (j : Fin 32) : payment (32*27+j.val) ≤ panelBound (32*27+j.val) := by
  fin_cases j
  · convert panel_paid_864 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_865 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_866 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_867 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_868 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_869 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_870 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_871 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_872 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_873 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_874 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_875 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_876 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_877 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_878 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_879 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_880 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_881 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_882 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_883 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_884 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_885 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_886 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_887 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_888 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_889 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_890 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_891 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_892 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_893 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_894 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
  · convert panel_paid_895 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock27,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_27
