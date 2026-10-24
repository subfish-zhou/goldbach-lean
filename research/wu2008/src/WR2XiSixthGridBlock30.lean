import WR2XiSixthPayments
import WR2XiSixthPanels30
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_30 (j : Fin 32) : payment (32*30+j.val) ≤ panelBound (32*30+j.val) := by
  fin_cases j
  · convert panel_paid_960 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_961 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_962 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_963 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_964 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_965 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_966 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_967 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_968 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_969 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_970 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_971 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_972 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_973 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_974 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_975 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_976 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_977 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_978 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_979 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_980 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_981 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_982 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_983 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_984 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_985 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_986 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_987 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_988 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_989 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_990 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
  · convert panel_paid_991 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock30,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_30
