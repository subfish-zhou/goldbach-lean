import WR2XiSixthPayments
import WR2XiSixthPanels29
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_29 (j : Fin 32) : payment (32*29+j.val) ≤ panelBound (32*29+j.val) := by
  fin_cases j
  · convert panel_paid_928 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_929 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_930 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_931 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_932 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_933 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_934 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_935 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_936 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_937 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_938 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_939 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_940 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_941 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_942 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_943 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_944 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_945 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_946 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_947 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_948 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_949 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_950 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_951 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_952 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_953 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_954 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_955 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_956 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_957 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_958 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
  · convert panel_paid_959 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock29,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_29
