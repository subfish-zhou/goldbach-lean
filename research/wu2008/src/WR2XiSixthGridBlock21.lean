import WR2XiSixthPayments
import WR2XiSixthPanels21
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_21 (j : Fin 32) : payment (32*21+j.val) ≤ panelBound (32*21+j.val) := by
  fin_cases j
  · convert panel_paid_672 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_673 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_674 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_675 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_676 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_677 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_678 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_679 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_680 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_681 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_682 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_683 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_684 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_685 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_686 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_687 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_688 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_689 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_690 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_691 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_692 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_693 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_694 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_695 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_696 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_697 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_698 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_699 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_700 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_701 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_702 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
  · convert panel_paid_703 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock21,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_21
