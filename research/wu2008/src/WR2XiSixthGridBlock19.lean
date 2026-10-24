import WR2XiSixthPayments
import WR2XiSixthPanels19
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_19 (j : Fin 32) : payment (32*19+j.val) ≤ panelBound (32*19+j.val) := by
  fin_cases j
  · convert panel_paid_608 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_609 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_610 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_611 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_612 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_613 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_614 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_615 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_616 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_617 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_618 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_619 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_620 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_621 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_622 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_623 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_624 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_625 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_626 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_627 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_628 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_629 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_630 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_631 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_632 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_633 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_634 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_635 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_636 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_637 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_638 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
  · convert panel_paid_639 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock19,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_19
