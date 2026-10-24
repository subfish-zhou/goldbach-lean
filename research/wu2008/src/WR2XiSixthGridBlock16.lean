import WR2XiSixthPayments
import WR2XiSixthPanels16
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_16 (j : Fin 32) : payment (32*16+j.val) ≤ panelBound (32*16+j.val) := by
  fin_cases j
  · convert panel_paid_512 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_513 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_514 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_515 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_516 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_517 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_518 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_519 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_520 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_521 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_522 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_523 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_524 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_525 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_526 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_527 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_528 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_529 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_530 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_531 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_532 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_533 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_534 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_535 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_536 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_537 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_538 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_539 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_540 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_541 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_542 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
  · convert panel_paid_543 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock16,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_16
