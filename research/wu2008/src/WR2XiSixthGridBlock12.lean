import WR2XiSixthPayments
import WR2XiSixthPanels12
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_12 (j : Fin 32) : payment (32*12+j.val) ≤ panelBound (32*12+j.val) := by
  fin_cases j
  · convert panel_paid_384 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_385 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_386 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_387 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_388 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_389 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_390 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_391 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_392 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_393 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_394 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_395 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_396 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_397 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_398 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_399 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_400 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_401 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_402 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_403 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_404 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_405 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_406 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_407 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_408 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_409 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_410 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_411 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_412 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_413 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_414 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
  · convert panel_paid_415 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock12,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_12
