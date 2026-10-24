import WR2XiSixthPayments
import WR2XiSixthPanels11
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_11 (j : Fin 32) : payment (32*11+j.val) ≤ panelBound (32*11+j.val) := by
  fin_cases j
  · convert panel_paid_352 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_353 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_354 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_355 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_356 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_357 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_358 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_359 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_360 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_361 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_362 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_363 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_364 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_365 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_366 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_367 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_368 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_369 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_370 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_371 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_372 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_373 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_374 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_375 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_376 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_377 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_378 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_379 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_380 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_381 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_382 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
  · convert panel_paid_383 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock11,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_11
