import WR2ClassicalEighthCorrectionPayments
import WR2ClassicalEighthCorrectionPoints029
noncomputable section
namespace WuPaper.ClassicalEighthCorrection
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_029 (j : Fin 16) : step*payment (16*29+j.val) ≤ cellPayment (point (16*29+j.val)) (point ((16*29+j.val)+1)) := by
  fin_cases j
  · change step*payment (464) ≤ cellPayment (point (464)) (point ((464)+1))
    have hp : payment 464 = (15359052852:ℝ)/1000000000000 := rfl
    have hl : point 464 = (41483:ℝ)/424640 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 465 = (132811:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_464
  · change step*payment (465) ≤ cellPayment (point (465)) (point ((465)+1))
    have hp : payment 465 = (15027528937:ℝ)/1000000000000 := rfl
    have hl : point 465 = (132811:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 466 = (332191:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_465
  · change step*payment (466) ≤ cellPayment (point (466)) (point ((466)+1))
    have hp : payment 466 = (14696364083:ℝ)/1000000000000 := rfl
    have hl : point 466 = (332191:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 467 = (664709:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_466
  · change step*payment (467) ≤ cellPayment (point (467)) (point ((467)+1))
    have hp : payment 467 = (14365557788:ℝ)/1000000000000 := rfl
    have hl : point 467 = (664709:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 468 = (166259:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_467
  · change step*payment (468) ≤ cellPayment (point (468)) (point ((468)+1))
    have hp : payment 468 = (14035109552:ℝ)/1000000000000 := rfl
    have hl : point 468 = (166259:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 469 = (665363:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_468
  · change step*payment (469) ≤ cellPayment (point (469)) (point ((469)+1))
    have hp : payment 469 = (13705018878:ℝ)/1000000000000 := rfl
    have hl : point 469 = (665363:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 470 = (66569:ℝ)/679424 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_469
  · change step*payment (470) ≤ cellPayment (point (470)) (point ((470)+1))
    have hp : payment 470 = (13375285267:ℝ)/1000000000000 := rfl
    have hl : point 470 = (66569:ℝ)/679424 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 471 = (666017:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_470
  · change step*payment (471) ≤ cellPayment (point (471)) (point ((471)+1))
    have hp : payment 471 = (13045908223:ℝ)/1000000000000 := rfl
    have hl : point 471 = (666017:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 472 = (83293:ℝ)/849280 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_471
  · change step*payment (472) ≤ cellPayment (point (472)) (point ((472)+1))
    have hp : payment 472 = (12716887250:ℝ)/1000000000000 := rfl
    have hl : point 472 = (83293:ℝ)/849280 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 473 = (666671:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_472
  · change step*payment (473) ≤ cellPayment (point (473)) (point ((473)+1))
    have hp : payment 473 = (12388221853:ℝ)/1000000000000 := rfl
    have hl : point 473 = (666671:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 474 = (333499:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_473
  · change step*payment (474) ≤ cellPayment (point (474)) (point ((474)+1))
    have hp : payment 474 = (12059911538:ℝ)/1000000000000 := rfl
    have hl : point 474 = (333499:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 475 = (133465:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_474
  · change step*payment (475) ≤ cellPayment (point (475)) (point ((475)+1))
    have hp : payment 475 = (11731955814:ℝ)/1000000000000 := rfl
    have hl : point 475 = (133465:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 476 = (166913:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_475
  · change step*payment (476) ≤ cellPayment (point (476)) (point ((476)+1))
    have hp : payment 476 = (11404354187:ℝ)/1000000000000 := rfl
    have hl : point 476 = (166913:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 477 = (667979:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_476
  · change step*payment (477) ≤ cellPayment (point (477)) (point ((477)+1))
    have hp : payment 477 = (11077106168:ℝ)/1000000000000 := rfl
    have hl : point 477 = (667979:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 478 = (334153:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_477
  · change step*payment (478) ≤ cellPayment (point (478)) (point ((478)+1))
    have hp : payment 478 = (10750211266:ℝ)/1000000000000 := rfl
    have hl : point 478 = (334153:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 479 = (668633:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_478
  · change step*payment (479) ≤ cellPayment (point (479)) (point ((479)+1))
    have hp : payment 479 = (10423668992:ℝ)/1000000000000 := rfl
    have hl : point 479 = (668633:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 480 = (4181:ℝ)/42464 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_479
end WuPaper.ClassicalEighthCorrection
#print axioms WuPaper.ClassicalEighthCorrection.grid_block_029
