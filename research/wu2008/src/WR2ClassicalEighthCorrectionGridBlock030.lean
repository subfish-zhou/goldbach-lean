import WR2ClassicalEighthCorrectionPayments
import WR2ClassicalEighthCorrectionPoints030
noncomputable section
namespace WuPaper.ClassicalEighthCorrection
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_030 (j : Fin 16) : step*payment (16*30+j.val) ≤ cellPayment (point (16*30+j.val)) (point ((16*30+j.val)+1)) := by
  fin_cases j
  · change step*payment (480) ≤ cellPayment (point (480)) (point ((480)+1))
    have hp : payment 480 = (10097478859:ℝ)/1000000000000 := rfl
    have hl : point 480 = (4181:ℝ)/42464 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 481 = (669287:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_480
  · change step*payment (481) ≤ cellPayment (point (481)) (point ((481)+1))
    have hp : payment 481 = (9771640380:ℝ)/1000000000000 := rfl
    have hl : point 481 = (669287:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 482 = (334807:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_481
  · change step*payment (482) ≤ cellPayment (point (482)) (point ((482)+1))
    have hp : payment 482 = (9446153069:ℝ)/1000000000000 := rfl
    have hl : point 482 = (334807:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 483 = (669941:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_482
  · change step*payment (483) ≤ cellPayment (point (483)) (point ((483)+1))
    have hp : payment 483 = (9121016441:ℝ)/1000000000000 := rfl
    have hl : point 483 = (669941:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 484 = (167567:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_483
  · change step*payment (484) ≤ cellPayment (point (484)) (point ((484)+1))
    have hp : payment 484 = (8796230011:ℝ)/1000000000000 := rfl
    have hl : point 484 = (167567:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 485 = (134119:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_484
  · change step*payment (485) ≤ cellPayment (point (485)) (point ((485)+1))
    have hp : payment 485 = (8471793298:ℝ)/1000000000000 := rfl
    have hl : point 485 = (134119:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 486 = (335461:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_485
  · change step*payment (486) ≤ cellPayment (point (486)) (point ((486)+1))
    have hp : payment 486 = (8147705817:ℝ)/1000000000000 := rfl
    have hl : point 486 = (335461:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 487 = (671249:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_486
  · change step*payment (487) ≤ cellPayment (point (487)) (point ((487)+1))
    have hp : payment 487 = (7823967090:ℝ)/1000000000000 := rfl
    have hl : point 487 = (671249:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 488 = (83947:ℝ)/849280 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_487
  · change step*payment (488) ≤ cellPayment (point (488)) (point ((488)+1))
    have hp : payment 488 = (7500576635:ℝ)/1000000000000 := rfl
    have hl : point 488 = (83947:ℝ)/849280 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 489 = (671903:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_488
  · change step*payment (489) ≤ cellPayment (point (489)) (point ((489)+1))
    have hp : payment 489 = (7177533972:ℝ)/1000000000000 := rfl
    have hl : point 489 = (671903:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 490 = (67223:ℝ)/679424 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_489
  · change step*payment (490) ≤ cellPayment (point (490)) (point ((490)+1))
    have hp : payment 490 = (6854838625:ℝ)/1000000000000 := rfl
    have hl : point 490 = (67223:ℝ)/679424 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 491 = (672557:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_490
  · change step*payment (491) ≤ cellPayment (point (491)) (point ((491)+1))
    have hp : payment 491 = (6532490115:ℝ)/1000000000000 := rfl
    have hl : point 491 = (672557:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 492 = (168221:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_491
  · change step*payment (492) ≤ cellPayment (point (492)) (point ((492)+1))
    have hp : payment 492 = (6210487965:ℝ)/1000000000000 := rfl
    have hl : point 492 = (168221:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 493 = (673211:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_492
  · change step*payment (493) ≤ cellPayment (point (493)) (point ((493)+1))
    have hp : payment 493 = (5888831701:ℝ)/1000000000000 := rfl
    have hl : point 493 = (673211:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 494 = (336769:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_493
  · change step*payment (494) ≤ cellPayment (point (494)) (point ((494)+1))
    have hp : payment 494 = (5567520849:ℝ)/1000000000000 := rfl
    have hl : point 494 = (336769:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 495 = (134773:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_494
  · change step*payment (495) ≤ cellPayment (point (495)) (point ((495)+1))
    have hp : payment 495 = (5246554933:ℝ)/1000000000000 := rfl
    have hl : point 495 = (134773:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 496 = (42137:ℝ)/424640 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_495
end WuPaper.ClassicalEighthCorrection
#print axioms WuPaper.ClassicalEighthCorrection.grid_block_030
