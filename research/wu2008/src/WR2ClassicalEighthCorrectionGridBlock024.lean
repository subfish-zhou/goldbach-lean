import WR2ClassicalEighthCorrectionPayments
import WR2ClassicalEighthCorrectionPoints024
noncomputable section
namespace WuPaper.ClassicalEighthCorrection
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_024 (j : Fin 16) : step*payment (16*24+j.val) ≤ cellPayment (point (16*24+j.val)) (point ((16*24+j.val)+1)) := by
  fin_cases j
  · change step*payment (384) ≤ cellPayment (point (384)) (point ((384)+1))
    have hp : payment 384 = (43090573098:ℝ)/1000000000000 := rfl
    have hl : point 384 = (4981:ℝ)/53080 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 385 = (127579:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_384
  · change step*payment (385) ≤ cellPayment (point (385)) (point ((385)+1))
    have hp : payment 385 = (42728609073:ℝ)/1000000000000 := rfl
    have hl : point 385 = (127579:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 386 = (319111:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_385
  · change step*payment (386) ≤ cellPayment (point (386)) (point ((386)+1))
    have hp : payment 386 = (42367047627:ℝ)/1000000000000 := rfl
    have hl : point 386 = (319111:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 387 = (638549:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_386
  · change step*payment (387) ≤ cellPayment (point (387)) (point ((387)+1))
    have hp : payment 387 = (42005888170:ℝ)/1000000000000 := rfl
    have hl : point 387 = (638549:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 388 = (159719:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_387
  · change step*payment (388) ≤ cellPayment (point (388)) (point ((388)+1))
    have hp : payment 388 = (41645130115:ℝ)/1000000000000 := rfl
    have hl : point 388 = (159719:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 389 = (639203:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_388
  · change step*payment (389) ≤ cellPayment (point (389)) (point ((389)+1))
    have hp : payment 389 = (41284772876:ℝ)/1000000000000 := rfl
    have hl : point 389 = (639203:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 390 = (63953:ℝ)/679424 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_389
  · change step*payment (390) ≤ cellPayment (point (390)) (point ((390)+1))
    have hp : payment 390 = (40924815865:ℝ)/1000000000000 := rfl
    have hl : point 390 = (63953:ℝ)/679424 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 391 = (639857:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_390
  · change step*payment (391) ≤ cellPayment (point (391)) (point ((391)+1))
    have hp : payment 391 = (40565258500:ℝ)/1000000000000 := rfl
    have hl : point 391 = (639857:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 392 = (80023:ℝ)/849280 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_391
  · change step*payment (392) ≤ cellPayment (point (392)) (point ((392)+1))
    have hp : payment 392 = (40206100198:ℝ)/1000000000000 := rfl
    have hl : point 392 = (80023:ℝ)/849280 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 393 = (640511:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_392
  · change step*payment (393) ≤ cellPayment (point (393)) (point ((393)+1))
    have hp : payment 393 = (39847340375:ℝ)/1000000000000 := rfl
    have hl : point 393 = (640511:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 394 = (320419:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_393
  · change step*payment (394) ≤ cellPayment (point (394)) (point ((394)+1))
    have hp : payment 394 = (39488978452:ℝ)/1000000000000 := rfl
    have hl : point 394 = (320419:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 395 = (128233:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_394
  · change step*payment (395) ≤ cellPayment (point (395)) (point ((395)+1))
    have hp : payment 395 = (39131013850:ℝ)/1000000000000 := rfl
    have hl : point 395 = (128233:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 396 = (160373:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_395
  · change step*payment (396) ≤ cellPayment (point (396)) (point ((396)+1))
    have hp : payment 396 = (38773445989:ℝ)/1000000000000 := rfl
    have hl : point 396 = (160373:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 397 = (641819:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_396
  · change step*payment (397) ≤ cellPayment (point (397)) (point ((397)+1))
    have hp : payment 397 = (38416274293:ℝ)/1000000000000 := rfl
    have hl : point 397 = (641819:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 398 = (321073:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_397
  · change step*payment (398) ≤ cellPayment (point (398)) (point ((398)+1))
    have hp : payment 398 = (38059498185:ℝ)/1000000000000 := rfl
    have hl : point 398 = (321073:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 399 = (642473:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_398
  · change step*payment (399) ≤ cellPayment (point (399)) (point ((399)+1))
    have hp : payment 399 = (37703117092:ℝ)/1000000000000 := rfl
    have hl : point 399 = (642473:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 400 = (8035:ℝ)/84928 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_399
end WuPaper.ClassicalEighthCorrection
#print axioms WuPaper.ClassicalEighthCorrection.grid_block_024
