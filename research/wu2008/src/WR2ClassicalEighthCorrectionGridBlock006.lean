import WR2ClassicalEighthCorrectionPayments
import WR2ClassicalEighthCorrectionPoints006
noncomputable section
namespace WuPaper.ClassicalEighthCorrection
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_006 (j : Fin 16) : step*payment (16*6+j.val) ≤ cellPayment (point (16*6+j.val)) (point ((16*6+j.val)+1)) := by
  fin_cases j
  · change step*payment (96) ≤ cellPayment (point (96)) (point ((96)+1))
    have hp : payment 96 = (166879542426:ℝ)/1000000000000 := rfl
    have hl : point 96 = (16981:ℝ)/212320 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 97 = (543719:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_96
  · change step*payment (97) ≤ cellPayment (point (97)) (point ((97)+1))
    have hp : payment 97 = (166371102620:ℝ)/1000000000000 := rfl
    have hl : point 97 = (543719:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 98 = (272023:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_97
  · change step*payment (98) ≤ cellPayment (point (98)) (point ((98)+1))
    have hp : payment 98 = (165863301867:ℝ)/1000000000000 := rfl
    have hl : point 98 = (272023:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 99 = (544373:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_98
  · change step*payment (99) ≤ cellPayment (point (99)) (point ((99)+1))
    have hp : payment 99 = (165356139046:ℝ)/1000000000000 := rfl
    have hl : point 99 = (544373:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 100 = (27235:ℝ)/339712 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_99
  · change step*payment (100) ≤ cellPayment (point (100)) (point ((100)+1))
    have hp : payment 100 = (164849613038:ℝ)/1000000000000 := rfl
    have hl : point 100 = (27235:ℝ)/339712 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 101 = (545027:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_100
  · change step*payment (101) ≤ cellPayment (point (101)) (point ((101)+1))
    have hp : payment 101 = (164343722727:ℝ)/1000000000000 := rfl
    have hl : point 101 = (545027:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 102 = (272677:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_101
  · change step*payment (102) ≤ cellPayment (point (102)) (point ((102)+1))
    have hp : payment 102 = (163838467000:ℝ)/1000000000000 := rfl
    have hl : point 102 = (272677:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 103 = (545681:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_102
  · change step*payment (103) ≤ cellPayment (point (103)) (point ((103)+1))
    have hp : payment 103 = (163333844745:ℝ)/1000000000000 := rfl
    have hl : point 103 = (545681:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 104 = (68251:ℝ)/849280 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_103
  · change step*payment (104) ≤ cellPayment (point (104)) (point ((104)+1))
    have hp : payment 104 = (162829854856:ℝ)/1000000000000 := rfl
    have hl : point 104 = (68251:ℝ)/849280 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 105 = (109267:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_104
  · change step*payment (105) ≤ cellPayment (point (105)) (point ((105)+1))
    have hp : payment 105 = (162326496227:ℝ)/1000000000000 := rfl
    have hl : point 105 = (109267:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 106 = (273331:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_105
  · change step*payment (106) ≤ cellPayment (point (106)) (point ((106)+1))
    have hp : payment 106 = (161823767755:ℝ)/1000000000000 := rfl
    have hl : point 106 = (273331:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 107 = (546989:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_106
  · change step*payment (107) ≤ cellPayment (point (107)) (point ((107)+1))
    have hp : payment 107 = (161321668341:ℝ)/1000000000000 := rfl
    have hl : point 107 = (546989:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 108 = (136829:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_107
  · change step*payment (108) ≤ cellPayment (point (108)) (point ((108)+1))
    have hp : payment 108 = (160820196887:ℝ)/1000000000000 := rfl
    have hl : point 108 = (136829:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 109 = (547643:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_108
  · change step*payment (109) ≤ cellPayment (point (109)) (point ((109)+1))
    have hp : payment 109 = (160319352298:ℝ)/1000000000000 := rfl
    have hl : point 109 = (547643:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 110 = (54797:ℝ)/679424 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_109
  · change step*payment (110) ≤ cellPayment (point (110)) (point ((110)+1))
    have hp : payment 110 = (159819133482:ℝ)/1000000000000 := rfl
    have hl : point 110 = (54797:ℝ)/679424 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 111 = (548297:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_110
  · change step*payment (111) ≤ cellPayment (point (111)) (point ((111)+1))
    have hp : payment 111 = (159319539350:ℝ)/1000000000000 := rfl
    have hl : point 111 = (548297:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 112 = (34289:ℝ)/424640 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_111
end WuPaper.ClassicalEighthCorrection
#print axioms WuPaper.ClassicalEighthCorrection.grid_block_006
