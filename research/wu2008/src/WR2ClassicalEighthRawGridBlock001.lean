import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints001
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_001 (j : Fin 16) : upperValue ((point (16*1+j.val)+point ((16*1+j.val)+1))/2) ≤ payment (16*1+j.val) := by
  fin_cases j
  · change upperValue ((point (16)+point ((16)+1))/2) ≤ payment (16)
    have hp : payment 16 = (7974164669095:ℝ)/1000000000000 := rfl
    have hx : (point 16+point 17)/2 = (420897:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_16
  · change upperValue ((point (17)+point ((17)+1))/2) ≤ payment (17)
    have hp : payment 17 = (7959313153811:ℝ)/1000000000000 := rfl
    have hx : (point 17+point 18)/2 = (1264745:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_17
  · change upperValue ((point (18)+point ((18)+1))/2) ≤ payment (18)
    have hp : payment 18 = (7944508642767:ℝ)/1000000000000 := rfl
    have hx : (point 18+point 19)/2 = (1266799:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_18
  · change upperValue ((point (19)+point ((19)+1))/2) ≤ payment (19)
    have hp : payment 19 = (7929750906950:ℝ)/1000000000000 := rfl
    have hx : (point 19+point 20)/2 = (422951:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_19
  · change upperValue ((point (20)+point ((20)+1))/2) ≤ payment (20)
    have hp : payment 20 = (7915039718823:ℝ)/1000000000000 := rfl
    have hx : (point 20+point 21)/2 = (1270907:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_20
  · change upperValue ((point (21)+point ((21)+1))/2) ≤ payment (21)
    have hp : payment 21 = (7900374852320:ℝ)/1000000000000 := rfl
    have hx : (point 21+point 22)/2 = (1272961:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_21
  · change upperValue ((point (22)+point ((22)+1))/2) ≤ payment (22)
    have hp : payment 22 = (7885756082830:ℝ)/1000000000000 := rfl
    have hx : (point 22+point 23)/2 = (425005:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_22
  · change upperValue ((point (23)+point ((23)+1))/2) ≤ payment (23)
    have hp : payment 23 = (7871183187186:ℝ)/1000000000000 := rfl
    have hx : (point 23+point 24)/2 = (1277069:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_23
  · change upperValue ((point (24)+point ((24)+1))/2) ≤ payment (24)
    have hp : payment 24 = (7856655943655:ℝ)/1000000000000 := rfl
    have hx : (point 24+point 25)/2 = (1279123:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_24
  · change upperValue ((point (25)+point ((25)+1))/2) ≤ payment (25)
    have hp : payment 25 = (7842174131925:ℝ)/1000000000000 := rfl
    have hx : (point 25+point 26)/2 = (427059:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_25
  · change upperValue ((point (26)+point ((26)+1))/2) ≤ payment (26)
    have hp : payment 26 = (7827737533093:ℝ)/1000000000000 := rfl
    have hx : (point 26+point 27)/2 = (1283231:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_26
  · change upperValue ((point (27)+point ((27)+1))/2) ≤ payment (27)
    have hp : payment 27 = (7813345929656:ℝ)/1000000000000 := rfl
    have hx : (point 27+point 28)/2 = (1285285:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_27
  · change upperValue ((point (28)+point ((28)+1))/2) ≤ payment (28)
    have hp : payment 28 = (7798999105497:ℝ)/1000000000000 := rfl
    have hx : (point 28+point 29)/2 = (429113:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_28
  · change upperValue ((point (29)+point ((29)+1))/2) ≤ payment (29)
    have hp : payment 29 = (7784696845878:ℝ)/1000000000000 := rfl
    have hx : (point 29+point 30)/2 = (1289393:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_29
  · change upperValue ((point (30)+point ((30)+1))/2) ≤ payment (30)
    have hp : payment 30 = (7770438937425:ℝ)/1000000000000 := rfl
    have hx : (point 30+point 31)/2 = (1291447:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_30
  · change upperValue ((point (31)+point ((31)+1))/2) ≤ payment (31)
    have hp : payment 31 = (7756225168118:ℝ)/1000000000000 := rfl
    have hx : (point 31+point 32)/2 = (431167:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_31
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_001
