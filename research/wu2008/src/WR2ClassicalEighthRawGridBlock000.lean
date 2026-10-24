import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints000
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_000 (j : Fin 16) : upperValue ((point (16*0+j.val)+point ((16*0+j.val)+1))/2) ≤ payment (16*0+j.val) := by
  fin_cases j
  · change upperValue ((point (0)+point ((0)+1))/2) ≤ payment (0)
    have hp : payment 0 = (8218374294433:ℝ)/1000000000000 := rfl
    have hx : (point 0+point 1)/2 = (1229827:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_0
  · change upperValue ((point (1)+point ((1)+1))/2) ≤ payment (1)
    have hp : payment 1 = (8202738309495:ℝ)/1000000000000 := rfl
    have hx : (point 1+point 2)/2 = (410627:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1
  · change upperValue ((point (2)+point ((2)+1))/2) ≤ payment (2)
    have hp : payment 2 = (8187153204519:ℝ)/1000000000000 := rfl
    have hx : (point 2+point 3)/2 = (1233935:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2
  · change upperValue ((point (3)+point ((3)+1))/2) ≤ payment (3)
    have hp : payment 3 = (8171618725088:ℝ)/1000000000000 := rfl
    have hx : (point 3+point 4)/2 = (1235989:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_3
  · change upperValue ((point (4)+point ((4)+1))/2) ≤ payment (4)
    have hp : payment 4 = (8156134618473:ℝ)/1000000000000 := rfl
    have hx : (point 4+point 5)/2 = (412681:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_4
  · change upperValue ((point (5)+point ((5)+1))/2) ≤ payment (5)
    have hp : payment 5 = (8140700633618:ℝ)/1000000000000 := rfl
    have hx : (point 5+point 6)/2 = (1240097:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_5
  · change upperValue ((point (6)+point ((6)+1))/2) ≤ payment (6)
    have hp : payment 6 = (8125316521127:ℝ)/1000000000000 := rfl
    have hx : (point 6+point 7)/2 = (1242151:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_6
  · change upperValue ((point (7)+point ((7)+1))/2) ≤ payment (7)
    have hp : payment 7 = (8109982033251:ℝ)/1000000000000 := rfl
    have hx : (point 7+point 8)/2 = (414735:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_7
  · change upperValue ((point (8)+point ((8)+1))/2) ≤ payment (8)
    have hp : payment 8 = (8094696923874:ℝ)/1000000000000 := rfl
    have hx : (point 8+point 9)/2 = (1246259:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_8
  · change upperValue ((point (9)+point ((9)+1))/2) ≤ payment (9)
    have hp : payment 9 = (8079460948499:ℝ)/1000000000000 := rfl
    have hx : (point 9+point 10)/2 = (1248313:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_9
  · change upperValue ((point (10)+point ((10)+1))/2) ≤ payment (10)
    have hp : payment 10 = (8064273864233:ℝ)/1000000000000 := rfl
    have hx : (point 10+point 11)/2 = (416789:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_10
  · change upperValue ((point (11)+point ((11)+1))/2) ≤ payment (11)
    have hp : payment 11 = (8049135429779:ℝ)/1000000000000 := rfl
    have hx : (point 11+point 12)/2 = (1252421:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_11
  · change upperValue ((point (12)+point ((12)+1))/2) ≤ payment (12)
    have hp : payment 12 = (8034045405417:ℝ)/1000000000000 := rfl
    have hx : (point 12+point 13)/2 = (1254475:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_12
  · change upperValue ((point (13)+point ((13)+1))/2) ≤ payment (13)
    have hp : payment 13 = (8019003552997:ℝ)/1000000000000 := rfl
    have hx : (point 13+point 14)/2 = (418843:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_13
  · change upperValue ((point (14)+point ((14)+1))/2) ≤ payment (14)
    have hp : payment 14 = (8004009635919:ℝ)/1000000000000 := rfl
    have hx : (point 14+point 15)/2 = (1258583:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_14
  · change upperValue ((point (15)+point ((15)+1))/2) ≤ payment (15)
    have hp : payment 15 = (7989063419128:ℝ)/1000000000000 := rfl
    have hx : (point 15+point 16)/2 = (1260637:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_15
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_000
