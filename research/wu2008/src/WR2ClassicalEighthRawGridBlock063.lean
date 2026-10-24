import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints063
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_063 (j : Fin 16) : upperValue ((point (16*63+j.val)+point ((16*63+j.val)+1))/2) ≤ payment (16*63+j.val) := by
  fin_cases j
  · change upperValue ((point (1008)+point ((1008)+1))/2) ≤ payment (1008)
    have hp : payment 1008 = (2052470977460:ℝ)/1000000000000 := rfl
    have hx : (point 1008+point 1009)/2 = (3300259:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1008
  · change upperValue ((point (1009)+point ((1009)+1))/2) ≤ payment (1009)
    have hp : payment 1009 = (2049838211097:ℝ)/1000000000000 := rfl
    have hx : (point 1009+point 1010)/2 = (1100771:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1009
  · change upperValue ((point (1010)+point ((1010)+1))/2) ≤ payment (1010)
    have hp : payment 1010 = (2047207833755:ℝ)/1000000000000 := rfl
    have hx : (point 1010+point 1011)/2 = (3304367:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1010
  · change upperValue ((point (1011)+point ((1011)+1))/2) ≤ payment (1011)
    have hp : payment 1011 = (2044579840317:ℝ)/1000000000000 := rfl
    have hx : (point 1011+point 1012)/2 = (3306421:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1011
  · change upperValue ((point (1012)+point ((1012)+1))/2) ≤ payment (1012)
    have hp : payment 1012 = (2041954225675:ℝ)/1000000000000 := rfl
    have hx : (point 1012+point 1013)/2 = (1102825:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1012
  · change upperValue ((point (1013)+point ((1013)+1))/2) ≤ payment (1013)
    have hp : payment 1013 = (2039330984737:ℝ)/1000000000000 := rfl
    have hx : (point 1013+point 1014)/2 = (3310529:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1013
  · change upperValue ((point (1014)+point ((1014)+1))/2) ≤ payment (1014)
    have hp : payment 1014 = (2036710112418:ℝ)/1000000000000 := rfl
    have hx : (point 1014+point 1015)/2 = (3312583:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1014
  · change upperValue ((point (1015)+point ((1015)+1))/2) ≤ payment (1015)
    have hp : payment 1015 = (2034091603650:ℝ)/1000000000000 := rfl
    have hx : (point 1015+point 1016)/2 = (1104879:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1015
  · change upperValue ((point (1016)+point ((1016)+1))/2) ≤ payment (1016)
    have hp : payment 1016 = (2031475453373:ℝ)/1000000000000 := rfl
    have hx : (point 1016+point 1017)/2 = (3316691:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1016
  · change upperValue ((point (1017)+point ((1017)+1))/2) ≤ payment (1017)
    have hp : payment 1017 = (2028861656540:ℝ)/1000000000000 := rfl
    have hx : (point 1017+point 1018)/2 = (3318745:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1017
  · change upperValue ((point (1018)+point ((1018)+1))/2) ≤ payment (1018)
    have hp : payment 1018 = (2026250208119:ℝ)/1000000000000 := rfl
    have hx : (point 1018+point 1019)/2 = (1106933:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1018
  · change upperValue ((point (1019)+point ((1019)+1))/2) ≤ payment (1019)
    have hp : payment 1019 = (2023641103084:ℝ)/1000000000000 := rfl
    have hx : (point 1019+point 1020)/2 = (3322853:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1019
  · change upperValue ((point (1020)+point ((1020)+1))/2) ≤ payment (1020)
    have hp : payment 1020 = (2021034336427:ℝ)/1000000000000 := rfl
    have hx : (point 1020+point 1021)/2 = (3324907:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1020
  · change upperValue ((point (1021)+point ((1021)+1))/2) ≤ payment (1021)
    have hp : payment 1021 = (2018429903146:ℝ)/1000000000000 := rfl
    have hx : (point 1021+point 1022)/2 = (1108987:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1021
  · change upperValue ((point (1022)+point ((1022)+1))/2) ≤ payment (1022)
    have hp : payment 1022 = (2015827798255:ℝ)/1000000000000 := rfl
    have hx : (point 1022+point 1023)/2 = (3329015:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1022
  · change upperValue ((point (1023)+point ((1023)+1))/2) ≤ payment (1023)
    have hp : payment 1023 = (2013228016778:ℝ)/1000000000000 := rfl
    have hx : (point 1023+point 1024)/2 = (3331069:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1023
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_063
