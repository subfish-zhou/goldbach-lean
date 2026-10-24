import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints039
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_039 (j : Fin 16) : upperValue ((point (16*39+j.val)+point ((16*39+j.val)+1))/2) ≤ payment (16*39+j.val) := by
  fin_cases j
  · change upperValue ((point (624)+point ((624)+1))/2) ≤ payment (624)
    have hp : payment 624 = (3303446686336:ℝ)/1000000000000 := rfl
    have hx : (point 624+point 625)/2 = (2511523:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_624
  · change upperValue ((point (625)+point ((625)+1))/2) ≤ payment (625)
    have hp : payment 625 = (3299354041669:ℝ)/1000000000000 := rfl
    have hx : (point 625+point 626)/2 = (837859:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_625
  · change upperValue ((point (626)+point ((626)+1))/2) ≤ payment (626)
    have hp : payment 626 = (3295267202604:ℝ)/1000000000000 := rfl
    have hx : (point 626+point 627)/2 = (2515631:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_626
  · change upperValue ((point (627)+point ((627)+1))/2) ≤ payment (627)
    have hp : payment 627 = (3291186154314:ℝ)/1000000000000 := rfl
    have hx : (point 627+point 628)/2 = (2517685:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_627
  · change upperValue ((point (628)+point ((628)+1))/2) ≤ payment (628)
    have hp : payment 628 = (3287110882018:ℝ)/1000000000000 := rfl
    have hx : (point 628+point 629)/2 = (839913:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_628
  · change upperValue ((point (629)+point ((629)+1))/2) ≤ payment (629)
    have hp : payment 629 = (3283041370982:ℝ)/1000000000000 := rfl
    have hx : (point 629+point 630)/2 = (2521793:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_629
  · change upperValue ((point (630)+point ((630)+1))/2) ≤ payment (630)
    have hp : payment 630 = (3278977606521:ℝ)/1000000000000 := rfl
    have hx : (point 630+point 631)/2 = (2523847:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_630
  · change upperValue ((point (631)+point ((631)+1))/2) ≤ payment (631)
    have hp : payment 631 = (3274919573996:ℝ)/1000000000000 := rfl
    have hx : (point 631+point 632)/2 = (841967:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_631
  · change upperValue ((point (632)+point ((632)+1))/2) ≤ payment (632)
    have hp : payment 632 = (3270867258816:ℝ)/1000000000000 := rfl
    have hx : (point 632+point 633)/2 = (2527955:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_632
  · change upperValue ((point (633)+point ((633)+1))/2) ≤ payment (633)
    have hp : payment 633 = (3266820646437:ℝ)/1000000000000 := rfl
    have hx : (point 633+point 634)/2 = (2530009:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_633
  · change upperValue ((point (634)+point ((634)+1))/2) ≤ payment (634)
    have hp : payment 634 = (3262779722360:ℝ)/1000000000000 := rfl
    have hx : (point 634+point 635)/2 = (844021:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_634
  · change upperValue ((point (635)+point ((635)+1))/2) ≤ payment (635)
    have hp : payment 635 = (3258744472134:ℝ)/1000000000000 := rfl
    have hx : (point 635+point 636)/2 = (2534117:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_635
  · change upperValue ((point (636)+point ((636)+1))/2) ≤ payment (636)
    have hp : payment 636 = (3254714881354:ℝ)/1000000000000 := rfl
    have hx : (point 636+point 637)/2 = (2536171:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_636
  · change upperValue ((point (637)+point ((637)+1))/2) ≤ payment (637)
    have hp : payment 637 = (3250690935661:ℝ)/1000000000000 := rfl
    have hx : (point 637+point 638)/2 = (846075:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_637
  · change upperValue ((point (638)+point ((638)+1))/2) ≤ payment (638)
    have hp : payment 638 = (3246672620742:ℝ)/1000000000000 := rfl
    have hx : (point 638+point 639)/2 = (2540279:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_638
  · change upperValue ((point (639)+point ((639)+1))/2) ≤ payment (639)
    have hp : payment 639 = (3242659922329:ℝ)/1000000000000 := rfl
    have hx : (point 639+point 640)/2 = (2542333:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_639
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_039
