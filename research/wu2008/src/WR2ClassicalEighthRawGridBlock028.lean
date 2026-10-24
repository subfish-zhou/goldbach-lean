import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints028
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_028 (j : Fin 16) : upperValue ((point (16*28+j.val)+point ((16*28+j.val)+1))/2) ≤ payment (16*28+j.val) := by
  fin_cases j
  · change upperValue ((point (448)+point ((448)+1))/2) ≤ payment (448)
    have hp : payment 448 = (4130202833059:ℝ)/1000000000000 := rfl
    have hx : (point 448+point 449)/2 = (716673:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_448
  · change upperValue ((point (449)+point ((449)+1))/2) ≤ payment (449)
    have hp : payment 449 = (4124803456034:ℝ)/1000000000000 := rfl
    have hx : (point 449+point 450)/2 = (2152073:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_449
  · change upperValue ((point (450)+point ((450)+1))/2) ≤ payment (450)
    have hp : payment 450 = (4119413469107:ℝ)/1000000000000 := rfl
    have hx : (point 450+point 451)/2 = (2154127:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_450
  · change upperValue ((point (451)+point ((451)+1))/2) ≤ payment (451)
    have hp : payment 451 = (4114032844818:ℝ)/1000000000000 := rfl
    have hx : (point 451+point 452)/2 = (718727:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_451
  · change upperValue ((point (452)+point ((452)+1))/2) ≤ payment (452)
    have hp : payment 452 = (4108661555816:ℝ)/1000000000000 := rfl
    have hx : (point 452+point 453)/2 = (2158235:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_452
  · change upperValue ((point (453)+point ((453)+1))/2) ≤ payment (453)
    have hp : payment 453 = (4103299574848:ℝ)/1000000000000 := rfl
    have hx : (point 453+point 454)/2 = (2160289:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_453
  · change upperValue ((point (454)+point ((454)+1))/2) ≤ payment (454)
    have hp : payment 454 = (4097946874769:ℝ)/1000000000000 := rfl
    have hx : (point 454+point 455)/2 = (720781:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_454
  · change upperValue ((point (455)+point ((455)+1))/2) ≤ payment (455)
    have hp : payment 455 = (4092603428533:ℝ)/1000000000000 := rfl
    have hx : (point 455+point 456)/2 = (2164397:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_455
  · change upperValue ((point (456)+point ((456)+1))/2) ≤ payment (456)
    have hp : payment 456 = (4087269209198:ℝ)/1000000000000 := rfl
    have hx : (point 456+point 457)/2 = (2166451:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_456
  · change upperValue ((point (457)+point ((457)+1))/2) ≤ payment (457)
    have hp : payment 457 = (4081944189923:ℝ)/1000000000000 := rfl
    have hx : (point 457+point 458)/2 = (722835:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_457
  · change upperValue ((point (458)+point ((458)+1))/2) ≤ payment (458)
    have hp : payment 458 = (4076628343967:ℝ)/1000000000000 := rfl
    have hx : (point 458+point 459)/2 = (2170559:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_458
  · change upperValue ((point (459)+point ((459)+1))/2) ≤ payment (459)
    have hp : payment 459 = (4071321644692:ℝ)/1000000000000 := rfl
    have hx : (point 459+point 460)/2 = (2172613:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_459
  · change upperValue ((point (460)+point ((460)+1))/2) ≤ payment (460)
    have hp : payment 460 = (4066024065557:ℝ)/1000000000000 := rfl
    have hx : (point 460+point 461)/2 = (724889:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_460
  · change upperValue ((point (461)+point ((461)+1))/2) ≤ payment (461)
    have hp : payment 461 = (4060735580124:ℝ)/1000000000000 := rfl
    have hx : (point 461+point 462)/2 = (2176721:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_461
  · change upperValue ((point (462)+point ((462)+1))/2) ≤ payment (462)
    have hp : payment 462 = (4055456162052:ℝ)/1000000000000 := rfl
    have hx : (point 462+point 463)/2 = (2178775:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_462
  · change upperValue ((point (463)+point ((463)+1))/2) ≤ payment (463)
    have hp : payment 463 = (4050185785098:ℝ)/1000000000000 := rfl
    have hx : (point 463+point 464)/2 = (726943:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_463
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_028
