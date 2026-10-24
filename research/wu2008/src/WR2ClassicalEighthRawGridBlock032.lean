import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints032
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_032 (j : Fin 16) : upperValue ((point (16*32+j.val)+point ((16*32+j.val)+1))/2) ≤ payment (16*32+j.val) := by
  fin_cases j
  · change upperValue ((point (512)+point ((512)+1))/2) ≤ payment (512)
    have hp : payment 512 = (3802491647559:ℝ)/1000000000000 := rfl
    have hx : (point 512+point 513)/2 = (2281475:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_512
  · change upperValue ((point (513)+point ((513)+1))/2) ≤ payment (513)
    have hp : payment 513 = (3797641920835:ℝ)/1000000000000 := rfl
    have hx : (point 513+point 514)/2 = (2283529:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_513
  · change upperValue ((point (514)+point ((514)+1))/2) ≤ payment (514)
    have hp : payment 514 = (3792800017622:ℝ)/1000000000000 := rfl
    have hx : (point 514+point 515)/2 = (761861:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_514
  · change upperValue ((point (515)+point ((515)+1))/2) ≤ payment (515)
    have hp : payment 515 = (3787965916226:ℝ)/1000000000000 := rfl
    have hx : (point 515+point 516)/2 = (2287637:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_515
  · change upperValue ((point (516)+point ((516)+1))/2) ≤ payment (516)
    have hp : payment 516 = (3783139595031:ℝ)/1000000000000 := rfl
    have hx : (point 516+point 517)/2 = (2289691:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_516
  · change upperValue ((point (517)+point ((517)+1))/2) ≤ payment (517)
    have hp : payment 517 = (3778321032501:ℝ)/1000000000000 := rfl
    have hx : (point 517+point 518)/2 = (763915:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_517
  · change upperValue ((point (518)+point ((518)+1))/2) ≤ payment (518)
    have hp : payment 518 = (3773510207171:ℝ)/1000000000000 := rfl
    have hx : (point 518+point 519)/2 = (2293799:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_518
  · change upperValue ((point (519)+point ((519)+1))/2) ≤ payment (519)
    have hp : payment 519 = (3768707097658:ℝ)/1000000000000 := rfl
    have hx : (point 519+point 520)/2 = (2295853:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_519
  · change upperValue ((point (520)+point ((520)+1))/2) ≤ payment (520)
    have hp : payment 520 = (3763911682651:ℝ)/1000000000000 := rfl
    have hx : (point 520+point 521)/2 = (765969:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_520
  · change upperValue ((point (521)+point ((521)+1))/2) ≤ payment (521)
    have hp : payment 521 = (3759123940917:ℝ)/1000000000000 := rfl
    have hx : (point 521+point 522)/2 = (2299961:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_521
  · change upperValue ((point (522)+point ((522)+1))/2) ≤ payment (522)
    have hp : payment 522 = (3754343851297:ℝ)/1000000000000 := rfl
    have hx : (point 522+point 523)/2 = (2302015:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_522
  · change upperValue ((point (523)+point ((523)+1))/2) ≤ payment (523)
    have hp : payment 523 = (3749571392706:ℝ)/1000000000000 := rfl
    have hx : (point 523+point 524)/2 = (768023:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_523
  · change upperValue ((point (524)+point ((524)+1))/2) ≤ payment (524)
    have hp : payment 524 = (3744806544136:ℝ)/1000000000000 := rfl
    have hx : (point 524+point 525)/2 = (2306123:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_524
  · change upperValue ((point (525)+point ((525)+1))/2) ≤ payment (525)
    have hp : payment 525 = (3740049284651:ℝ)/1000000000000 := rfl
    have hx : (point 525+point 526)/2 = (2308177:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_525
  · change upperValue ((point (526)+point ((526)+1))/2) ≤ payment (526)
    have hp : payment 526 = (3735299593391:ℝ)/1000000000000 := rfl
    have hx : (point 526+point 527)/2 = (770077:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_526
  · change upperValue ((point (527)+point ((527)+1))/2) ≤ payment (527)
    have hp : payment 527 = (3730557449568:ℝ)/1000000000000 := rfl
    have hx : (point 527+point 528)/2 = (2312285:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_527
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_032
