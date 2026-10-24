import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints034
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_034 (j : Fin 16) : upperValue ((point (16*34+j.val)+point ((16*34+j.val)+1))/2) ≤ payment (16*34+j.val) := by
  fin_cases j
  · change upperValue ((point (544)+point ((544)+1))/2) ≤ payment (544)
    have hp : payment 544 = (3651075969408:ℝ)/1000000000000 := rfl
    have hx : (point 544+point 545)/2 = (782401:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_544
  · change upperValue ((point (545)+point ((545)+1))/2) ≤ payment (545)
    have hp : payment 545 = (3646466206774:ℝ)/1000000000000 := rfl
    have hx : (point 545+point 546)/2 = (2349257:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_545
  · change upperValue ((point (546)+point ((546)+1))/2) ≤ payment (546)
    have hp : payment 546 = (3641863610172:ℝ)/1000000000000 := rfl
    have hx : (point 546+point 547)/2 = (2351311:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_546
  · change upperValue ((point (547)+point ((547)+1))/2) ≤ payment (547)
    have hp : payment 547 = (3637268160223:ℝ)/1000000000000 := rfl
    have hx : (point 547+point 548)/2 = (784455:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_547
  · change upperValue ((point (548)+point ((548)+1))/2) ≤ payment (548)
    have hp : payment 548 = (3632679837611:ℝ)/1000000000000 := rfl
    have hx : (point 548+point 549)/2 = (2355419:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_548
  · change upperValue ((point (549)+point ((549)+1))/2) ≤ payment (549)
    have hp : payment 549 = (3628098623087:ℝ)/1000000000000 := rfl
    have hx : (point 549+point 550)/2 = (2357473:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_549
  · change upperValue ((point (550)+point ((550)+1))/2) ≤ payment (550)
    have hp : payment 550 = (3623524497471:ℝ)/1000000000000 := rfl
    have hx : (point 550+point 551)/2 = (786509:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_550
  · change upperValue ((point (551)+point ((551)+1))/2) ≤ payment (551)
    have hp : payment 551 = (3618957441646:ℝ)/1000000000000 := rfl
    have hx : (point 551+point 552)/2 = (2361581:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_551
  · change upperValue ((point (552)+point ((552)+1))/2) ≤ payment (552)
    have hp : payment 552 = (3614397436564:ℝ)/1000000000000 := rfl
    have hx : (point 552+point 553)/2 = (2363635:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_552
  · change upperValue ((point (553)+point ((553)+1))/2) ≤ payment (553)
    have hp : payment 553 = (3609844463240:ℝ)/1000000000000 := rfl
    have hx : (point 553+point 554)/2 = (788563:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_553
  · change upperValue ((point (554)+point ((554)+1))/2) ≤ payment (554)
    have hp : payment 554 = (3605298502756:ℝ)/1000000000000 := rfl
    have hx : (point 554+point 555)/2 = (2367743:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_554
  · change upperValue ((point (555)+point ((555)+1))/2) ≤ payment (555)
    have hp : payment 555 = (3600759536258:ℝ)/1000000000000 := rfl
    have hx : (point 555+point 556)/2 = (2369797:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_555
  · change upperValue ((point (556)+point ((556)+1))/2) ≤ payment (556)
    have hp : payment 556 = (3596227544958:ℝ)/1000000000000 := rfl
    have hx : (point 556+point 557)/2 = (790617:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_556
  · change upperValue ((point (557)+point ((557)+1))/2) ≤ payment (557)
    have hp : payment 557 = (3591702510132:ℝ)/1000000000000 := rfl
    have hx : (point 557+point 558)/2 = (2373905:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_557
  · change upperValue ((point (558)+point ((558)+1))/2) ≤ payment (558)
    have hp : payment 558 = (3587184413119:ℝ)/1000000000000 := rfl
    have hx : (point 558+point 559)/2 = (2375959:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_558
  · change upperValue ((point (559)+point ((559)+1))/2) ≤ payment (559)
    have hp : payment 559 = (3582673235324:ℝ)/1000000000000 := rfl
    have hx : (point 559+point 560)/2 = (792671:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_559
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_034
