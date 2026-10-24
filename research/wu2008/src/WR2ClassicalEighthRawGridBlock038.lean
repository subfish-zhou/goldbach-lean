import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints038
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_038 (j : Fin 16) : upperValue ((point (16*38+j.val)+point ((16*38+j.val)+1))/2) ≤ payment (16*38+j.val) := by
  fin_cases j
  · change upperValue ((point (608)+point ((608)+1))/2) ≤ payment (608)
    have hp : payment 608 = (3369730851493:ℝ)/1000000000000 := rfl
    have hx : (point 608+point 609)/2 = (2478659:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_608
  · change upperValue ((point (609)+point ((609)+1))/2) ≤ payment (609)
    have hp : payment 609 = (3365543260711:ℝ)/1000000000000 := rfl
    have hx : (point 609+point 610)/2 = (2480713:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_609
  · change upperValue ((point (610)+point ((610)+1))/2) ≤ payment (610)
    have hp : payment 610 = (3361361719454:ℝ)/1000000000000 := rfl
    have hx : (point 610+point 611)/2 = (827589:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_610
  · change upperValue ((point (611)+point ((611)+1))/2) ≤ payment (611)
    have hp : payment 611 = (3357186212102:ℝ)/1000000000000 := rfl
    have hx : (point 611+point 612)/2 = (2484821:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_611
  · change upperValue ((point (612)+point ((612)+1))/2) ≤ payment (612)
    have hp : payment 612 = (3353016723084:ℝ)/1000000000000 := rfl
    have hx : (point 612+point 613)/2 = (2486875:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_612
  · change upperValue ((point (613)+point ((613)+1))/2) ≤ payment (613)
    have hp : payment 613 = (3348853236881:ℝ)/1000000000000 := rfl
    have hx : (point 613+point 614)/2 = (829643:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_613
  · change upperValue ((point (614)+point ((614)+1))/2) ≤ payment (614)
    have hp : payment 614 = (3344695738026:ℝ)/1000000000000 := rfl
    have hx : (point 614+point 615)/2 = (2490983:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_614
  · change upperValue ((point (615)+point ((615)+1))/2) ≤ payment (615)
    have hp : payment 615 = (3340544211100:ℝ)/1000000000000 := rfl
    have hx : (point 615+point 616)/2 = (2493037:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_615
  · change upperValue ((point (616)+point ((616)+1))/2) ≤ payment (616)
    have hp : payment 616 = (3336398640736:ℝ)/1000000000000 := rfl
    have hx : (point 616+point 617)/2 = (831697:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_616
  · change upperValue ((point (617)+point ((617)+1))/2) ≤ payment (617)
    have hp : payment 617 = (3332259011616:ℝ)/1000000000000 := rfl
    have hx : (point 617+point 618)/2 = (2497145:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_617
  · change upperValue ((point (618)+point ((618)+1))/2) ≤ payment (618)
    have hp : payment 618 = (3328125308472:ℝ)/1000000000000 := rfl
    have hx : (point 618+point 619)/2 = (2499199:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_618
  · change upperValue ((point (619)+point ((619)+1))/2) ≤ payment (619)
    have hp : payment 619 = (3323997516085:ℝ)/1000000000000 := rfl
    have hx : (point 619+point 620)/2 = (833751:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_619
  · change upperValue ((point (620)+point ((620)+1))/2) ≤ payment (620)
    have hp : payment 620 = (3319875619289:ℝ)/1000000000000 := rfl
    have hx : (point 620+point 621)/2 = (2503307:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_620
  · change upperValue ((point (621)+point ((621)+1))/2) ≤ payment (621)
    have hp : payment 621 = (3315759602961:ℝ)/1000000000000 := rfl
    have hx : (point 621+point 622)/2 = (2505361:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_621
  · change upperValue ((point (622)+point ((622)+1))/2) ≤ payment (622)
    have hp : payment 622 = (3311649452033:ℝ)/1000000000000 := rfl
    have hx : (point 622+point 623)/2 = (835805:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_622
  · change upperValue ((point (623)+point ((623)+1))/2) ≤ payment (623)
    have hp : payment 623 = (3307545151483:ℝ)/1000000000000 := rfl
    have hx : (point 623+point 624)/2 = (2509469:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_623
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_038
