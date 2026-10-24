import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints045
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_045 (j : Fin 16) : upperValue ((point (16*45+j.val)+point ((16*45+j.val)+1))/2) ≤ payment (16*45+j.val) := by
  fin_cases j
  · change upperValue ((point (720)+point ((720)+1))/2) ≤ payment (720)
    have hp : payment 720 = (2935055369216:ℝ)/1000000000000 := rfl
    have hx : (point 720+point 721)/2 = (2708707:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_720
  · change upperValue ((point (721)+point ((721)+1))/2) ≤ payment (721)
    have hp : payment 721 = (2931458680856:ℝ)/1000000000000 := rfl
    have hx : (point 721+point 722)/2 = (903587:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_721
  · change upperValue ((point (722)+point ((722)+1))/2) ≤ payment (722)
    have hp : payment 722 = (2927866567552:ℝ)/1000000000000 := rfl
    have hx : (point 722+point 723)/2 = (2712815:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_722
  · change upperValue ((point (723)+point ((723)+1))/2) ≤ payment (723)
    have hp : payment 723 = (2924279018298:ℝ)/1000000000000 := rfl
    have hx : (point 723+point 724)/2 = (2714869:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_723
  · change upperValue ((point (724)+point ((724)+1))/2) ≤ payment (724)
    have hp : payment 724 = (2920696022115:ℝ)/1000000000000 := rfl
    have hx : (point 724+point 725)/2 = (905641:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_724
  · change upperValue ((point (725)+point ((725)+1))/2) ≤ payment (725)
    have hp : payment 725 = (2917117568061:ℝ)/1000000000000 := rfl
    have hx : (point 725+point 726)/2 = (2718977:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_725
  · change upperValue ((point (726)+point ((726)+1))/2) ≤ payment (726)
    have hp : payment 726 = (2913543645225:ℝ)/1000000000000 := rfl
    have hx : (point 726+point 727)/2 = (2721031:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_726
  · change upperValue ((point (727)+point ((727)+1))/2) ≤ payment (727)
    have hp : payment 727 = (2909974242728:ℝ)/1000000000000 := rfl
    have hx : (point 727+point 728)/2 = (907695:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_727
  · change upperValue ((point (728)+point ((728)+1))/2) ≤ payment (728)
    have hp : payment 728 = (2906409349724:ℝ)/1000000000000 := rfl
    have hx : (point 728+point 729)/2 = (2725139:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_728
  · change upperValue ((point (729)+point ((729)+1))/2) ≤ payment (729)
    have hp : payment 729 = (2902848955398:ℝ)/1000000000000 := rfl
    have hx : (point 729+point 730)/2 = (2727193:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_729
  · change upperValue ((point (730)+point ((730)+1))/2) ≤ payment (730)
    have hp : payment 730 = (2899293048969:ℝ)/1000000000000 := rfl
    have hx : (point 730+point 731)/2 = (909749:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_730
  · change upperValue ((point (731)+point ((731)+1))/2) ≤ payment (731)
    have hp : payment 731 = (2895741619686:ℝ)/1000000000000 := rfl
    have hx : (point 731+point 732)/2 = (2731301:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_731
  · change upperValue ((point (732)+point ((732)+1))/2) ≤ payment (732)
    have hp : payment 732 = (2892194656830:ℝ)/1000000000000 := rfl
    have hx : (point 732+point 733)/2 = (2733355:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_732
  · change upperValue ((point (733)+point ((733)+1))/2) ≤ payment (733)
    have hp : payment 733 = (2888652149714:ℝ)/1000000000000 := rfl
    have hx : (point 733+point 734)/2 = (911803:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_733
  · change upperValue ((point (734)+point ((734)+1))/2) ≤ payment (734)
    have hp : payment 734 = (2885114087684:ℝ)/1000000000000 := rfl
    have hx : (point 734+point 735)/2 = (2737463:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_734
  · change upperValue ((point (735)+point ((735)+1))/2) ≤ payment (735)
    have hp : payment 735 = (2881580460114:ℝ)/1000000000000 := rfl
    have hx : (point 735+point 736)/2 = (2739517:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_735
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_045
