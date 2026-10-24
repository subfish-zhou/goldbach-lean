import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints048
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_048 (j : Fin 16) : upperValue ((point (16*48+j.val)+point ((16*48+j.val)+1))/2) ≤ payment (16*48+j.val) := by
  fin_cases j
  · change upperValue ((point (768)+point ((768)+1))/2) ≤ payment (768)
    have hp : payment 768 = (2767390748192:ℝ)/1000000000000 := rfl
    have hx : (point 768+point 769)/2 = (2807299:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_768
  · change upperValue ((point (769)+point ((769)+1))/2) ≤ payment (769)
    have hp : payment 769 = (2764001787639:ℝ)/1000000000000 := rfl
    have hx : (point 769+point 770)/2 = (936451:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_769
  · change upperValue ((point (770)+point ((770)+1))/2) ≤ payment (770)
    have hp : payment 770 = (2760616908605:ℝ)/1000000000000 := rfl
    have hx : (point 770+point 771)/2 = (2811407:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_770
  · change upperValue ((point (771)+point ((771)+1))/2) ≤ payment (771)
    have hp : payment 771 = (2757236101523:ℝ)/1000000000000 := rfl
    have hx : (point 771+point 772)/2 = (2813461:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_771
  · change upperValue ((point (772)+point ((772)+1))/2) ≤ payment (772)
    have hp : payment 772 = (2753859356851:ℝ)/1000000000000 := rfl
    have hx : (point 772+point 773)/2 = (938505:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_772
  · change upperValue ((point (773)+point ((773)+1))/2) ≤ payment (773)
    have hp : payment 773 = (2750486665075:ℝ)/1000000000000 := rfl
    have hx : (point 773+point 774)/2 = (2817569:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_773
  · change upperValue ((point (774)+point ((774)+1))/2) ≤ payment (774)
    have hp : payment 774 = (2747118016710:ℝ)/1000000000000 := rfl
    have hx : (point 774+point 775)/2 = (2819623:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_774
  · change upperValue ((point (775)+point ((775)+1))/2) ≤ payment (775)
    have hp : payment 775 = (2743753402295:ℝ)/1000000000000 := rfl
    have hx : (point 775+point 776)/2 = (940559:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_775
  · change upperValue ((point (776)+point ((776)+1))/2) ≤ payment (776)
    have hp : payment 776 = (2740392812398:ℝ)/1000000000000 := rfl
    have hx : (point 776+point 777)/2 = (2823731:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_776
  · change upperValue ((point (777)+point ((777)+1))/2) ≤ payment (777)
    have hp : payment 777 = (2737036237614:ℝ)/1000000000000 := rfl
    have hx : (point 777+point 778)/2 = (2825785:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_777
  · change upperValue ((point (778)+point ((778)+1))/2) ≤ payment (778)
    have hp : payment 778 = (2733683668563:ℝ)/1000000000000 := rfl
    have hx : (point 778+point 779)/2 = (942613:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_778
  · change upperValue ((point (779)+point ((779)+1))/2) ≤ payment (779)
    have hp : payment 779 = (2730335095894:ℝ)/1000000000000 := rfl
    have hx : (point 779+point 780)/2 = (2829893:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_779
  · change upperValue ((point (780)+point ((780)+1))/2) ≤ payment (780)
    have hp : payment 780 = (2726990510281:ℝ)/1000000000000 := rfl
    have hx : (point 780+point 781)/2 = (2831947:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_780
  · change upperValue ((point (781)+point ((781)+1))/2) ≤ payment (781)
    have hp : payment 781 = (2723649902424:ℝ)/1000000000000 := rfl
    have hx : (point 781+point 782)/2 = (944667:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_781
  · change upperValue ((point (782)+point ((782)+1))/2) ≤ payment (782)
    have hp : payment 782 = (2720313263051:ℝ)/1000000000000 := rfl
    have hx : (point 782+point 783)/2 = (2836055:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_782
  · change upperValue ((point (783)+point ((783)+1))/2) ≤ payment (783)
    have hp : payment 783 = (2716980582916:ℝ)/1000000000000 := rfl
    have hx : (point 783+point 784)/2 = (2838109:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_783
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_048
