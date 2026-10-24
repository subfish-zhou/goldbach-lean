import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints050
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_050 (j : Fin 16) : upperValue ((point (16*50+j.val)+point ((16*50+j.val)+1))/2) ≤ payment (16*50+j.val) := by
  fin_cases j
  · change upperValue ((point (800)+point ((800)+1))/2) ≤ payment (800)
    have hp : payment 800 = (2660921949494:ℝ)/1000000000000 := rfl
    have hx : (point 800+point 801)/2 = (2873027:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_800
  · change upperValue ((point (801)+point ((801)+1))/2) ≤ payment (801)
    have hp : payment 801 = (2657658983879:ℝ)/1000000000000 := rfl
    have hx : (point 801+point 802)/2 = (2875081:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_801
  · change upperValue ((point (802)+point ((802)+1))/2) ≤ payment (802)
    have hp : payment 802 = (2654399806686:ℝ)/1000000000000 := rfl
    have hx : (point 802+point 803)/2 = (959045:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_802
  · change upperValue ((point (803)+point ((803)+1))/2) ≤ payment (803)
    have hp : payment 803 = (2651144409176:ℝ)/1000000000000 := rfl
    have hx : (point 803+point 804)/2 = (2879189:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_803
  · change upperValue ((point (804)+point ((804)+1))/2) ≤ payment (804)
    have hp : payment 804 = (2647892782631:ℝ)/1000000000000 := rfl
    have hx : (point 804+point 805)/2 = (2881243:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_804
  · change upperValue ((point (805)+point ((805)+1))/2) ≤ payment (805)
    have hp : payment 805 = (2644644918362:ℝ)/1000000000000 := rfl
    have hx : (point 805+point 806)/2 = (961099:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_805
  · change upperValue ((point (806)+point ((806)+1))/2) ≤ payment (806)
    have hp : payment 806 = (2641400807699:ℝ)/1000000000000 := rfl
    have hx : (point 806+point 807)/2 = (2885351:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_806
  · change upperValue ((point (807)+point ((807)+1))/2) ≤ payment (807)
    have hp : payment 807 = (2638160442000:ℝ)/1000000000000 := rfl
    have hx : (point 807+point 808)/2 = (2887405:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_807
  · change upperValue ((point (808)+point ((808)+1))/2) ≤ payment (808)
    have hp : payment 808 = (2634923812645:ℝ)/1000000000000 := rfl
    have hx : (point 808+point 809)/2 = (963153:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_808
  · change upperValue ((point (809)+point ((809)+1))/2) ≤ payment (809)
    have hp : payment 809 = (2631690911038:ℝ)/1000000000000 := rfl
    have hx : (point 809+point 810)/2 = (2891513:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_809
  · change upperValue ((point (810)+point ((810)+1))/2) ≤ payment (810)
    have hp : payment 810 = (2628461728607:ℝ)/1000000000000 := rfl
    have hx : (point 810+point 811)/2 = (2893567:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_810
  · change upperValue ((point (811)+point ((811)+1))/2) ≤ payment (811)
    have hp : payment 811 = (2625236256805:ℝ)/1000000000000 := rfl
    have hx : (point 811+point 812)/2 = (965207:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_811
  · change upperValue ((point (812)+point ((812)+1))/2) ≤ payment (812)
    have hp : payment 812 = (2622014487108:ℝ)/1000000000000 := rfl
    have hx : (point 812+point 813)/2 = (2897675:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_812
  · change upperValue ((point (813)+point ((813)+1))/2) ≤ payment (813)
    have hp : payment 813 = (2618796411014:ℝ)/1000000000000 := rfl
    have hx : (point 813+point 814)/2 = (2899729:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_813
  · change upperValue ((point (814)+point ((814)+1))/2) ≤ payment (814)
    have hp : payment 814 = (2615582020047:ℝ)/1000000000000 := rfl
    have hx : (point 814+point 815)/2 = (967261:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_814
  · change upperValue ((point (815)+point ((815)+1))/2) ≤ payment (815)
    have hp : payment 815 = (2612371305752:ℝ)/1000000000000 := rfl
    have hx : (point 815+point 816)/2 = (2903837:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_815
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_050
