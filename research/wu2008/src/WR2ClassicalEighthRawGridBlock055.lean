import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints055
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_055 (j : Fin 16) : upperValue ((point (16*55+j.val)+point ((16*55+j.val)+1))/2) ≤ payment (16*55+j.val) := by
  fin_cases j
  · change upperValue ((point (880)+point ((880)+1))/2) ≤ payment (880)
    have hp : payment 880 = (2411174532622:ℝ)/1000000000000 := rfl
    have hx : (point 880+point 881)/2 = (1012449:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_880
  · change upperValue ((point (881)+point ((881)+1))/2) ≤ payment (881)
    have hp : payment 881 = (2408188892547:ℝ)/1000000000000 := rfl
    have hx : (point 881+point 882)/2 = (3039401:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_881
  · change upperValue ((point (882)+point ((882)+1))/2) ≤ payment (882)
    have hp : payment 882 = (2405206412000:ℝ)/1000000000000 := rfl
    have hx : (point 882+point 883)/2 = (3041455:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_882
  · change upperValue ((point (883)+point ((883)+1))/2) ≤ payment (883)
    have hp : payment 883 = (2402227083939:ℝ)/1000000000000 := rfl
    have hx : (point 883+point 884)/2 = (1014503:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_883
  · change upperValue ((point (884)+point ((884)+1))/2) ≤ payment (884)
    have hp : payment 884 = (2399250901343:ℝ)/1000000000000 := rfl
    have hx : (point 884+point 885)/2 = (3045563:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_884
  · change upperValue ((point (885)+point ((885)+1))/2) ≤ payment (885)
    have hp : payment 885 = (2396277857210:ℝ)/1000000000000 := rfl
    have hx : (point 885+point 886)/2 = (3047617:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_885
  · change upperValue ((point (886)+point ((886)+1))/2) ≤ payment (886)
    have hp : payment 886 = (2393307944553:ℝ)/1000000000000 := rfl
    have hx : (point 886+point 887)/2 = (1016557:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_886
  · change upperValue ((point (887)+point ((887)+1))/2) ≤ payment (887)
    have hp : payment 887 = (2390341156407:ℝ)/1000000000000 := rfl
    have hx : (point 887+point 888)/2 = (3051725:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_887
  · change upperValue ((point (888)+point ((888)+1))/2) ≤ payment (888)
    have hp : payment 888 = (2387377485822:ℝ)/1000000000000 := rfl
    have hx : (point 888+point 889)/2 = (3053779:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_888
  · change upperValue ((point (889)+point ((889)+1))/2) ≤ payment (889)
    have hp : payment 889 = (2384416925868:ℝ)/1000000000000 := rfl
    have hx : (point 889+point 890)/2 = (1018611:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_889
  · change upperValue ((point (890)+point ((890)+1))/2) ≤ payment (890)
    have hp : payment 890 = (2381459469632:ℝ)/1000000000000 := rfl
    have hx : (point 890+point 891)/2 = (3057887:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_890
  · change upperValue ((point (891)+point ((891)+1))/2) ≤ payment (891)
    have hp : payment 891 = (2378505110221:ℝ)/1000000000000 := rfl
    have hx : (point 891+point 892)/2 = (3059941:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_891
  · change upperValue ((point (892)+point ((892)+1))/2) ≤ payment (892)
    have hp : payment 892 = (2375553840756:ℝ)/1000000000000 := rfl
    have hx : (point 892+point 893)/2 = (1020665:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_892
  · change upperValue ((point (893)+point ((893)+1))/2) ≤ payment (893)
    have hp : payment 893 = (2372605654380:ℝ)/1000000000000 := rfl
    have hx : (point 893+point 894)/2 = (3064049:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_893
  · change upperValue ((point (894)+point ((894)+1))/2) ≤ payment (894)
    have hp : payment 894 = (2369660544252:ℝ)/1000000000000 := rfl
    have hx : (point 894+point 895)/2 = (3066103:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_894
  · change upperValue ((point (895)+point ((895)+1))/2) ≤ payment (895)
    have hp : payment 895 = (2366718503548:ℝ)/1000000000000 := rfl
    have hx : (point 895+point 896)/2 = (1022719:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_895
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_055
