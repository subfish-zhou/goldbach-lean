import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints057
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_057 (j : Fin 16) : upperValue ((point (16*57+j.val)+point ((16*57+j.val)+1))/2) ≤ payment (16*57+j.val) := by
  fin_cases j
  · change upperValue ((point (912)+point ((912)+1))/2) ≤ payment (912)
    have hp : payment 912 = (2317166906455:ℝ)/1000000000000 := rfl
    have hx : (point 912+point 913)/2 = (3103075:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_912
  · change upperValue ((point (913)+point ((913)+1))/2) ≤ payment (913)
    have hp : payment 913 = (2314278968470:ℝ)/1000000000000 := rfl
    have hx : (point 913+point 914)/2 = (1035043:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_913
  · change upperValue ((point (914)+point ((914)+1))/2) ≤ payment (914)
    have hp : payment 914 = (2311393973558:ℝ)/1000000000000 := rfl
    have hx : (point 914+point 915)/2 = (3107183:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_914
  · change upperValue ((point (915)+point ((915)+1))/2) ≤ payment (915)
    have hp : payment 915 = (2308511915238:ℝ)/1000000000000 := rfl
    have hx : (point 915+point 916)/2 = (3109237:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_915
  · change upperValue ((point (916)+point ((916)+1))/2) ≤ payment (916)
    have hp : payment 916 = (2305632787045:ℝ)/1000000000000 := rfl
    have hx : (point 916+point 917)/2 = (1037097:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_916
  · change upperValue ((point (917)+point ((917)+1))/2) ≤ payment (917)
    have hp : payment 917 = (2302756582532:ℝ)/1000000000000 := rfl
    have hx : (point 917+point 918)/2 = (3113345:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_917
  · change upperValue ((point (918)+point ((918)+1))/2) ≤ payment (918)
    have hp : payment 918 = (2299883295268:ℝ)/1000000000000 := rfl
    have hx : (point 918+point 919)/2 = (3115399:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_918
  · change upperValue ((point (919)+point ((919)+1))/2) ≤ payment (919)
    have hp : payment 919 = (2297012918836:ℝ)/1000000000000 := rfl
    have hx : (point 919+point 920)/2 = (1039151:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_919
  · change upperValue ((point (920)+point ((920)+1))/2) ≤ payment (920)
    have hp : payment 920 = (2294145446839:ℝ)/1000000000000 := rfl
    have hx : (point 920+point 921)/2 = (3119507:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_920
  · change upperValue ((point (921)+point ((921)+1))/2) ≤ payment (921)
    have hp : payment 921 = (2291280872892:ℝ)/1000000000000 := rfl
    have hx : (point 921+point 922)/2 = (3121561:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_921
  · change upperValue ((point (922)+point ((922)+1))/2) ≤ payment (922)
    have hp : payment 922 = (2288419190631:ℝ)/1000000000000 := rfl
    have hx : (point 922+point 923)/2 = (1041205:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_922
  · change upperValue ((point (923)+point ((923)+1))/2) ≤ payment (923)
    have hp : payment 923 = (2285560393705:ℝ)/1000000000000 := rfl
    have hx : (point 923+point 924)/2 = (3125669:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_923
  · change upperValue ((point (924)+point ((924)+1))/2) ≤ payment (924)
    have hp : payment 924 = (2282704475780:ℝ)/1000000000000 := rfl
    have hx : (point 924+point 925)/2 = (3127723:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_924
  · change upperValue ((point (925)+point ((925)+1))/2) ≤ payment (925)
    have hp : payment 925 = (2279851430536:ℝ)/1000000000000 := rfl
    have hx : (point 925+point 926)/2 = (1043259:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_925
  · change upperValue ((point (926)+point ((926)+1))/2) ≤ payment (926)
    have hp : payment 926 = (2277001251673:ℝ)/1000000000000 := rfl
    have hx : (point 926+point 927)/2 = (3131831:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_926
  · change upperValue ((point (927)+point ((927)+1))/2) ≤ payment (927)
    have hp : payment 927 = (2274153932904:ℝ)/1000000000000 := rfl
    have hx : (point 927+point 928)/2 = (3133885:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_927
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_057
