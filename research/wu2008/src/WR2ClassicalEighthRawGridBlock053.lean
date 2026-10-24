import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints053
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_053 (j : Fin 16) : upperValue ((point (16*53+j.val)+point ((16*53+j.val)+1))/2) ≤ payment (16*53+j.val) := by
  fin_cases j
  · change upperValue ((point (848)+point ((848)+1))/2) ≤ payment (848)
    have hp : payment 848 = (2508426360931:ℝ)/1000000000000 := rfl
    have hx : (point 848+point 849)/2 = (2971619:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_848
  · change upperValue ((point (849)+point ((849)+1))/2) ≤ payment (849)
    have hp : payment 849 = (2505335785320:ℝ)/1000000000000 := rfl
    have hx : (point 849+point 850)/2 = (2973673:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_849
  · change upperValue ((point (850)+point ((850)+1))/2) ≤ payment (850)
    have hp : payment 850 = (2502248604626:ℝ)/1000000000000 := rfl
    have hx : (point 850+point 851)/2 = (991909:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_850
  · change upperValue ((point (851)+point ((851)+1))/2) ≤ payment (851)
    have hp : payment 851 = (2499164811184:ℝ)/1000000000000 := rfl
    have hx : (point 851+point 852)/2 = (2977781:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_851
  · change upperValue ((point (852)+point ((852)+1))/2) ≤ payment (852)
    have hp : payment 852 = (2496084397351:ℝ)/1000000000000 := rfl
    have hx : (point 852+point 853)/2 = (2979835:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_852
  · change upperValue ((point (853)+point ((853)+1))/2) ≤ payment (853)
    have hp : payment 853 = (2493007355505:ℝ)/1000000000000 := rfl
    have hx : (point 853+point 854)/2 = (993963:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_853
  · change upperValue ((point (854)+point ((854)+1))/2) ≤ payment (854)
    have hp : payment 854 = (2489933678042:ℝ)/1000000000000 := rfl
    have hx : (point 854+point 855)/2 = (2983943:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_854
  · change upperValue ((point (855)+point ((855)+1))/2) ≤ payment (855)
    have hp : payment 855 = (2486863357382:ℝ)/1000000000000 := rfl
    have hx : (point 855+point 856)/2 = (2985997:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_855
  · change upperValue ((point (856)+point ((856)+1))/2) ≤ payment (856)
    have hp : payment 856 = (2483796385963:ℝ)/1000000000000 := rfl
    have hx : (point 856+point 857)/2 = (996017:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_856
  · change upperValue ((point (857)+point ((857)+1))/2) ≤ payment (857)
    have hp : payment 857 = (2480732756242:ℝ)/1000000000000 := rfl
    have hx : (point 857+point 858)/2 = (2990105:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_857
  · change upperValue ((point (858)+point ((858)+1))/2) ≤ payment (858)
    have hp : payment 858 = (2477672460700:ℝ)/1000000000000 := rfl
    have hx : (point 858+point 859)/2 = (2992159:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_858
  · change upperValue ((point (859)+point ((859)+1))/2) ≤ payment (859)
    have hp : payment 859 = (2474615491834:ℝ)/1000000000000 := rfl
    have hx : (point 859+point 860)/2 = (998071:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_859
  · change upperValue ((point (860)+point ((860)+1))/2) ≤ payment (860)
    have hp : payment 860 = (2471561842162:ℝ)/1000000000000 := rfl
    have hx : (point 860+point 861)/2 = (2996267:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_860
  · change upperValue ((point (861)+point ((861)+1))/2) ≤ payment (861)
    have hp : payment 861 = (2468511504225:ℝ)/1000000000000 := rfl
    have hx : (point 861+point 862)/2 = (2998321:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_861
  · change upperValue ((point (862)+point ((862)+1))/2) ≤ payment (862)
    have hp : payment 862 = (2465464470580:ℝ)/1000000000000 := rfl
    have hx : (point 862+point 863)/2 = (1000125:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_862
  · change upperValue ((point (863)+point ((863)+1))/2) ≤ payment (863)
    have hp : payment 863 = (2462420733805:ℝ)/1000000000000 := rfl
    have hx : (point 863+point 864)/2 = (3002429:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_863
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_053
