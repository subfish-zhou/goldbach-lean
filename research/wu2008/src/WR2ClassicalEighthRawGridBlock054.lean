import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints054
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_054 (j : Fin 16) : upperValue ((point (16*54+j.val)+point ((16*54+j.val)+1))/2) ≤ payment (16*54+j.val) := by
  fin_cases j
  · change upperValue ((point (864)+point ((864)+1))/2) ≤ payment (864)
    have hp : payment 864 = (2459380286499:ℝ)/1000000000000 := rfl
    have hx : (point 864+point 865)/2 = (3004483:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_864
  · change upperValue ((point (865)+point ((865)+1))/2) ≤ payment (865)
    have hp : payment 865 = (2456343121279:ℝ)/1000000000000 := rfl
    have hx : (point 865+point 866)/2 = (1002179:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_865
  · change upperValue ((point (866)+point ((866)+1))/2) ≤ payment (866)
    have hp : payment 866 = (2453309230782:ℝ)/1000000000000 := rfl
    have hx : (point 866+point 867)/2 = (3008591:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_866
  · change upperValue ((point (867)+point ((867)+1))/2) ≤ payment (867)
    have hp : payment 867 = (2450278607665:ℝ)/1000000000000 := rfl
    have hx : (point 867+point 868)/2 = (3010645:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_867
  · change upperValue ((point (868)+point ((868)+1))/2) ≤ payment (868)
    have hp : payment 868 = (2447251244604:ℝ)/1000000000000 := rfl
    have hx : (point 868+point 869)/2 = (1004233:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_868
  · change upperValue ((point (869)+point ((869)+1))/2) ≤ payment (869)
    have hp : payment 869 = (2444227134295:ℝ)/1000000000000 := rfl
    have hx : (point 869+point 870)/2 = (3014753:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_869
  · change upperValue ((point (870)+point ((870)+1))/2) ≤ payment (870)
    have hp : payment 870 = (2441206269452:ℝ)/1000000000000 := rfl
    have hx : (point 870+point 871)/2 = (3016807:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_870
  · change upperValue ((point (871)+point ((871)+1))/2) ≤ payment (871)
    have hp : payment 871 = (2438188642810:ℝ)/1000000000000 := rfl
    have hx : (point 871+point 872)/2 = (1006287:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_871
  · change upperValue ((point (872)+point ((872)+1))/2) ≤ payment (872)
    have hp : payment 872 = (2435174247122:ℝ)/1000000000000 := rfl
    have hx : (point 872+point 873)/2 = (3020915:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_872
  · change upperValue ((point (873)+point ((873)+1))/2) ≤ payment (873)
    have hp : payment 873 = (2432163075160:ℝ)/1000000000000 := rfl
    have hx : (point 873+point 874)/2 = (3022969:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_873
  · change upperValue ((point (874)+point ((874)+1))/2) ≤ payment (874)
    have hp : payment 874 = (2429155119715:ℝ)/1000000000000 := rfl
    have hx : (point 874+point 875)/2 = (1008341:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_874
  · change upperValue ((point (875)+point ((875)+1))/2) ≤ payment (875)
    have hp : payment 875 = (2426150373599:ℝ)/1000000000000 := rfl
    have hx : (point 875+point 876)/2 = (3027077:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_875
  · change upperValue ((point (876)+point ((876)+1))/2) ≤ payment (876)
    have hp : payment 876 = (2423148829640:ℝ)/1000000000000 := rfl
    have hx : (point 876+point 877)/2 = (3029131:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_876
  · change upperValue ((point (877)+point ((877)+1))/2) ≤ payment (877)
    have hp : payment 877 = (2420150480686:ℝ)/1000000000000 := rfl
    have hx : (point 877+point 878)/2 = (1010395:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_877
  · change upperValue ((point (878)+point ((878)+1))/2) ≤ payment (878)
    have hp : payment 878 = (2417155319605:ℝ)/1000000000000 := rfl
    have hx : (point 878+point 879)/2 = (3033239:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_878
  · change upperValue ((point (879)+point ((879)+1))/2) ≤ payment (879)
    have hp : payment 879 = (2414163339282:ℝ)/1000000000000 := rfl
    have hx : (point 879+point 880)/2 = (3035293:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_879
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_054
