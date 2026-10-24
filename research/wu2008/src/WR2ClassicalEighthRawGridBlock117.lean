import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints117
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_117 (j : Fin 16) : upperValue ((point (16*117+j.val)+point ((16*117+j.val)+1))/2) ≤ payment (16*117+j.val) := by
  fin_cases j
  · change upperValue ((point (1872)+point ((1872)+1))/2) ≤ payment (1872)
    have hp : payment 1872 = (299554046003:ℝ)/1000000000000 := rfl
    have hx : (point 1872+point 1873)/2 = (5074915:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1872
  · change upperValue ((point (1873)+point ((1873)+1))/2) ≤ payment (1873)
    have hp : payment 1873 = (297834486335:ℝ)/1000000000000 := rfl
    have hx : (point 1873+point 1874)/2 = (1692323:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1873
  · change upperValue ((point (1874)+point ((1874)+1))/2) ≤ payment (1874)
    have hp : payment 1874 = (296115146835:ℝ)/1000000000000 := rfl
    have hx : (point 1874+point 1875)/2 = (5079023:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1874
  · change upperValue ((point (1875)+point ((1875)+1))/2) ≤ payment (1875)
    have hp : payment 1875 = (294396026175:ℝ)/1000000000000 := rfl
    have hx : (point 1875+point 1876)/2 = (5081077:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1875
  · change upperValue ((point (1876)+point ((1876)+1))/2) ≤ payment (1876)
    have hp : payment 1876 = (292677123033:ℝ)/1000000000000 := rfl
    have hx : (point 1876+point 1877)/2 = (1694377:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1876
  · change upperValue ((point (1877)+point ((1877)+1))/2) ≤ payment (1877)
    have hp : payment 1877 = (290958436084:ℝ)/1000000000000 := rfl
    have hx : (point 1877+point 1878)/2 = (5085185:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1877
  · change upperValue ((point (1878)+point ((1878)+1))/2) ≤ payment (1878)
    have hp : payment 1878 = (289239964008:ℝ)/1000000000000 := rfl
    have hx : (point 1878+point 1879)/2 = (5087239:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1878
  · change upperValue ((point (1879)+point ((1879)+1))/2) ≤ payment (1879)
    have hp : payment 1879 = (287521705481:ℝ)/1000000000000 := rfl
    have hx : (point 1879+point 1880)/2 = (1696431:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1879
  · change upperValue ((point (1880)+point ((1880)+1))/2) ≤ payment (1880)
    have hp : payment 1880 = (285803659185:ℝ)/1000000000000 := rfl
    have hx : (point 1880+point 1881)/2 = (5091347:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1880
  · change upperValue ((point (1881)+point ((1881)+1))/2) ≤ payment (1881)
    have hp : payment 1881 = (284085823800:ℝ)/1000000000000 := rfl
    have hx : (point 1881+point 1882)/2 = (5093401:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1881
  · change upperValue ((point (1882)+point ((1882)+1))/2) ≤ payment (1882)
    have hp : payment 1882 = (282368198006:ℝ)/1000000000000 := rfl
    have hx : (point 1882+point 1883)/2 = (1698485:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1882
  · change upperValue ((point (1883)+point ((1883)+1))/2) ≤ payment (1883)
    have hp : payment 1883 = (280650780486:ℝ)/1000000000000 := rfl
    have hx : (point 1883+point 1884)/2 = (5097509:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1883
  · change upperValue ((point (1884)+point ((1884)+1))/2) ≤ payment (1884)
    have hp : payment 1884 = (278933569924:ℝ)/1000000000000 := rfl
    have hx : (point 1884+point 1885)/2 = (5099563:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1884
  · change upperValue ((point (1885)+point ((1885)+1))/2) ≤ payment (1885)
    have hp : payment 1885 = (277216565003:ℝ)/1000000000000 := rfl
    have hx : (point 1885+point 1886)/2 = (1700539:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1885
  · change upperValue ((point (1886)+point ((1886)+1))/2) ≤ payment (1886)
    have hp : payment 1886 = (275499764408:ℝ)/1000000000000 := rfl
    have hx : (point 1886+point 1887)/2 = (5103671:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1886
  · change upperValue ((point (1887)+point ((1887)+1))/2) ≤ payment (1887)
    have hp : payment 1887 = (273783166826:ℝ)/1000000000000 := rfl
    have hx : (point 1887+point 1888)/2 = (5105725:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1887
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_117
