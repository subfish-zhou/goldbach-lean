import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints118
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_118 (j : Fin 16) : upperValue ((point (16*118+j.val)+point ((16*118+j.val)+1))/2) ≤ payment (16*118+j.val) := by
  fin_cases j
  · change upperValue ((point (1888)+point ((1888)+1))/2) ≤ payment (1888)
    have hp : payment 1888 = (272066770943:ℝ)/1000000000000 := rfl
    have hx : (point 1888+point 1889)/2 = (1702593:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1888
  · change upperValue ((point (1889)+point ((1889)+1))/2) ≤ payment (1889)
    have hp : payment 1889 = (270350575446:ℝ)/1000000000000 := rfl
    have hx : (point 1889+point 1890)/2 = (5109833:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1889
  · change upperValue ((point (1890)+point ((1890)+1))/2) ≤ payment (1890)
    have hp : payment 1890 = (268634579024:ℝ)/1000000000000 := rfl
    have hx : (point 1890+point 1891)/2 = (5111887:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1890
  · change upperValue ((point (1891)+point ((1891)+1))/2) ≤ payment (1891)
    have hp : payment 1891 = (266918780367:ℝ)/1000000000000 := rfl
    have hx : (point 1891+point 1892)/2 = (1704647:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1891
  · change upperValue ((point (1892)+point ((1892)+1))/2) ≤ payment (1892)
    have hp : payment 1892 = (265203178164:ℝ)/1000000000000 := rfl
    have hx : (point 1892+point 1893)/2 = (5115995:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1892
  · change upperValue ((point (1893)+point ((1893)+1))/2) ≤ payment (1893)
    have hp : payment 1893 = (263487771107:ℝ)/1000000000000 := rfl
    have hx : (point 1893+point 1894)/2 = (5118049:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1893
  · change upperValue ((point (1894)+point ((1894)+1))/2) ≤ payment (1894)
    have hp : payment 1894 = (261772557888:ℝ)/1000000000000 := rfl
    have hx : (point 1894+point 1895)/2 = (1706701:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1894
  · change upperValue ((point (1895)+point ((1895)+1))/2) ≤ payment (1895)
    have hp : payment 1895 = (260057537199:ℝ)/1000000000000 := rfl
    have hx : (point 1895+point 1896)/2 = (5122157:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1895
  · change upperValue ((point (1896)+point ((1896)+1))/2) ≤ payment (1896)
    have hp : payment 1896 = (258342707735:ℝ)/1000000000000 := rfl
    have hx : (point 1896+point 1897)/2 = (5124211:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1896
  · change upperValue ((point (1897)+point ((1897)+1))/2) ≤ payment (1897)
    have hp : payment 1897 = (256628068189:ℝ)/1000000000000 := rfl
    have hx : (point 1897+point 1898)/2 = (1708755:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1897
  · change upperValue ((point (1898)+point ((1898)+1))/2) ≤ payment (1898)
    have hp : payment 1898 = (254913617257:ℝ)/1000000000000 := rfl
    have hx : (point 1898+point 1899)/2 = (5128319:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1898
  · change upperValue ((point (1899)+point ((1899)+1))/2) ≤ payment (1899)
    have hp : payment 1899 = (253199353635:ℝ)/1000000000000 := rfl
    have hx : (point 1899+point 1900)/2 = (5130373:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1899
  · change upperValue ((point (1900)+point ((1900)+1))/2) ≤ payment (1900)
    have hp : payment 1900 = (251485276020:ℝ)/1000000000000 := rfl
    have hx : (point 1900+point 1901)/2 = (1710809:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1900
  · change upperValue ((point (1901)+point ((1901)+1))/2) ≤ payment (1901)
    have hp : payment 1901 = (249771383111:ℝ)/1000000000000 := rfl
    have hx : (point 1901+point 1902)/2 = (5134481:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1901
  · change upperValue ((point (1902)+point ((1902)+1))/2) ≤ payment (1902)
    have hp : payment 1902 = (248057673605:ℝ)/1000000000000 := rfl
    have hx : (point 1902+point 1903)/2 = (5136535:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1902
  · change upperValue ((point (1903)+point ((1903)+1))/2) ≤ payment (1903)
    have hp : payment 1903 = (246344146203:ℝ)/1000000000000 := rfl
    have hx : (point 1903+point 1904)/2 = (1712863:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1903
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_118
