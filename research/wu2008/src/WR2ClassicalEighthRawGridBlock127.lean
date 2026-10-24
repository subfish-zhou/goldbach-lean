import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints127
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_127 (j : Fin 16) : upperValue ((point (16*127+j.val)+point ((16*127+j.val)+1))/2) ≤ payment (16*127+j.val) := by
  fin_cases j
  · change upperValue ((point (2032)+point ((2032)+1))/2) ≤ payment (2032)
    have hp : payment 2032 = (26358835016:ℝ)/1000000000000 := rfl
    have hx : (point 2032+point 2033)/2 = (1801185:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2032
  · change upperValue ((point (2033)+point ((2033)+1))/2) ≤ payment (2033)
    have hp : payment 2033 = (24658176831:ℝ)/1000000000000 := rfl
    have hx : (point 2033+point 2034)/2 = (5405609:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2033
  · change upperValue ((point (2034)+point ((2034)+1))/2) ≤ payment (2034)
    have hp : payment 2034 = (22957536292:ℝ)/1000000000000 := rfl
    have hx : (point 2034+point 2035)/2 = (5407663:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2034
  · change upperValue ((point (2035)+point ((2035)+1))/2) ≤ payment (2035)
    have hp : payment 2035 = (21256912179:ℝ)/1000000000000 := rfl
    have hx : (point 2035+point 2036)/2 = (1803239:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2035
  · change upperValue ((point (2036)+point ((2036)+1))/2) ≤ payment (2036)
    have hp : payment 2036 = (19556303273:ℝ)/1000000000000 := rfl
    have hx : (point 2036+point 2037)/2 = (5411771:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2036
  · change upperValue ((point (2037)+point ((2037)+1))/2) ≤ payment (2037)
    have hp : payment 2037 = (17855708356:ℝ)/1000000000000 := rfl
    have hx : (point 2037+point 2038)/2 = (5413825:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2037
  · change upperValue ((point (2038)+point ((2038)+1))/2) ≤ payment (2038)
    have hp : payment 2038 = (16155126209:ℝ)/1000000000000 := rfl
    have hx : (point 2038+point 2039)/2 = (1805293:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2038
  · change upperValue ((point (2039)+point ((2039)+1))/2) ≤ payment (2039)
    have hp : payment 2039 = (14454555614:ℝ)/1000000000000 := rfl
    have hx : (point 2039+point 2040)/2 = (5417933:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2039
  · change upperValue ((point (2040)+point ((2040)+1))/2) ≤ payment (2040)
    have hp : payment 2040 = (12753995353:ℝ)/1000000000000 := rfl
    have hx : (point 2040+point 2041)/2 = (5419987:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2040
  · change upperValue ((point (2041)+point ((2041)+1))/2) ≤ payment (2041)
    have hp : payment 2041 = (11053444209:ℝ)/1000000000000 := rfl
    have hx : (point 2041+point 2042)/2 = (1807347:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2041
  · change upperValue ((point (2042)+point ((2042)+1))/2) ≤ payment (2042)
    have hp : payment 2042 = (9352900965:ℝ)/1000000000000 := rfl
    have hx : (point 2042+point 2043)/2 = (5424095:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2042
  · change upperValue ((point (2043)+point ((2043)+1))/2) ≤ payment (2043)
    have hp : payment 2043 = (7652364405:ℝ)/1000000000000 := rfl
    have hx : (point 2043+point 2044)/2 = (5426149:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2043
  · change upperValue ((point (2044)+point ((2044)+1))/2) ≤ payment (2044)
    have hp : payment 2044 = (5951833313:ℝ)/1000000000000 := rfl
    have hx : (point 2044+point 2045)/2 = (1809401:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2044
  · change upperValue ((point (2045)+point ((2045)+1))/2) ≤ payment (2045)
    have hp : payment 2045 = (4251306473:ℝ)/1000000000000 := rfl
    have hx : (point 2045+point 2046)/2 = (5430257:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2045
  · change upperValue ((point (2046)+point ((2046)+1))/2) ≤ payment (2046)
    have hp : payment 2046 = (2550782669:ℝ)/1000000000000 := rfl
    have hx : (point 2046+point 2047)/2 = (5432311:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2046
  · change upperValue ((point (2047)+point ((2047)+1))/2) ≤ payment (2047)
    have hp : payment 2047 = (850260688:ℝ)/1000000000000 := rfl
    have hx : (point 2047+point 2048)/2 = (1811455:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2047
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_127
