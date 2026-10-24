import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints064
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_064 (j : Fin 16) : upperValue ((point (16*64+j.val)+point ((16*64+j.val)+1))/2) ≤ payment (16*64+j.val) := by
  fin_cases j
  · change upperValue ((point (1024)+point ((1024)+1))/2) ≤ payment (1024)
    have hp : payment 1024 = (2010630553750:ℝ)/1000000000000 := rfl
    have hx : (point 1024+point 1025)/2 = (1111041:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1024
  · change upperValue ((point (1025)+point ((1025)+1))/2) ≤ payment (1025)
    have hp : payment 1025 = (2008035404218:ℝ)/1000000000000 := rfl
    have hx : (point 1025+point 1026)/2 = (3335177:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1025
  · change upperValue ((point (1026)+point ((1026)+1))/2) ≤ payment (1026)
    have hp : payment 1026 = (2005442563243:ℝ)/1000000000000 := rfl
    have hx : (point 1026+point 1027)/2 = (3337231:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1026
  · change upperValue ((point (1027)+point ((1027)+1))/2) ≤ payment (1027)
    have hp : payment 1027 = (2002852025894:ℝ)/1000000000000 := rfl
    have hx : (point 1027+point 1028)/2 = (1113095:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1027
  · change upperValue ((point (1028)+point ((1028)+1))/2) ≤ payment (1028)
    have hp : payment 1028 = (2000263787252:ℝ)/1000000000000 := rfl
    have hx : (point 1028+point 1029)/2 = (3341339:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1028
  · change upperValue ((point (1029)+point ((1029)+1))/2) ≤ payment (1029)
    have hp : payment 1029 = (1997677842412:ℝ)/1000000000000 := rfl
    have hx : (point 1029+point 1030)/2 = (3343393:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1029
  · change upperValue ((point (1030)+point ((1030)+1))/2) ≤ payment (1030)
    have hp : payment 1030 = (1995094186479:ℝ)/1000000000000 := rfl
    have hx : (point 1030+point 1031)/2 = (1115149:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1030
  · change upperValue ((point (1031)+point ((1031)+1))/2) ≤ payment (1031)
    have hp : payment 1031 = (1992512814568:ℝ)/1000000000000 := rfl
    have hx : (point 1031+point 1032)/2 = (3347501:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1031
  · change upperValue ((point (1032)+point ((1032)+1))/2) ≤ payment (1032)
    have hp : payment 1032 = (1989933721806:ℝ)/1000000000000 := rfl
    have hx : (point 1032+point 1033)/2 = (3349555:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1032
  · change upperValue ((point (1033)+point ((1033)+1))/2) ≤ payment (1033)
    have hp : payment 1033 = (1987356903334:ℝ)/1000000000000 := rfl
    have hx : (point 1033+point 1034)/2 = (1117203:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1033
  · change upperValue ((point (1034)+point ((1034)+1))/2) ≤ payment (1034)
    have hp : payment 1034 = (1984782354301:ℝ)/1000000000000 := rfl
    have hx : (point 1034+point 1035)/2 = (3353663:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1034
  · change upperValue ((point (1035)+point ((1035)+1))/2) ≤ payment (1035)
    have hp : payment 1035 = (1982210069867:ℝ)/1000000000000 := rfl
    have hx : (point 1035+point 1036)/2 = (3355717:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1035
  · change upperValue ((point (1036)+point ((1036)+1))/2) ≤ payment (1036)
    have hp : payment 1036 = (1979640045207:ℝ)/1000000000000 := rfl
    have hx : (point 1036+point 1037)/2 = (1119257:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1036
  · change upperValue ((point (1037)+point ((1037)+1))/2) ≤ payment (1037)
    have hp : payment 1037 = (1977072275504:ℝ)/1000000000000 := rfl
    have hx : (point 1037+point 1038)/2 = (3359825:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1037
  · change upperValue ((point (1038)+point ((1038)+1))/2) ≤ payment (1038)
    have hp : payment 1038 = (1974506755952:ℝ)/1000000000000 := rfl
    have hx : (point 1038+point 1039)/2 = (3361879:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1038
  · change upperValue ((point (1039)+point ((1039)+1))/2) ≤ payment (1039)
    have hp : payment 1039 = (1971943481758:ℝ)/1000000000000 := rfl
    have hx : (point 1039+point 1040)/2 = (1121311:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1039
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_064
