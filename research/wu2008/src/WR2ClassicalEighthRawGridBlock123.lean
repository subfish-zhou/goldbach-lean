import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints123
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_123 (j : Fin 16) : upperValue ((point (16*123+j.val)+point ((16*123+j.val)+1))/2) ≤ payment (16*123+j.val) := by
  fin_cases j
  · change upperValue ((point (1968)+point ((1968)+1))/2) ≤ payment (1968)
    have hp : payment 1968 = (135293815605:ℝ)/1000000000000 := rfl
    have hx : (point 1968+point 1969)/2 = (5272099:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1968
  · change upperValue ((point (1969)+point ((1969)+1))/2) ≤ payment (1969)
    have hp : payment 1969 = (133589470348:ℝ)/1000000000000 := rfl
    have hx : (point 1969+point 1970)/2 = (1758051:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1969
  · change upperValue ((point (1970)+point ((1970)+1))/2) ≤ payment (1970)
    have hp : payment 1970 = (131885221777:ℝ)/1000000000000 := rfl
    have hx : (point 1970+point 1971)/2 = (5276207:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1970
  · change upperValue ((point (1971)+point ((1971)+1))/2) ≤ payment (1971)
    have hp : payment 1971 = (130181068639:ℝ)/1000000000000 := rfl
    have hx : (point 1971+point 1972)/2 = (5278261:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1971
  · change upperValue ((point (1972)+point ((1972)+1))/2) ≤ payment (1972)
    have hp : payment 1972 = (128477009682:ℝ)/1000000000000 := rfl
    have hx : (point 1972+point 1973)/2 = (1760105:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1972
  · change upperValue ((point (1973)+point ((1973)+1))/2) ≤ payment (1973)
    have hp : payment 1973 = (126773043657:ℝ)/1000000000000 := rfl
    have hx : (point 1973+point 1974)/2 = (5282369:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1973
  · change upperValue ((point (1974)+point ((1974)+1))/2) ≤ payment (1974)
    have hp : payment 1974 = (125069169313:ℝ)/1000000000000 := rfl
    have hx : (point 1974+point 1975)/2 = (5284423:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1974
  · change upperValue ((point (1975)+point ((1975)+1))/2) ≤ payment (1975)
    have hp : payment 1975 = (123365385401:ℝ)/1000000000000 := rfl
    have hx : (point 1975+point 1976)/2 = (1762159:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1975
  · change upperValue ((point (1976)+point ((1976)+1))/2) ≤ payment (1976)
    have hp : payment 1976 = (121661690671:ℝ)/1000000000000 := rfl
    have hx : (point 1976+point 1977)/2 = (5288531:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1976
  · change upperValue ((point (1977)+point ((1977)+1))/2) ≤ payment (1977)
    have hp : payment 1977 = (119958083875:ℝ)/1000000000000 := rfl
    have hx : (point 1977+point 1978)/2 = (5290585:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1977
  · change upperValue ((point (1978)+point ((1978)+1))/2) ≤ payment (1978)
    have hp : payment 1978 = (118254563766:ℝ)/1000000000000 := rfl
    have hx : (point 1978+point 1979)/2 = (1764213:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1978
  · change upperValue ((point (1979)+point ((1979)+1))/2) ≤ payment (1979)
    have hp : payment 1979 = (116551129096:ℝ)/1000000000000 := rfl
    have hx : (point 1979+point 1980)/2 = (5294693:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1979
  · change upperValue ((point (1980)+point ((1980)+1))/2) ≤ payment (1980)
    have hp : payment 1980 = (114847778619:ℝ)/1000000000000 := rfl
    have hx : (point 1980+point 1981)/2 = (5296747:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1980
  · change upperValue ((point (1981)+point ((1981)+1))/2) ≤ payment (1981)
    have hp : payment 1981 = (113144511089:ℝ)/1000000000000 := rfl
    have hx : (point 1981+point 1982)/2 = (1766267:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1981
  · change upperValue ((point (1982)+point ((1982)+1))/2) ≤ payment (1982)
    have hp : payment 1982 = (111441325260:ℝ)/1000000000000 := rfl
    have hx : (point 1982+point 1983)/2 = (5300855:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1982
  · change upperValue ((point (1983)+point ((1983)+1))/2) ≤ payment (1983)
    have hp : payment 1983 = (109738219887:ℝ)/1000000000000 := rfl
    have hx : (point 1983+point 1984)/2 = (5302909:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1983
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_123
