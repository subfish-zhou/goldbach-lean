import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints122
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_122 (j : Fin 16) : upperValue ((point (16*122+j.val)+point ((16*122+j.val)+1))/2) ≤ payment (16*122+j.val) := by
  fin_cases j
  · change upperValue ((point (1952)+point ((1952)+1))/2) ≤ payment (1952)
    have hp : payment 1952 = (162577512848:ℝ)/1000000000000 := rfl
    have hx : (point 1952+point 1953)/2 = (5239235:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1952
  · change upperValue ((point (1953)+point ((1953)+1))/2) ≤ payment (1953)
    have hp : payment 1953 = (160871449864:ℝ)/1000000000000 := rfl
    have hx : (point 1953+point 1954)/2 = (5241289:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1953
  · change upperValue ((point (1954)+point ((1954)+1))/2) ≤ payment (1954)
    have hp : payment 1954 = (159165503680:ℝ)/1000000000000 := rfl
    have hx : (point 1954+point 1955)/2 = (1747781:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1954
  · change upperValue ((point (1955)+point ((1955)+1))/2) ≤ payment (1955)
    have hp : payment 1955 = (157459673034:ℝ)/1000000000000 := rfl
    have hx : (point 1955+point 1956)/2 = (5245397:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1955
  · change upperValue ((point (1956)+point ((1956)+1))/2) ≤ payment (1956)
    have hp : payment 1956 = (155753956666:ℝ)/1000000000000 := rfl
    have hx : (point 1956+point 1957)/2 = (5247451:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1956
  · change upperValue ((point (1957)+point ((1957)+1))/2) ≤ payment (1957)
    have hp : payment 1957 = (154048353314:ℝ)/1000000000000 := rfl
    have hx : (point 1957+point 1958)/2 = (1749835:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1957
  · change upperValue ((point (1958)+point ((1958)+1))/2) ≤ payment (1958)
    have hp : payment 1958 = (152342861718:ℝ)/1000000000000 := rfl
    have hx : (point 1958+point 1959)/2 = (5251559:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1958
  · change upperValue ((point (1959)+point ((1959)+1))/2) ≤ payment (1959)
    have hp : payment 1959 = (150637480619:ℝ)/1000000000000 := rfl
    have hx : (point 1959+point 1960)/2 = (5253613:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1959
  · change upperValue ((point (1960)+point ((1960)+1))/2) ≤ payment (1960)
    have hp : payment 1960 = (148932208758:ℝ)/1000000000000 := rfl
    have hx : (point 1960+point 1961)/2 = (1751889:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1960
  · change upperValue ((point (1961)+point ((1961)+1))/2) ≤ payment (1961)
    have hp : payment 1961 = (147227044877:ℝ)/1000000000000 := rfl
    have hx : (point 1961+point 1962)/2 = (5257721:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1961
  · change upperValue ((point (1962)+point ((1962)+1))/2) ≤ payment (1962)
    have hp : payment 1962 = (145521987719:ℝ)/1000000000000 := rfl
    have hx : (point 1962+point 1963)/2 = (5259775:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1962
  · change upperValue ((point (1963)+point ((1963)+1))/2) ≤ payment (1963)
    have hp : payment 1963 = (143817036027:ℝ)/1000000000000 := rfl
    have hx : (point 1963+point 1964)/2 = (1753943:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1963
  · change upperValue ((point (1964)+point ((1964)+1))/2) ≤ payment (1964)
    have hp : payment 1964 = (142112188544:ℝ)/1000000000000 := rfl
    have hx : (point 1964+point 1965)/2 = (5263883:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1964
  · change upperValue ((point (1965)+point ((1965)+1))/2) ≤ payment (1965)
    have hp : payment 1965 = (140407444015:ℝ)/1000000000000 := rfl
    have hx : (point 1965+point 1966)/2 = (5265937:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1965
  · change upperValue ((point (1966)+point ((1966)+1))/2) ≤ payment (1966)
    have hp : payment 1966 = (138702801185:ℝ)/1000000000000 := rfl
    have hx : (point 1966+point 1967)/2 = (1755997:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1966
  · change upperValue ((point (1967)+point ((1967)+1))/2) ≤ payment (1967)
    have hp : payment 1967 = (136998258800:ℝ)/1000000000000 := rfl
    have hx : (point 1967+point 1968)/2 = (5270045:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1967
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_122
