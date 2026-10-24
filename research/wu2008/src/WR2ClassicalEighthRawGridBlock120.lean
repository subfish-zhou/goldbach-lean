import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints120
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_120 (j : Fin 16) : upperValue ((point (16*120+j.val)+point ((16*120+j.val)+1))/2) ≤ payment (16*120+j.val) := by
  fin_cases j
  · change upperValue ((point (1920)+point ((1920)+1))/2) ≤ payment (1920)
    have hp : payment 1920 = (217240785988:ℝ)/1000000000000 := rfl
    have hx : (point 1920+point 1921)/2 = (5173507:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1920
  · change upperValue ((point (1921)+point ((1921)+1))/2) ≤ payment (1921)
    have hp : payment 1921 = (215530314993:ℝ)/1000000000000 := rfl
    have hx : (point 1921+point 1922)/2 = (1725187:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1921
  · change upperValue ((point (1922)+point ((1922)+1))/2) ≤ payment (1922)
    have hp : payment 1922 = (213820001546:ℝ)/1000000000000 := rfl
    have hx : (point 1922+point 1923)/2 = (5177615:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1922
  · change upperValue ((point (1923)+point ((1923)+1))/2) ≤ payment (1923)
    have hp : payment 1923 = (212109844362:ℝ)/1000000000000 := rfl
    have hx : (point 1923+point 1924)/2 = (5179669:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1923
  · change upperValue ((point (1924)+point ((1924)+1))/2) ≤ payment (1924)
    have hp : payment 1924 = (210399842158:ℝ)/1000000000000 := rfl
    have hx : (point 1924+point 1925)/2 = (1727241:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1924
  · change upperValue ((point (1925)+point ((1925)+1))/2) ≤ payment (1925)
    have hp : payment 1925 = (208689993649:ℝ)/1000000000000 := rfl
    have hx : (point 1925+point 1926)/2 = (5183777:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1925
  · change upperValue ((point (1926)+point ((1926)+1))/2) ≤ payment (1926)
    have hp : payment 1926 = (206980297555:ℝ)/1000000000000 := rfl
    have hx : (point 1926+point 1927)/2 = (5185831:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1926
  · change upperValue ((point (1927)+point ((1927)+1))/2) ≤ payment (1927)
    have hp : payment 1927 = (205270752593:ℝ)/1000000000000 := rfl
    have hx : (point 1927+point 1928)/2 = (1729295:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1927
  · change upperValue ((point (1928)+point ((1928)+1))/2) ≤ payment (1928)
    have hp : payment 1928 = (203561357482:ℝ)/1000000000000 := rfl
    have hx : (point 1928+point 1929)/2 = (5189939:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1928
  · change upperValue ((point (1929)+point ((1929)+1))/2) ≤ payment (1929)
    have hp : payment 1929 = (201852110943:ℝ)/1000000000000 := rfl
    have hx : (point 1929+point 1930)/2 = (5191993:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1929
  · change upperValue ((point (1930)+point ((1930)+1))/2) ≤ payment (1930)
    have hp : payment 1930 = (200143011696:ℝ)/1000000000000 := rfl
    have hx : (point 1930+point 1931)/2 = (1731349:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1930
  · change upperValue ((point (1931)+point ((1931)+1))/2) ≤ payment (1931)
    have hp : payment 1931 = (198434058462:ℝ)/1000000000000 := rfl
    have hx : (point 1931+point 1932)/2 = (5196101:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1931
  · change upperValue ((point (1932)+point ((1932)+1))/2) ≤ payment (1932)
    have hp : payment 1932 = (196725249964:ℝ)/1000000000000 := rfl
    have hx : (point 1932+point 1933)/2 = (5198155:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1932
  · change upperValue ((point (1933)+point ((1933)+1))/2) ≤ payment (1933)
    have hp : payment 1933 = (195016584924:ℝ)/1000000000000 := rfl
    have hx : (point 1933+point 1934)/2 = (1733403:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1933
  · change upperValue ((point (1934)+point ((1934)+1))/2) ≤ payment (1934)
    have hp : payment 1934 = (193308062066:ℝ)/1000000000000 := rfl
    have hx : (point 1934+point 1935)/2 = (5202263:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1934
  · change upperValue ((point (1935)+point ((1935)+1))/2) ≤ payment (1935)
    have hp : payment 1935 = (191599680114:ℝ)/1000000000000 := rfl
    have hx : (point 1935+point 1936)/2 = (5204317:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1935
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_120
