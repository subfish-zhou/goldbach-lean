import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints121
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_121 (j : Fin 16) : upperValue ((point (16*121+j.val)+point ((16*121+j.val)+1))/2) ≤ payment (16*121+j.val) := by
  fin_cases j
  · change upperValue ((point (1936)+point ((1936)+1))/2) ≤ payment (1936)
    have hp : payment 1936 = (189891437794:ℝ)/1000000000000 := rfl
    have hx : (point 1936+point 1937)/2 = (1735457:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1936
  · change upperValue ((point (1937)+point ((1937)+1))/2) ≤ payment (1937)
    have hp : payment 1937 = (188183333830:ℝ)/1000000000000 := rfl
    have hx : (point 1937+point 1938)/2 = (5208425:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1937
  · change upperValue ((point (1938)+point ((1938)+1))/2) ≤ payment (1938)
    have hp : payment 1938 = (186475366950:ℝ)/1000000000000 := rfl
    have hx : (point 1938+point 1939)/2 = (5210479:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1938
  · change upperValue ((point (1939)+point ((1939)+1))/2) ≤ payment (1939)
    have hp : payment 1939 = (184767535880:ℝ)/1000000000000 := rfl
    have hx : (point 1939+point 1940)/2 = (1737511:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1939
  · change upperValue ((point (1940)+point ((1940)+1))/2) ≤ payment (1940)
    have hp : payment 1940 = (183059839349:ℝ)/1000000000000 := rfl
    have hx : (point 1940+point 1941)/2 = (5214587:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1940
  · change upperValue ((point (1941)+point ((1941)+1))/2) ≤ payment (1941)
    have hp : payment 1941 = (181352276085:ℝ)/1000000000000 := rfl
    have hx : (point 1941+point 1942)/2 = (5216641:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1941
  · change upperValue ((point (1942)+point ((1942)+1))/2) ≤ payment (1942)
    have hp : payment 1942 = (179644844816:ℝ)/1000000000000 := rfl
    have hx : (point 1942+point 1943)/2 = (1739565:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1942
  · change upperValue ((point (1943)+point ((1943)+1))/2) ≤ payment (1943)
    have hp : payment 1943 = (177937544274:ℝ)/1000000000000 := rfl
    have hx : (point 1943+point 1944)/2 = (5220749:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1943
  · change upperValue ((point (1944)+point ((1944)+1))/2) ≤ payment (1944)
    have hp : payment 1944 = (176230373189:ℝ)/1000000000000 := rfl
    have hx : (point 1944+point 1945)/2 = (5222803:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1944
  · change upperValue ((point (1945)+point ((1945)+1))/2) ≤ payment (1945)
    have hp : payment 1945 = (174523330291:ℝ)/1000000000000 := rfl
    have hx : (point 1945+point 1946)/2 = (1741619:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1945
  · change upperValue ((point (1946)+point ((1946)+1))/2) ≤ payment (1946)
    have hp : payment 1946 = (172816414314:ℝ)/1000000000000 := rfl
    have hx : (point 1946+point 1947)/2 = (5226911:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1946
  · change upperValue ((point (1947)+point ((1947)+1))/2) ≤ payment (1947)
    have hp : payment 1947 = (171109623989:ℝ)/1000000000000 := rfl
    have hx : (point 1947+point 1948)/2 = (5228965:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1947
  · change upperValue ((point (1948)+point ((1948)+1))/2) ≤ payment (1948)
    have hp : payment 1948 = (169402958051:ℝ)/1000000000000 := rfl
    have hx : (point 1948+point 1949)/2 = (1743673:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1948
  · change upperValue ((point (1949)+point ((1949)+1))/2) ≤ payment (1949)
    have hp : payment 1949 = (167696415232:ℝ)/1000000000000 := rfl
    have hx : (point 1949+point 1950)/2 = (5233073:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1949
  · change upperValue ((point (1950)+point ((1950)+1))/2) ≤ payment (1950)
    have hp : payment 1950 = (165989994269:ℝ)/1000000000000 := rfl
    have hx : (point 1950+point 1951)/2 = (5235127:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1950
  · change upperValue ((point (1951)+point ((1951)+1))/2) ≤ payment (1951)
    have hp : payment 1951 = (164283693895:ℝ)/1000000000000 := rfl
    have hx : (point 1951+point 1952)/2 = (1745727:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1951
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_121
