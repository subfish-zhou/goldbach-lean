import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints058
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_058 (j : Fin 16) : upperValue ((point (16*58+j.val)+point ((16*58+j.val)+1))/2) ≤ payment (16*58+j.val) := by
  fin_cases j
  · change upperValue ((point (928)+point ((928)+1))/2) ≤ payment (928)
    have hp : payment 928 = (2271309467959:ℝ)/1000000000000 := rfl
    have hx : (point 928+point 929)/2 = (1045313:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_928
  · change upperValue ((point (929)+point ((929)+1))/2) ≤ payment (929)
    have hp : payment 929 = (2268467850582:ℝ)/1000000000000 := rfl
    have hx : (point 929+point 930)/2 = (3137993:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_929
  · change upperValue ((point (930)+point ((930)+1))/2) ≤ payment (930)
    have hp : payment 930 = (2265629074536:ℝ)/1000000000000 := rfl
    have hx : (point 930+point 931)/2 = (3140047:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_930
  · change upperValue ((point (931)+point ((931)+1))/2) ≤ payment (931)
    have hp : payment 931 = (2262793133596:ℝ)/1000000000000 := rfl
    have hx : (point 931+point 932)/2 = (1047367:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_931
  · change upperValue ((point (932)+point ((932)+1))/2) ≤ payment (932)
    have hp : payment 932 = (2259960021557:ℝ)/1000000000000 := rfl
    have hx : (point 932+point 933)/2 = (3144155:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_932
  · change upperValue ((point (933)+point ((933)+1))/2) ≤ payment (933)
    have hp : payment 933 = (2257129732225:ℝ)/1000000000000 := rfl
    have hx : (point 933+point 934)/2 = (3146209:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_933
  · change upperValue ((point (934)+point ((934)+1))/2) ≤ payment (934)
    have hp : payment 934 = (2254302259424:ℝ)/1000000000000 := rfl
    have hx : (point 934+point 935)/2 = (1049421:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_934
  · change upperValue ((point (935)+point ((935)+1))/2) ≤ payment (935)
    have hp : payment 935 = (2251477596995:ℝ)/1000000000000 := rfl
    have hx : (point 935+point 936)/2 = (3150317:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_935
  · change upperValue ((point (936)+point ((936)+1))/2) ≤ payment (936)
    have hp : payment 936 = (2248655738791:ℝ)/1000000000000 := rfl
    have hx : (point 936+point 937)/2 = (3152371:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_936
  · change upperValue ((point (937)+point ((937)+1))/2) ≤ payment (937)
    have hp : payment 937 = (2245836678683:ℝ)/1000000000000 := rfl
    have hx : (point 937+point 938)/2 = (1051475:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_937
  · change upperValue ((point (938)+point ((938)+1))/2) ≤ payment (938)
    have hp : payment 938 = (2243020410556:ℝ)/1000000000000 := rfl
    have hx : (point 938+point 939)/2 = (3156479:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_938
  · change upperValue ((point (939)+point ((939)+1))/2) ≤ payment (939)
    have hp : payment 939 = (2240206928310:ℝ)/1000000000000 := rfl
    have hx : (point 939+point 940)/2 = (3158533:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_939
  · change upperValue ((point (940)+point ((940)+1))/2) ≤ payment (940)
    have hp : payment 940 = (2237396225863:ℝ)/1000000000000 := rfl
    have hx : (point 940+point 941)/2 = (1053529:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_940
  · change upperValue ((point (941)+point ((941)+1))/2) ≤ payment (941)
    have hp : payment 941 = (2234588297145:ℝ)/1000000000000 := rfl
    have hx : (point 941+point 942)/2 = (3162641:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_941
  · change upperValue ((point (942)+point ((942)+1))/2) ≤ payment (942)
    have hp : payment 942 = (2231783136102:ℝ)/1000000000000 := rfl
    have hx : (point 942+point 943)/2 = (3164695:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_942
  · change upperValue ((point (943)+point ((943)+1))/2) ≤ payment (943)
    have hp : payment 943 = (2228980736697:ℝ)/1000000000000 := rfl
    have hx : (point 943+point 944)/2 = (1055583:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_943
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_058
