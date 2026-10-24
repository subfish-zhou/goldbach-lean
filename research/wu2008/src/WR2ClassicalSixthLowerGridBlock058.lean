import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints058
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_058 (j : Fin 16) : lowerPayment (16*58+j.val) ≤
    lowerValue ((point 2 split 4096 (16*58+j.val)+point 2 split 4096 (16*58+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 928 ≤ lowerValue ((point 2 split 4096 928+point 2 split 4096 929)/2)
    have hp : lowerPayment 928 = (125315345740:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 928+point 2 split 4096 929)/2 = (391606667:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((391606667:ℝ)/168755200)/ClassicalSixthBranch.v ((391606667:ℝ)/168755200) = (148445886079:ℝ)/75200627128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_928
  · change lowerPayment 929 ≤ lowerValue ((point 2 split 4096 929+point 2 split 4096 930)/2)
    have hp : lowerPayment 929 = (125428871694:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 929+point 2 split 4096 930)/2 = (391664929:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((391664929:ℝ)/168755200)/ClassicalSixthBranch.v ((391664929:ℝ)/168755200) = (742152116721:ℝ)/375955127752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_929
  · change lowerPayment 930 ≤ lowerValue ((point 2 split 4096 930+point 2 split 4096 931)/2)
    have hp : lowerPayment 930 = (125542363399:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 930+point 2 split 4096 931)/2 = (391723191:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((391723191:ℝ)/168755200)/ClassicalSixthBranch.v ((391723191:ℝ)/168755200) = (742074803047:ℝ)/375907119864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_930
  · change lowerPayment 931 ≤ lowerValue ((point 2 split 4096 931+point 2 split 4096 932)/2)
    have hp : lowerPayment 931 = (125655820885:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 931+point 2 split 4096 932)/2 = (391781453:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((391781453:ℝ)/168755200)/ClassicalSixthBranch.v ((391781453:ℝ)/168755200) = (741997489373:ℝ)/375859111976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_931
  · change lowerPayment 932 ≤ lowerValue ((point 2 split 4096 932+point 2 split 4096 933)/2)
    have hp : lowerPayment 932 = (125769244185:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 932+point 2 split 4096 933)/2 = (78367943:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((78367943:ℝ)/33751040)/ClassicalSixthBranch.v ((78367943:ℝ)/33751040) = (741920175699:ℝ)/375811104088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_932
  · change lowerPayment 933 ≤ lowerValue ((point 2 split 4096 933+point 2 split 4096 934)/2)
    have hp : lowerPayment 933 = (125882633328:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 933+point 2 split 4096 934)/2 = (391897977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((391897977:ℝ)/168755200)/ClassicalSixthBranch.v ((391897977:ℝ)/168755200) = (29673714481:ℝ)/15030523848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_933
  · change lowerPayment 934 ≤ lowerValue ((point 2 split 4096 934+point 2 split 4096 935)/2)
    have hp : lowerPayment 934 = (125995988346:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 934+point 2 split 4096 935)/2 = (391956239:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((391956239:ℝ)/168755200)/ClassicalSixthBranch.v ((391956239:ℝ)/168755200) = (741765548351:ℝ)/375715088312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_934
  · change lowerPayment 935 ≤ lowerValue ((point 2 split 4096 935+point 2 split 4096 936)/2)
    have hp : lowerPayment 935 = (126109309271:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 935+point 2 split 4096 936)/2 = (392014501:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((392014501:ℝ)/168755200)/ClassicalSixthBranch.v ((392014501:ℝ)/168755200) = (741688234677:ℝ)/375667080424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_935
  · change lowerPayment 936 ≤ lowerValue ((point 2 split 4096 936+point 2 split 4096 937)/2)
    have hp : lowerPayment 936 = (126222596133:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 936+point 2 split 4096 937)/2 = (392072763:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((392072763:ℝ)/168755200)/ClassicalSixthBranch.v ((392072763:ℝ)/168755200) = (741610921003:ℝ)/375619072536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_936
  · change lowerPayment 937 ≤ lowerValue ((point 2 split 4096 937+point 2 split 4096 938)/2)
    have hp : lowerPayment 937 = (126335848964:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 937+point 2 split 4096 938)/2 = (15685241:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((15685241:ℝ)/6750208)/ClassicalSixthBranch.v ((15685241:ℝ)/6750208) = (741533607329:ℝ)/375571064648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_937
  · change lowerPayment 938 ≤ lowerValue ((point 2 split 4096 938+point 2 split 4096 939)/2)
    have hp : lowerPayment 938 = (126449067794:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 938+point 2 split 4096 939)/2 = (392189287:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((392189287:ℝ)/168755200)/ClassicalSixthBranch.v ((392189287:ℝ)/168755200) = (148291258731:ℝ)/75104611352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_938
  · change lowerPayment 939 ≤ lowerValue ((point 2 split 4096 939+point 2 split 4096 940)/2)
    have hp : lowerPayment 939 = (126562252656:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 939+point 2 split 4096 940)/2 = (392247549:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((392247549:ℝ)/168755200)/ClassicalSixthBranch.v ((392247549:ℝ)/168755200) = (741378979981:ℝ)/375475048872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_939
  · change lowerPayment 940 ≤ lowerValue ((point 2 split 4096 940+point 2 split 4096 941)/2)
    have hp : lowerPayment 940 = (126675403578:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 940+point 2 split 4096 941)/2 = (392305811:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((392305811:ℝ)/168755200)/ClassicalSixthBranch.v ((392305811:ℝ)/168755200) = (741301666307:ℝ)/375427040984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_940
  · change lowerPayment 941 ≤ lowerValue ((point 2 split 4096 941+point 2 split 4096 942)/2)
    have hp : lowerPayment 941 = (126788520594:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 941+point 2 split 4096 942)/2 = (392364073:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((392364073:ℝ)/168755200)/ClassicalSixthBranch.v ((392364073:ℝ)/168755200) = (741224352633:ℝ)/375379033096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_941
  · change lowerPayment 942 ≤ lowerValue ((point 2 split 4096 942+point 2 split 4096 943)/2)
    have hp : lowerPayment 942 = (126901603733:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 942+point 2 split 4096 943)/2 = (78484467:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((78484467:ℝ)/33751040)/ClassicalSixthBranch.v ((78484467:ℝ)/33751040) = (741147038959:ℝ)/375331025208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_942
  · change lowerPayment 943 ≤ lowerValue ((point 2 split 4096 943+point 2 split 4096 944)/2)
    have hp : lowerPayment 943 = (127014653027:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 943+point 2 split 4096 944)/2 = (392480597:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((392480597:ℝ)/168755200)/ClassicalSixthBranch.v ((392480597:ℝ)/168755200) = (148213945057:ℝ)/75056603464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_943
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_058
