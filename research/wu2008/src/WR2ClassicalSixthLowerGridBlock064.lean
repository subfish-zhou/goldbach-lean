import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints064
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_064 (j : Fin 16) : lowerPayment (16*64+j.val) ≤
    lowerValue ((point 2 split 4096 (16*64+j.val)+point 2 split 4096 (16*64+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1024 ≤ lowerValue ((point 2 split 4096 1024+point 2 split 4096 1025)/2)
    have hp : lowerPayment 1024 = (136062045290:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1024+point 2 split 4096 1025)/2 = (397199819:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((397199819:ℝ)/168755200)/ClassicalSixthBranch.v ((397199819:ℝ)/168755200) = (734807317691:ℝ)/371394378392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1024
  · change lowerPayment 1025 ≤ lowerValue ((point 2 split 4096 1025+point 2 split 4096 1026)/2)
    have hp : lowerPayment 1025 = (136172422424:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1025+point 2 split 4096 1026)/2 = (397258081:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((397258081:ℝ)/168755200)/ClassicalSixthBranch.v ((397258081:ℝ)/168755200) = (734730004017:ℝ)/371346370504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1025
  · change lowerPayment 1026 ≤ lowerValue ((point 2 split 4096 1026+point 2 split 4096 1027)/2)
    have hp : lowerPayment 1026 = (136282768204:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1026+point 2 split 4096 1027)/2 = (397316343:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((397316343:ℝ)/168755200)/ClassicalSixthBranch.v ((397316343:ℝ)/168755200) = (734652690343:ℝ)/371298362616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1026
  · change lowerPayment 1027 ≤ lowerValue ((point 2 split 4096 1027+point 2 split 4096 1028)/2)
    have hp : lowerPayment 1027 = (136393082656:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1027+point 2 split 4096 1028)/2 = (79474921:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((79474921:ℝ)/33751040)/ClassicalSixthBranch.v ((79474921:ℝ)/33751040) = (734575376669:ℝ)/371250354728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1027
  · change lowerPayment 1028 ≤ lowerValue ((point 2 split 4096 1028+point 2 split 4096 1029)/2)
    have hp : lowerPayment 1028 = (136503365812:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1028+point 2 split 4096 1029)/2 = (397432867:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((397432867:ℝ)/168755200)/ClassicalSixthBranch.v ((397432867:ℝ)/168755200) = (146899612599:ℝ)/74240469368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1028
  · change lowerPayment 1029 ≤ lowerValue ((point 2 split 4096 1029+point 2 split 4096 1030)/2)
    have hp : lowerPayment 1029 = (136613617700:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1029+point 2 split 4096 1030)/2 = (397491129:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((397491129:ℝ)/168755200)/ClassicalSixthBranch.v ((397491129:ℝ)/168755200) = (734420749321:ℝ)/371154338952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1029
  · change lowerPayment 1030 ≤ lowerValue ((point 2 split 4096 1030+point 2 split 4096 1031)/2)
    have hp : lowerPayment 1030 = (136723838348:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1030+point 2 split 4096 1031)/2 = (397549391:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((397549391:ℝ)/168755200)/ClassicalSixthBranch.v ((397549391:ℝ)/168755200) = (734343435647:ℝ)/371106331064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1030
  · change lowerPayment 1031 ≤ lowerValue ((point 2 split 4096 1031+point 2 split 4096 1032)/2)
    have hp : lowerPayment 1031 = (136834027786:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1031+point 2 split 4096 1032)/2 = (397607653:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((397607653:ℝ)/168755200)/ClassicalSixthBranch.v ((397607653:ℝ)/168755200) = (734266121973:ℝ)/371058323176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1031
  · change lowerPayment 1032 ≤ lowerValue ((point 2 split 4096 1032+point 2 split 4096 1033)/2)
    have hp : lowerPayment 1032 = (136944186043:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1032+point 2 split 4096 1033)/2 = (79533183:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((79533183:ℝ)/33751040)/ClassicalSixthBranch.v ((79533183:ℝ)/33751040) = (734188808299:ℝ)/371010315288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1032
  · change lowerPayment 1033 ≤ lowerValue ((point 2 split 4096 1033+point 2 split 4096 1034)/2)
    have hp : lowerPayment 1033 = (137054313148:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1033+point 2 split 4096 1034)/2 = (397724177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((397724177:ℝ)/168755200)/ClassicalSixthBranch.v ((397724177:ℝ)/168755200) = (29364459785:ℝ)/14838492296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1033
  · change lowerPayment 1034 ≤ lowerValue ((point 2 split 4096 1034+point 2 split 4096 1035)/2)
    have hp : lowerPayment 1034 = (137164409129:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1034+point 2 split 4096 1035)/2 = (397782439:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((397782439:ℝ)/168755200)/ClassicalSixthBranch.v ((397782439:ℝ)/168755200) = (734034180951:ℝ)/370914299512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1034
  · change lowerPayment 1035 ≤ lowerValue ((point 2 split 4096 1035+point 2 split 4096 1036)/2)
    have hp : lowerPayment 1035 = (137274474016:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1035+point 2 split 4096 1036)/2 = (397840701:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((397840701:ℝ)/168755200)/ClassicalSixthBranch.v ((397840701:ℝ)/168755200) = (733956867277:ℝ)/370866291624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1035
  · change lowerPayment 1036 ≤ lowerValue ((point 2 split 4096 1036+point 2 split 4096 1037)/2)
    have hp : lowerPayment 1036 = (137384507838:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1036+point 2 split 4096 1037)/2 = (397898963:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((397898963:ℝ)/168755200)/ClassicalSixthBranch.v ((397898963:ℝ)/168755200) = (733879553603:ℝ)/370818283736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1036
  · change lowerPayment 1037 ≤ lowerValue ((point 2 split 4096 1037+point 2 split 4096 1038)/2)
    have hp : lowerPayment 1037 = (137494510622:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1037+point 2 split 4096 1038)/2 = (15918289:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((15918289:ℝ)/6750208)/ClassicalSixthBranch.v ((15918289:ℝ)/6750208) = (733802239929:ℝ)/370770275848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1037
  · change lowerPayment 1038 ≤ lowerValue ((point 2 split 4096 1038+point 2 split 4096 1039)/2)
    have hp : lowerPayment 1038 = (137604482399:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1038+point 2 split 4096 1039)/2 = (398015487:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((398015487:ℝ)/168755200)/ClassicalSixthBranch.v ((398015487:ℝ)/168755200) = (146744985251:ℝ)/74144453592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1038
  · change lowerPayment 1039 ≤ lowerValue ((point 2 split 4096 1039+point 2 split 4096 1040)/2)
    have hp : lowerPayment 1039 = (137714423197:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1039+point 2 split 4096 1040)/2 = (398073749:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((398073749:ℝ)/168755200)/ClassicalSixthBranch.v ((398073749:ℝ)/168755200) = (733647612581:ℝ)/370674260072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1039
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_064
