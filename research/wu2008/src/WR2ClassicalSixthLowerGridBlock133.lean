import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints133
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_133 (j : Fin 16) : lowerPayment (16*133+j.val) ≤
    lowerValue ((point 2 split 4096 (16*133+j.val)+point 2 split 4096 (16*133+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2128 ≤ lowerValue ((point 2 split 4096 2128+point 2 split 4096 2129)/2)
    have hp : lowerPayment 2128 = (244292888388:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2128+point 2 split 4096 2129)/2 = (461521067:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((461521067:ℝ)/168755200)/ClassicalSixthBranch.v ((461521067:ℝ)/168755200) = (129890604319:ℝ)/63678734008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2128
  · change lowerPayment 2129 ≤ lowerValue ((point 2 split 4096 2129+point 2 split 4096 2130)/2)
    have hp : lowerPayment 2129 = (244382790353:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2129+point 2 split 4096 2130)/2 = (461579329:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((461579329:ℝ)/168755200)/ClassicalSixthBranch.v ((461579329:ℝ)/168755200) = (649375707921:ℝ)/318345662152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2129
  · change lowerPayment 2130 ≤ lowerValue ((point 2 split 4096 2130+point 2 split 4096 2131)/2)
    have hp : lowerPayment 2130 = (244472684242:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2130+point 2 split 4096 2131)/2 = (461637591:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((461637591:ℝ)/168755200)/ClassicalSixthBranch.v ((461637591:ℝ)/168755200) = (649298394247:ℝ)/318297654264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2130
  · change lowerPayment 2131 ≤ lowerValue ((point 2 split 4096 2131+point 2 split 4096 2132)/2)
    have hp : lowerPayment 2131 = (244562570073:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2131+point 2 split 4096 2132)/2 = (461695853:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((461695853:ℝ)/168755200)/ClassicalSixthBranch.v ((461695853:ℝ)/168755200) = (649221080573:ℝ)/318249646376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2131
  · change lowerPayment 2132 ≤ lowerValue ((point 2 split 4096 2132+point 2 split 4096 2133)/2)
    have hp : lowerPayment 2132 = (244652447860:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2132+point 2 split 4096 2133)/2 = (92350823:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((92350823:ℝ)/33751040)/ClassicalSixthBranch.v ((92350823:ℝ)/33751040) = (649143766899:ℝ)/318201638488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2132
  · change lowerPayment 2133 ≤ lowerValue ((point 2 split 4096 2133+point 2 split 4096 2134)/2)
    have hp : lowerPayment 2133 = (244742317621:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2133+point 2 split 4096 2134)/2 = (461812377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((461812377:ℝ)/168755200)/ClassicalSixthBranch.v ((461812377:ℝ)/168755200) = (25962658129:ℝ)/12726145224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2133
  · change lowerPayment 2134 ≤ lowerValue ((point 2 split 4096 2134+point 2 split 4096 2135)/2)
    have hp : lowerPayment 2134 = (244832179370:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2134+point 2 split 4096 2135)/2 = (461870639:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((461870639:ℝ)/168755200)/ClassicalSixthBranch.v ((461870639:ℝ)/168755200) = (648989139551:ℝ)/318105622712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2134
  · change lowerPayment 2135 ≤ lowerValue ((point 2 split 4096 2135+point 2 split 4096 2136)/2)
    have hp : lowerPayment 2135 = (244922033125:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2135+point 2 split 4096 2136)/2 = (461928901:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((461928901:ℝ)/168755200)/ClassicalSixthBranch.v ((461928901:ℝ)/168755200) = (648911825877:ℝ)/318057614824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2135
  · change lowerPayment 2136 ≤ lowerValue ((point 2 split 4096 2136+point 2 split 4096 2137)/2)
    have hp : lowerPayment 2136 = (245011878899:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2136+point 2 split 4096 2137)/2 = (461987163:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((461987163:ℝ)/168755200)/ClassicalSixthBranch.v ((461987163:ℝ)/168755200) = (648834512203:ℝ)/318009606936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2136
  · change lowerPayment 2137 ≤ lowerValue ((point 2 split 4096 2137+point 2 split 4096 2138)/2)
    have hp : lowerPayment 2137 = (245101716711:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2137+point 2 split 4096 2138)/2 = (18481817:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((18481817:ℝ)/6750208)/ClassicalSixthBranch.v ((18481817:ℝ)/6750208) = (648757198529:ℝ)/317961599048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2137
  · change lowerPayment 2138 ≤ lowerValue ((point 2 split 4096 2138+point 2 split 4096 2139)/2)
    have hp : lowerPayment 2138 = (245191546575:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2138+point 2 split 4096 2139)/2 = (462103687:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((462103687:ℝ)/168755200)/ClassicalSixthBranch.v ((462103687:ℝ)/168755200) = (129735976971:ℝ)/63582718232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2138
  · change lowerPayment 2139 ≤ lowerValue ((point 2 split 4096 2139+point 2 split 4096 2140)/2)
    have hp : lowerPayment 2139 = (245281368507:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2139+point 2 split 4096 2140)/2 = (462161949:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((462161949:ℝ)/168755200)/ClassicalSixthBranch.v ((462161949:ℝ)/168755200) = (648602571181:ℝ)/317865583272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2139
  · change lowerPayment 2140 ≤ lowerValue ((point 2 split 4096 2140+point 2 split 4096 2141)/2)
    have hp : lowerPayment 2140 = (245371182524:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2140+point 2 split 4096 2141)/2 = (462220211:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((462220211:ℝ)/168755200)/ClassicalSixthBranch.v ((462220211:ℝ)/168755200) = (648525257507:ℝ)/317817575384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2140
  · change lowerPayment 2141 ≤ lowerValue ((point 2 split 4096 2141+point 2 split 4096 2142)/2)
    have hp : lowerPayment 2141 = (245460988641:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2141+point 2 split 4096 2142)/2 = (462278473:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((462278473:ℝ)/168755200)/ClassicalSixthBranch.v ((462278473:ℝ)/168755200) = (648447943833:ℝ)/317769567496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2141
  · change lowerPayment 2142 ≤ lowerValue ((point 2 split 4096 2142+point 2 split 4096 2143)/2)
    have hp : lowerPayment 2142 = (245550786875:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2142+point 2 split 4096 2143)/2 = (92467347:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((92467347:ℝ)/33751040)/ClassicalSixthBranch.v ((92467347:ℝ)/33751040) = (648370630159:ℝ)/317721559608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2142
  · change lowerPayment 2143 ≤ lowerValue ((point 2 split 4096 2143+point 2 split 4096 2144)/2)
    have hp : lowerPayment 2143 = (245640577240:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2143+point 2 split 4096 2144)/2 = (462394997:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((462394997:ℝ)/168755200)/ClassicalSixthBranch.v ((462394997:ℝ)/168755200) = (129658663297:ℝ)/63534710344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2143
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_133
