import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints133
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_133 (j : Fin 16) : upperPayment (16*133+j.val) ≤
    upperValue ((point split endpoint 4096 (16*133+j.val)+point split endpoint 4096 (16*133+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2128 ≤ upperValue ((point split endpoint 4096 2128+point split endpoint 4096 2129)/2)
    have hp : upperPayment 2128 = (261150424598:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2128+point split endpoint 4096 2129)/2 = (629683327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629683327:ℝ)/168755200)*ClassicalSixthBranch.v ((629683327:ℝ)/168755200)/ClassicalSixthBranch.r = (112175018976657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2128
  · change upperPayment 2129 ≤ upperValue ((point split endpoint 4096 2129+point split endpoint 4096 2130)/2)
    have hp : upperPayment 2129 = (261048482068:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2129+point split endpoint 4096 2130)/2 = (629708477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629708477:ℝ)/168755200)*ClassicalSixthBranch.v ((629708477:ℝ)/168755200)/ClassicalSixthBranch.r = (112153310909081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2129
  · change upperPayment 2130 ≤ upperValue ((point split endpoint 4096 2130+point split endpoint 4096 2131)/2)
    have hp : upperPayment 2130 = (260946512631:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2130+point split endpoint 4096 2131)/2 = (629733627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629733627:ℝ)/168755200)*ClassicalSixthBranch.v ((629733627:ℝ)/168755200)/ClassicalSixthBranch.r = (112131604865577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2130
  · change upperPayment 2131 ≤ upperValue ((point split endpoint 4096 2131+point split endpoint 4096 2132)/2)
    have hp : upperPayment 2131 = (260844516284:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2131+point split endpoint 4096 2132)/2 = (629758777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629758777:ℝ)/168755200)*ClassicalSixthBranch.v ((629758777:ℝ)/168755200)/ClassicalSixthBranch.r = (112109900846145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2131
  · change upperPayment 2132 ≤ upperValue ((point split endpoint 4096 2132+point split endpoint 4096 2133)/2)
    have hp : upperPayment 2132 = (260742493019:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2132+point split endpoint 4096 2133)/2 = (629783927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629783927:ℝ)/168755200)*ClassicalSixthBranch.v ((629783927:ℝ)/168755200)/ClassicalSixthBranch.r = (112088198850785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2132
  · change upperPayment 2133 ≤ upperValue ((point split endpoint 4096 2133+point split endpoint 4096 2134)/2)
    have hp : upperPayment 2133 = (260640442832:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2133+point split endpoint 4096 2134)/2 = (629809077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629809077:ℝ)/168755200)*ClassicalSixthBranch.v ((629809077:ℝ)/168755200)/ClassicalSixthBranch.r = (112066498879497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2133
  · change upperPayment 2134 ≤ upperValue ((point split endpoint 4096 2134+point split endpoint 4096 2135)/2)
    have hp : upperPayment 2134 = (260538365718:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2134+point split endpoint 4096 2135)/2 = (629834227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629834227:ℝ)/168755200)*ClassicalSixthBranch.v ((629834227:ℝ)/168755200)/ClassicalSixthBranch.r = (112044800932281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2134
  · change upperPayment 2135 ≤ upperValue ((point split endpoint 4096 2135+point split endpoint 4096 2136)/2)
    have hp : upperPayment 2135 = (260436261670:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2135+point split endpoint 4096 2136)/2 = (629859377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629859377:ℝ)/168755200)*ClassicalSixthBranch.v ((629859377:ℝ)/168755200)/ClassicalSixthBranch.r = (112023105009137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2135
  · change upperPayment 2136 ≤ upperValue ((point split endpoint 4096 2136+point split endpoint 4096 2137)/2)
    have hp : upperPayment 2136 = (260334130683:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2136+point split endpoint 4096 2137)/2 = (629884527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629884527:ℝ)/168755200)*ClassicalSixthBranch.v ((629884527:ℝ)/168755200)/ClassicalSixthBranch.r = (112001411110065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2136
  · change upperPayment 2137 ≤ upperValue ((point split endpoint 4096 2137+point split endpoint 4096 2138)/2)
    have hp : upperPayment 2137 = (260231972752:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2137+point split endpoint 4096 2138)/2 = (629909677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629909677:ℝ)/168755200)*ClassicalSixthBranch.v ((629909677:ℝ)/168755200)/ClassicalSixthBranch.r = (111979719235065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2137
  · change upperPayment 2138 ≤ upperValue ((point split endpoint 4096 2138+point split endpoint 4096 2139)/2)
    have hp : upperPayment 2138 = (260129787871:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2138+point split endpoint 4096 2139)/2 = (629934827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629934827:ℝ)/168755200)*ClassicalSixthBranch.v ((629934827:ℝ)/168755200)/ClassicalSixthBranch.r = (111958029384137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2138
  · change upperPayment 2139 ≤ upperValue ((point split endpoint 4096 2139+point split endpoint 4096 2140)/2)
    have hp : upperPayment 2139 = (260027576035:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2139+point split endpoint 4096 2140)/2 = (629959977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629959977:ℝ)/168755200)*ClassicalSixthBranch.v ((629959977:ℝ)/168755200)/ClassicalSixthBranch.r = (111936341557281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2139
  · change upperPayment 2140 ≤ upperValue ((point split endpoint 4096 2140+point split endpoint 4096 2141)/2)
    have hp : upperPayment 2140 = (259925337239:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2140+point split endpoint 4096 2141)/2 = (629985127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629985127:ℝ)/168755200)*ClassicalSixthBranch.v ((629985127:ℝ)/168755200)/ClassicalSixthBranch.r = (111914655754497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2140
  · change upperPayment 2141 ≤ upperValue ((point split endpoint 4096 2141+point split endpoint 4096 2142)/2)
    have hp : upperPayment 2141 = (259823071477:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2141+point split endpoint 4096 2142)/2 = (630010277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630010277:ℝ)/168755200)*ClassicalSixthBranch.v ((630010277:ℝ)/168755200)/ClassicalSixthBranch.r = (111892971975785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2141
  · change upperPayment 2142 ≤ upperValue ((point split endpoint 4096 2142+point split endpoint 4096 2143)/2)
    have hp : upperPayment 2142 = (259720778742:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2142+point split endpoint 4096 2143)/2 = (630035427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630035427:ℝ)/168755200)*ClassicalSixthBranch.v ((630035427:ℝ)/168755200)/ClassicalSixthBranch.r = (111871290221145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2142
  · change upperPayment 2143 ≤ upperValue ((point split endpoint 4096 2143+point split endpoint 4096 2144)/2)
    have hp : upperPayment 2143 = (259618459031:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2143+point split endpoint 4096 2144)/2 = (630060577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630060577:ℝ)/168755200)*ClassicalSixthBranch.v ((630060577:ℝ)/168755200)/ClassicalSixthBranch.r = (111849610490577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2143
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_133
