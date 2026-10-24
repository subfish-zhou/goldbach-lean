import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints197
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_197 (j : Fin 16) : upperPayment (16*197+j.val) ≤
    upperValue ((point split endpoint 4096 (16*197+j.val)+point split endpoint 4096 (16*197+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3152 ≤ upperValue ((point split endpoint 4096 3152+point split endpoint 4096 3153)/2)
    have hp : upperPayment 3152 = (141587107699:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3152+point split endpoint 4096 3153)/2 = (655436927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655436927:ℝ)/168755200)*ClassicalSixthBranch.v ((655436927:ℝ)/168755200)/ClassicalSixthBranch.r = (91006118114705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3152
  · change upperPayment 3153 ≤ upperValue ((point split endpoint 4096 3153+point split endpoint 4096 3154)/2)
    have hp : upperPayment 3153 = (141454322908:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3153+point split endpoint 4096 3154)/2 = (655462077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655462077:ℝ)/168755200)*ClassicalSixthBranch.v ((655462077:ℝ)/168755200)/ClassicalSixthBranch.r = (90986482696857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3153
  · change upperPayment 3154 ≤ upperValue ((point split endpoint 4096 3154+point split endpoint 4096 3155)/2)
    have hp : upperPayment 3154 = (141321504303:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3154+point split endpoint 4096 3155)/2 = (655487227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655487227:ℝ)/168755200)*ClassicalSixthBranch.v ((655487227:ℝ)/168755200)/ClassicalSixthBranch.r = (90966849303081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3154
  · change upperPayment 3155 ≤ upperValue ((point split endpoint 4096 3155+point split endpoint 4096 3156)/2)
    have hp : upperPayment 3155 = (141188651877:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3155+point split endpoint 4096 3156)/2 = (655512377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655512377:ℝ)/168755200)*ClassicalSixthBranch.v ((655512377:ℝ)/168755200)/ClassicalSixthBranch.r = (90947217933377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3155
  · change upperPayment 3156 ≤ upperValue ((point split endpoint 4096 3156+point split endpoint 4096 3157)/2)
    have hp : upperPayment 3156 = (141055765622:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3156+point split endpoint 4096 3157)/2 = (655537527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655537527:ℝ)/168755200)*ClassicalSixthBranch.v ((655537527:ℝ)/168755200)/ClassicalSixthBranch.r = (90927588587745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3156
  · change upperPayment 3157 ≤ upperValue ((point split endpoint 4096 3157+point split endpoint 4096 3158)/2)
    have hp : upperPayment 3157 = (140922845529:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3157+point split endpoint 4096 3158)/2 = (655562677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655562677:ℝ)/168755200)*ClassicalSixthBranch.v ((655562677:ℝ)/168755200)/ClassicalSixthBranch.r = (90907961266185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3157
  · change upperPayment 3158 ≤ upperValue ((point split endpoint 4096 3158+point split endpoint 4096 3159)/2)
    have hp : upperPayment 3158 = (140789891590:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3158+point split endpoint 4096 3159)/2 = (655587827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655587827:ℝ)/168755200)*ClassicalSixthBranch.v ((655587827:ℝ)/168755200)/ClassicalSixthBranch.r = (90888335968697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3158
  · change upperPayment 3159 ≤ upperValue ((point split endpoint 4096 3159+point split endpoint 4096 3160)/2)
    have hp : upperPayment 3159 = (140656903797:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3159+point split endpoint 4096 3160)/2 = (655612977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655612977:ℝ)/168755200)*ClassicalSixthBranch.v ((655612977:ℝ)/168755200)/ClassicalSixthBranch.r = (90868712695281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3159
  · change upperPayment 3160 ≤ upperValue ((point split endpoint 4096 3160+point split endpoint 4096 3161)/2)
    have hp : upperPayment 3160 = (140523882142:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3160+point split endpoint 4096 3161)/2 = (655638127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655638127:ℝ)/168755200)*ClassicalSixthBranch.v ((655638127:ℝ)/168755200)/ClassicalSixthBranch.r = (90849091445937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3160
  · change upperPayment 3161 ≤ upperValue ((point split endpoint 4096 3161+point split endpoint 4096 3162)/2)
    have hp : upperPayment 3161 = (140390826615:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3161+point split endpoint 4096 3162)/2 = (655663277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655663277:ℝ)/168755200)*ClassicalSixthBranch.v ((655663277:ℝ)/168755200)/ClassicalSixthBranch.r = (90829472220665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3161
  · change upperPayment 3162 ≤ upperValue ((point split endpoint 4096 3162+point split endpoint 4096 3163)/2)
    have hp : upperPayment 3162 = (140257737210:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3162+point split endpoint 4096 3163)/2 = (655688427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655688427:ℝ)/168755200)*ClassicalSixthBranch.v ((655688427:ℝ)/168755200)/ClassicalSixthBranch.r = (90809855019465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3162
  · change upperPayment 3163 ≤ upperValue ((point split endpoint 4096 3163+point split endpoint 4096 3164)/2)
    have hp : upperPayment 3163 = (140124613917:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3163+point split endpoint 4096 3164)/2 = (655713577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655713577:ℝ)/168755200)*ClassicalSixthBranch.v ((655713577:ℝ)/168755200)/ClassicalSixthBranch.r = (90790239842337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3163
  · change upperPayment 3164 ≤ upperValue ((point split endpoint 4096 3164+point split endpoint 4096 3165)/2)
    have hp : upperPayment 3164 = (139991456729:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3164+point split endpoint 4096 3165)/2 = (655738727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655738727:ℝ)/168755200)*ClassicalSixthBranch.v ((655738727:ℝ)/168755200)/ClassicalSixthBranch.r = (90770626689281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3164
  · change upperPayment 3165 ≤ upperValue ((point split endpoint 4096 3165+point split endpoint 4096 3166)/2)
    have hp : upperPayment 3165 = (139858265637:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3165+point split endpoint 4096 3166)/2 = (655763877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655763877:ℝ)/168755200)*ClassicalSixthBranch.v ((655763877:ℝ)/168755200)/ClassicalSixthBranch.r = (90751015560297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3165
  · change upperPayment 3166 ≤ upperValue ((point split endpoint 4096 3166+point split endpoint 4096 3167)/2)
    have hp : upperPayment 3166 = (139725040633:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3166+point split endpoint 4096 3167)/2 = (655789027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655789027:ℝ)/168755200)*ClassicalSixthBranch.v ((655789027:ℝ)/168755200)/ClassicalSixthBranch.r = (90731406455385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3166
  · change upperPayment 3167 ≤ upperValue ((point split endpoint 4096 3167+point split endpoint 4096 3168)/2)
    have hp : upperPayment 3167 = (139591781708:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3167+point split endpoint 4096 3168)/2 = (655814177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655814177:ℝ)/168755200)*ClassicalSixthBranch.v ((655814177:ℝ)/168755200)/ClassicalSixthBranch.r = (90711799374545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3167
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_197
