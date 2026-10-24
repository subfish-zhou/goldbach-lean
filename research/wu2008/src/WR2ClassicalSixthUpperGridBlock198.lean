import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints198
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_198 (j : Fin 16) : upperPayment (16*198+j.val) ≤
    upperValue ((point split endpoint 4096 (16*198+j.val)+point split endpoint 4096 (16*198+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3168 ≤ upperValue ((point split endpoint 4096 3168+point split endpoint 4096 3169)/2)
    have hp : upperPayment 3168 = (139458488855:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3168+point split endpoint 4096 3169)/2 = (655839327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655839327:ℝ)/168755200)*ClassicalSixthBranch.v ((655839327:ℝ)/168755200)/ClassicalSixthBranch.r = (90692194317777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3168
  · change upperPayment 3169 ≤ upperValue ((point split endpoint 4096 3169+point split endpoint 4096 3170)/2)
    have hp : upperPayment 3169 = (139325162065:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3169+point split endpoint 4096 3170)/2 = (655864477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655864477:ℝ)/168755200)*ClassicalSixthBranch.v ((655864477:ℝ)/168755200)/ClassicalSixthBranch.r = (90672591285081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3169
  · change upperPayment 3170 ≤ upperValue ((point split endpoint 4096 3170+point split endpoint 4096 3171)/2)
    have hp : upperPayment 3170 = (139191801329:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3170+point split endpoint 4096 3171)/2 = (655889627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655889627:ℝ)/168755200)*ClassicalSixthBranch.v ((655889627:ℝ)/168755200)/ClassicalSixthBranch.r = (90652990276457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3170
  · change upperPayment 3171 ≤ upperValue ((point split endpoint 4096 3171+point split endpoint 4096 3172)/2)
    have hp : upperPayment 3171 = (139058406641:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3171+point split endpoint 4096 3172)/2 = (655914777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655914777:ℝ)/168755200)*ClassicalSixthBranch.v ((655914777:ℝ)/168755200)/ClassicalSixthBranch.r = (90633391291905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3171
  · change upperPayment 3172 ≤ upperValue ((point split endpoint 4096 3172+point split endpoint 4096 3173)/2)
    have hp : upperPayment 3172 = (138924977990:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3172+point split endpoint 4096 3173)/2 = (655939927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655939927:ℝ)/168755200)*ClassicalSixthBranch.v ((655939927:ℝ)/168755200)/ClassicalSixthBranch.r = (90613794331425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3172
  · change upperPayment 3173 ≤ upperValue ((point split endpoint 4096 3173+point split endpoint 4096 3174)/2)
    have hp : upperPayment 3173 = (138791515369:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3173+point split endpoint 4096 3174)/2 = (655965077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655965077:ℝ)/168755200)*ClassicalSixthBranch.v ((655965077:ℝ)/168755200)/ClassicalSixthBranch.r = (90594199395017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3173
  · change upperPayment 3174 ≤ upperValue ((point split endpoint 4096 3174+point split endpoint 4096 3175)/2)
    have hp : upperPayment 3174 = (138658018770:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3174+point split endpoint 4096 3175)/2 = (655990227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655990227:ℝ)/168755200)*ClassicalSixthBranch.v ((655990227:ℝ)/168755200)/ClassicalSixthBranch.r = (90574606482681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3174
  · change upperPayment 3175 ≤ upperValue ((point split endpoint 4096 3175+point split endpoint 4096 3176)/2)
    have hp : upperPayment 3175 = (138524488184:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3175+point split endpoint 4096 3176)/2 = (656015377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656015377:ℝ)/168755200)*ClassicalSixthBranch.v ((656015377:ℝ)/168755200)/ClassicalSixthBranch.r = (90555015594417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3175
  · change upperPayment 3176 ≤ upperValue ((point split endpoint 4096 3176+point split endpoint 4096 3177)/2)
    have hp : upperPayment 3176 = (138390923603:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3176+point split endpoint 4096 3177)/2 = (656040527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656040527:ℝ)/168755200)*ClassicalSixthBranch.v ((656040527:ℝ)/168755200)/ClassicalSixthBranch.r = (90535426730225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3176
  · change upperPayment 3177 ≤ upperValue ((point split endpoint 4096 3177+point split endpoint 4096 3178)/2)
    have hp : upperPayment 3177 = (138257325018:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3177+point split endpoint 4096 3178)/2 = (656065677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656065677:ℝ)/168755200)*ClassicalSixthBranch.v ((656065677:ℝ)/168755200)/ClassicalSixthBranch.r = (90515839890105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3177
  · change upperPayment 3178 ≤ upperValue ((point split endpoint 4096 3178+point split endpoint 4096 3179)/2)
    have hp : upperPayment 3178 = (138123692422:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3178+point split endpoint 4096 3179)/2 = (656090827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656090827:ℝ)/168755200)*ClassicalSixthBranch.v ((656090827:ℝ)/168755200)/ClassicalSixthBranch.r = (90496255074057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3178
  · change upperPayment 3179 ≤ upperValue ((point split endpoint 4096 3179+point split endpoint 4096 3180)/2)
    have hp : upperPayment 3179 = (137990025806:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3179+point split endpoint 4096 3180)/2 = (656115977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656115977:ℝ)/168755200)*ClassicalSixthBranch.v ((656115977:ℝ)/168755200)/ClassicalSixthBranch.r = (90476672282081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3179
  · change upperPayment 3180 ≤ upperValue ((point split endpoint 4096 3180+point split endpoint 4096 3181)/2)
    have hp : upperPayment 3180 = (137856325161:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3180+point split endpoint 4096 3181)/2 = (656141127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656141127:ℝ)/168755200)*ClassicalSixthBranch.v ((656141127:ℝ)/168755200)/ClassicalSixthBranch.r = (90457091514177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3180
  · change upperPayment 3181 ≤ upperValue ((point split endpoint 4096 3181+point split endpoint 4096 3182)/2)
    have hp : upperPayment 3181 = (137722590480:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3181+point split endpoint 4096 3182)/2 = (656166277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656166277:ℝ)/168755200)*ClassicalSixthBranch.v ((656166277:ℝ)/168755200)/ClassicalSixthBranch.r = (90437512770345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3181
  · change upperPayment 3182 ≤ upperValue ((point split endpoint 4096 3182+point split endpoint 4096 3183)/2)
    have hp : upperPayment 3182 = (137588821754:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3182+point split endpoint 4096 3183)/2 = (656191427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656191427:ℝ)/168755200)*ClassicalSixthBranch.v ((656191427:ℝ)/168755200)/ClassicalSixthBranch.r = (90417936050585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3182
  · change upperPayment 3183 ≤ upperValue ((point split endpoint 4096 3183+point split endpoint 4096 3184)/2)
    have hp : upperPayment 3183 = (137455018975:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3183+point split endpoint 4096 3184)/2 = (656216577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656216577:ℝ)/168755200)*ClassicalSixthBranch.v ((656216577:ℝ)/168755200)/ClassicalSixthBranch.r = (90398361354897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3183
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_198
