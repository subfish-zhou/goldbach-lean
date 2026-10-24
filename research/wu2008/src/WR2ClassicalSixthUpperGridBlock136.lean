import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints136
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_136 (j : Fin 16) : upperPayment (16*136+j.val) ≤
    upperValue ((point split endpoint 4096 (16*136+j.val)+point split endpoint 4096 (16*136+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2176 ≤ upperValue ((point split endpoint 4096 2176+point split endpoint 4096 2177)/2)
    have hp : upperPayment 2176 = (256226738454:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2176+point split endpoint 4096 2177)/2 = (630890527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630890527:ℝ)/168755200)*ClassicalSixthBranch.v ((630890527:ℝ)/168755200)/ClassicalSixthBranch.r = (111135314886225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2176
  · change upperPayment 2177 ≤ upperValue ((point split endpoint 4096 2177+point split endpoint 4096 2178)/2)
    have hp : upperPayment 2177 = (256123498247:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2177+point split endpoint 4096 2178)/2 = (630915677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630915677:ℝ)/168755200)*ClassicalSixthBranch.v ((630915677:ℝ)/168755200)/ClassicalSixthBranch.r = (111113703974105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2177
  · change upperPayment 2178 ≤ upperValue ((point split endpoint 4096 2178+point split endpoint 4096 2179)/2)
    have hp : upperPayment 2178 = (256020230871:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2178+point split endpoint 4096 2179)/2 = (630940827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630940827:ℝ)/168755200)*ClassicalSixthBranch.v ((630940827:ℝ)/168755200)/ClassicalSixthBranch.r = (111092095086057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2178
  · change upperPayment 2179 ≤ upperValue ((point split endpoint 4096 2179+point split endpoint 4096 2180)/2)
    have hp : upperPayment 2179 = (255916936318:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2179+point split endpoint 4096 2180)/2 = (630965977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630965977:ℝ)/168755200)*ClassicalSixthBranch.v ((630965977:ℝ)/168755200)/ClassicalSixthBranch.r = (111070488222081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2179
  · change upperPayment 2180 ≤ upperValue ((point split endpoint 4096 2180+point split endpoint 4096 2181)/2)
    have hp : upperPayment 2180 = (255813614585:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2180+point split endpoint 4096 2181)/2 = (630991127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630991127:ℝ)/168755200)*ClassicalSixthBranch.v ((630991127:ℝ)/168755200)/ClassicalSixthBranch.r = (111048883382177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2180
  · change upperPayment 2181 ≤ upperValue ((point split endpoint 4096 2181+point split endpoint 4096 2182)/2)
    have hp : upperPayment 2181 = (255710265664:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2181+point split endpoint 4096 2182)/2 = (631016277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631016277:ℝ)/168755200)*ClassicalSixthBranch.v ((631016277:ℝ)/168755200)/ClassicalSixthBranch.r = (111027280566345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2181
  · change upperPayment 2182 ≤ upperValue ((point split endpoint 4096 2182+point split endpoint 4096 2183)/2)
    have hp : upperPayment 2182 = (255606889551:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2182+point split endpoint 4096 2183)/2 = (631041427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631041427:ℝ)/168755200)*ClassicalSixthBranch.v ((631041427:ℝ)/168755200)/ClassicalSixthBranch.r = (111005679774585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2182
  · change upperPayment 2183 ≤ upperValue ((point split endpoint 4096 2183+point split endpoint 4096 2184)/2)
    have hp : upperPayment 2183 = (255503486240:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2183+point split endpoint 4096 2184)/2 = (631066577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631066577:ℝ)/168755200)*ClassicalSixthBranch.v ((631066577:ℝ)/168755200)/ClassicalSixthBranch.r = (110984081006897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2183
  · change upperPayment 2184 ≤ upperValue ((point split endpoint 4096 2184+point split endpoint 4096 2185)/2)
    have hp : upperPayment 2184 = (255400055726:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2184+point split endpoint 4096 2185)/2 = (631091727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631091727:ℝ)/168755200)*ClassicalSixthBranch.v ((631091727:ℝ)/168755200)/ClassicalSixthBranch.r = (110962484263281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2184
  · change upperPayment 2185 ≤ upperValue ((point split endpoint 4096 2185+point split endpoint 4096 2186)/2)
    have hp : upperPayment 2185 = (255296598002:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2185+point split endpoint 4096 2186)/2 = (631116877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631116877:ℝ)/168755200)*ClassicalSixthBranch.v ((631116877:ℝ)/168755200)/ClassicalSixthBranch.r = (110940889543737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2185
  · change upperPayment 2186 ≤ upperValue ((point split endpoint 4096 2186+point split endpoint 4096 2187)/2)
    have hp : upperPayment 2186 = (255193113064:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2186+point split endpoint 4096 2187)/2 = (631142027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631142027:ℝ)/168755200)*ClassicalSixthBranch.v ((631142027:ℝ)/168755200)/ClassicalSixthBranch.r = (110919296848265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2186
  · change upperPayment 2187 ≤ upperValue ((point split endpoint 4096 2187+point split endpoint 4096 2188)/2)
    have hp : upperPayment 2187 = (255089600905:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2187+point split endpoint 4096 2188)/2 = (631167177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631167177:ℝ)/168755200)*ClassicalSixthBranch.v ((631167177:ℝ)/168755200)/ClassicalSixthBranch.r = (110897706176865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2187
  · change upperPayment 2188 ≤ upperValue ((point split endpoint 4096 2188+point split endpoint 4096 2189)/2)
    have hp : upperPayment 2188 = (254986061520:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2188+point split endpoint 4096 2189)/2 = (631192327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631192327:ℝ)/168755200)*ClassicalSixthBranch.v ((631192327:ℝ)/168755200)/ClassicalSixthBranch.r = (110876117529537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2188
  · change upperPayment 2189 ≤ upperValue ((point split endpoint 4096 2189+point split endpoint 4096 2190)/2)
    have hp : upperPayment 2189 = (254882494904:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2189+point split endpoint 4096 2190)/2 = (631217477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631217477:ℝ)/168755200)*ClassicalSixthBranch.v ((631217477:ℝ)/168755200)/ClassicalSixthBranch.r = (110854530906281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2189
  · change upperPayment 2190 ≤ upperValue ((point split endpoint 4096 2190+point split endpoint 4096 2191)/2)
    have hp : upperPayment 2190 = (254778901051:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2190+point split endpoint 4096 2191)/2 = (631242627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631242627:ℝ)/168755200)*ClassicalSixthBranch.v ((631242627:ℝ)/168755200)/ClassicalSixthBranch.r = (1076048022399:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2190
  · change upperPayment 2191 ≤ upperValue ((point split endpoint 4096 2191+point split endpoint 4096 2192)/2)
    have hp : upperPayment 2191 = (254675279955:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2191+point split endpoint 4096 2192)/2 = (631267777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631267777:ℝ)/168755200)*ClassicalSixthBranch.v ((631267777:ℝ)/168755200)/ClassicalSixthBranch.r = (110811363731985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2191
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_136
