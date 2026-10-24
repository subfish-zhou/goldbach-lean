import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints136
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_136 (j : Fin 16) : lowerPayment (16*136+j.val) ≤
    lowerValue ((point 2 split 4096 (16*136+j.val)+point 2 split 4096 (16*136+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2176 ≤ lowerValue ((point 2 split 4096 2176+point 2 split 4096 2177)/2)
    have hp : lowerPayment 2176 = (248599349069:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2176+point 2 split 4096 2177)/2 = (464317643:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((464317643:ℝ)/168755200)/ClassicalSixthBranch.v ((464317643:ℝ)/168755200) = (645741965243:ℝ)/316089291416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2176
  · change lowerPayment 2177 ≤ lowerValue ((point 2 split 4096 2177+point 2 split 4096 2178)/2)
    have hp : lowerPayment 2177 = (248688881342:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2177+point 2 split 4096 2178)/2 = (92875181:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((92875181:ℝ)/33751040)/ClassicalSixthBranch.v ((92875181:ℝ)/33751040) = (645664651569:ℝ)/316041283528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2177
  · change lowerPayment 2178 ≤ lowerValue ((point 2 split 4096 2178+point 2 split 4096 2179)/2)
    have hp : lowerPayment 2178 = (248778406300:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2178+point 2 split 4096 2179)/2 = (464434167:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((464434167:ℝ)/168755200)/ClassicalSixthBranch.v ((464434167:ℝ)/168755200) = (129117467579:ℝ)/63198655128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2178
  · change lowerPayment 2179 ≤ lowerValue ((point 2 split 4096 2179+point 2 split 4096 2180)/2)
    have hp : lowerPayment 2179 = (248867923958:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2179+point 2 split 4096 2180)/2 = (464492429:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((464492429:ℝ)/168755200)/ClassicalSixthBranch.v ((464492429:ℝ)/168755200) = (645510024221:ℝ)/315945267752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2179
  · change lowerPayment 2180 ≤ lowerValue ((point 2 split 4096 2180+point 2 split 4096 2181)/2)
    have hp : lowerPayment 2180 = (248957434333:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2180+point 2 split 4096 2181)/2 = (464550691:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((464550691:ℝ)/168755200)/ClassicalSixthBranch.v ((464550691:ℝ)/168755200) = (645432710547:ℝ)/315897259864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2180
  · change lowerPayment 2181 ≤ lowerValue ((point 2 split 4096 2181+point 2 split 4096 2182)/2)
    have hp : lowerPayment 2181 = (249046937440:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2181+point 2 split 4096 2182)/2 = (464608953:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((464608953:ℝ)/168755200)/ClassicalSixthBranch.v ((464608953:ℝ)/168755200) = (645355396873:ℝ)/315849251976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2181
  · change lowerPayment 2182 ≤ lowerValue ((point 2 split 4096 2182+point 2 split 4096 2183)/2)
    have hp : lowerPayment 2182 = (249136433295:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2182+point 2 split 4096 2183)/2 = (92933443:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((92933443:ℝ)/33751040)/ClassicalSixthBranch.v ((92933443:ℝ)/33751040) = (645278083199:ℝ)/315801244088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2182
  · change lowerPayment 2183 ≤ lowerValue ((point 2 split 4096 2183+point 2 split 4096 2184)/2)
    have hp : lowerPayment 2183 = (249225921913:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2183+point 2 split 4096 2184)/2 = (464725477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((464725477:ℝ)/168755200)/ClassicalSixthBranch.v ((464725477:ℝ)/168755200) = (25808030781:ℝ)/12630129448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2183
  · change lowerPayment 2184 ≤ lowerValue ((point 2 split 4096 2184+point 2 split 4096 2185)/2)
    have hp : lowerPayment 2184 = (249315403311:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2184+point 2 split 4096 2185)/2 = (464783739:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((464783739:ℝ)/168755200)/ClassicalSixthBranch.v ((464783739:ℝ)/168755200) = (645123455851:ℝ)/315705228312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2184
  · change lowerPayment 2185 ≤ lowerValue ((point 2 split 4096 2185+point 2 split 4096 2186)/2)
    have hp : lowerPayment 2185 = (249404877503:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2185+point 2 split 4096 2186)/2 = (464842001:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((464842001:ℝ)/168755200)/ClassicalSixthBranch.v ((464842001:ℝ)/168755200) = (645046142177:ℝ)/315657220424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2185
  · change lowerPayment 2186 ≤ lowerValue ((point 2 split 4096 2186+point 2 split 4096 2187)/2)
    have hp : lowerPayment 2186 = (249494344506:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2186+point 2 split 4096 2187)/2 = (464900263:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((464900263:ℝ)/168755200)/ClassicalSixthBranch.v ((464900263:ℝ)/168755200) = (644968828503:ℝ)/315609212536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2186
  · change lowerPayment 2187 ≤ lowerValue ((point 2 split 4096 2187+point 2 split 4096 2188)/2)
    have hp : lowerPayment 2187 = (249583804335:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2187+point 2 split 4096 2188)/2 = (18598341:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((18598341:ℝ)/6750208)/ClassicalSixthBranch.v ((18598341:ℝ)/6750208) = (644891514829:ℝ)/315561204648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2187
  · change lowerPayment 2188 ≤ lowerValue ((point 2 split 4096 2188+point 2 split 4096 2189)/2)
    have hp : lowerPayment 2188 = (249673257006:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2188+point 2 split 4096 2189)/2 = (465016787:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((465016787:ℝ)/168755200)/ClassicalSixthBranch.v ((465016787:ℝ)/168755200) = (128962840231:ℝ)/63102639352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2188
  · change lowerPayment 2189 ≤ lowerValue ((point 2 split 4096 2189+point 2 split 4096 2190)/2)
    have hp : lowerPayment 2189 = (249762702534:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2189+point 2 split 4096 2190)/2 = (465075049:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((465075049:ℝ)/168755200)/ClassicalSixthBranch.v ((465075049:ℝ)/168755200) = (644736887481:ℝ)/315465188872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2189
  · change lowerPayment 2190 ≤ lowerValue ((point 2 split 4096 2190+point 2 split 4096 2191)/2)
    have hp : lowerPayment 2190 = (249852140936:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2190+point 2 split 4096 2191)/2 = (465133311:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((465133311:ℝ)/168755200)/ClassicalSixthBranch.v ((465133311:ℝ)/168755200) = (644659573807:ℝ)/315417180984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2190
  · change lowerPayment 2191 ≤ lowerValue ((point 2 split 4096 2191+point 2 split 4096 2192)/2)
    have hp : lowerPayment 2191 = (249941572226:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2191+point 2 split 4096 2192)/2 = (465191573:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((465191573:ℝ)/168755200)/ClassicalSixthBranch.v ((465191573:ℝ)/168755200) = (644582260133:ℝ)/315369173096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2191
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_136
