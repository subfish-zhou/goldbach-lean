import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints198
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_198 (j : Fin 16) : lowerPayment (16*198+j.val) ≤
    lowerValue ((point 2 split 4096 (16*198+j.val)+point 2 split 4096 (16*198+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3168 ≤ lowerValue ((point 2 split 4096 3168+point 2 split 4096 3169)/2)
    have hp : lowerPayment 3168 = (336232239460:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3168+point 2 split 4096 3169)/2 = (522113547:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((522113547:ℝ)/168755200)/ClassicalSixthBranch.v ((522113547:ℝ)/168755200) = (113809360127:ℝ)/53693093304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3168
  · change lowerPayment 3169 ≤ lowerValue ((point 2 split 4096 3169+point 2 split 4096 3170)/2)
    have hp : lowerPayment 3169 = (336321746131:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3169+point 2 split 4096 3170)/2 = (522171809:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((522171809:ℝ)/168755200)/ClassicalSixthBranch.v ((522171809:ℝ)/168755200) = (568969486961:ℝ)/268417458632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3169
  · change lowerPayment 3170 ≤ lowerValue ((point 2 split 4096 3170+point 2 split 4096 3171)/2)
    have hp : lowerPayment 3170 = (336411259871:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3170+point 2 split 4096 3171)/2 = (522230071:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((522230071:ℝ)/168755200)/ClassicalSixthBranch.v ((522230071:ℝ)/168755200) = (568892173287:ℝ)/268369450744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3170
  · change lowerPayment 3171 ≤ lowerValue ((point 2 split 4096 3171+point 2 split 4096 3172)/2)
    have hp : lowerPayment 3171 = (336500780695:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3171+point 2 split 4096 3172)/2 = (522288333:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((522288333:ℝ)/168755200)/ClassicalSixthBranch.v ((522288333:ℝ)/168755200) = (568814859613:ℝ)/268321442856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3171
  · change lowerPayment 3172 ≤ lowerValue ((point 2 split 4096 3172+point 2 split 4096 3173)/2)
    have hp : lowerPayment 3172 = (336590308617:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3172+point 2 split 4096 3173)/2 = (104469319:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((104469319:ℝ)/33751040)/ClassicalSixthBranch.v ((104469319:ℝ)/33751040) = (568737545939:ℝ)/268273434968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3172
  · change lowerPayment 3173 ≤ lowerValue ((point 2 split 4096 3173+point 2 split 4096 3174)/2)
    have hp : lowerPayment 3173 = (336679843651:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3173+point 2 split 4096 3174)/2 = (522404857:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((522404857:ℝ)/168755200)/ClassicalSixthBranch.v ((522404857:ℝ)/168755200) = (113732046453:ℝ)/53645085416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3173
  · change lowerPayment 3174 ≤ lowerValue ((point 2 split 4096 3174+point 2 split 4096 3175)/2)
    have hp : lowerPayment 3174 = (336769385812:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3174+point 2 split 4096 3175)/2 = (522463119:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((522463119:ℝ)/168755200)/ClassicalSixthBranch.v ((522463119:ℝ)/168755200) = (568582918591:ℝ)/268177419192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3174
  · change lowerPayment 3175 ≤ lowerValue ((point 2 split 4096 3175+point 2 split 4096 3176)/2)
    have hp : lowerPayment 3175 = (336858935114:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3175+point 2 split 4096 3176)/2 = (522521381:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((522521381:ℝ)/168755200)/ClassicalSixthBranch.v ((522521381:ℝ)/168755200) = (568505604917:ℝ)/268129411304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3175
  · change lowerPayment 3176 ≤ lowerValue ((point 2 split 4096 3176+point 2 split 4096 3177)/2)
    have hp : lowerPayment 3176 = (336948491572:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3176+point 2 split 4096 3177)/2 = (522579643:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((522579643:ℝ)/168755200)/ClassicalSixthBranch.v ((522579643:ℝ)/168755200) = (568428291243:ℝ)/268081403416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3176
  · change lowerPayment 3177 ≤ lowerValue ((point 2 split 4096 3177+point 2 split 4096 3178)/2)
    have hp : lowerPayment 3177 = (337038055201:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3177+point 2 split 4096 3178)/2 = (104527581:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((104527581:ℝ)/33751040)/ClassicalSixthBranch.v ((104527581:ℝ)/33751040) = (568350977569:ℝ)/268033395528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3177
  · change lowerPayment 3178 ≤ lowerValue ((point 2 split 4096 3178+point 2 split 4096 3179)/2)
    have hp : lowerPayment 3178 = (337127626013:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3178+point 2 split 4096 3179)/2 = (522696167:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((522696167:ℝ)/168755200)/ClassicalSixthBranch.v ((522696167:ℝ)/168755200) = (113654732779:ℝ)/53597077528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3178
  · change lowerPayment 3179 ≤ lowerValue ((point 2 split 4096 3179+point 2 split 4096 3180)/2)
    have hp : lowerPayment 3179 = (337217204025:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3179+point 2 split 4096 3180)/2 = (522754429:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((522754429:ℝ)/168755200)/ClassicalSixthBranch.v ((522754429:ℝ)/168755200) = (568196350221:ℝ)/267937379752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3179
  · change lowerPayment 3180 ≤ lowerValue ((point 2 split 4096 3180+point 2 split 4096 3181)/2)
    have hp : lowerPayment 3180 = (337306789250:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3180+point 2 split 4096 3181)/2 = (522812691:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((522812691:ℝ)/168755200)/ClassicalSixthBranch.v ((522812691:ℝ)/168755200) = (568119036547:ℝ)/267889371864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3180
  · change lowerPayment 3181 ≤ lowerValue ((point 2 split 4096 3181+point 2 split 4096 3182)/2)
    have hp : lowerPayment 3181 = (337396381704:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3181+point 2 split 4096 3182)/2 = (522870953:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((522870953:ℝ)/168755200)/ClassicalSixthBranch.v ((522870953:ℝ)/168755200) = (568041722873:ℝ)/267841363976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3181
  · change lowerPayment 3182 ≤ lowerValue ((point 2 split 4096 3182+point 2 split 4096 3183)/2)
    have hp : lowerPayment 3182 = (337485981399:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3182+point 2 split 4096 3183)/2 = (104585843:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((104585843:ℝ)/33751040)/ClassicalSixthBranch.v ((104585843:ℝ)/33751040) = (567964409199:ℝ)/267793356088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3182
  · change lowerPayment 3183 ≤ lowerValue ((point 2 split 4096 3183+point 2 split 4096 3184)/2)
    have hp : lowerPayment 3183 = (337575588352:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3183+point 2 split 4096 3184)/2 = (522987477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((522987477:ℝ)/168755200)/ClassicalSixthBranch.v ((522987477:ℝ)/168755200) = (22715483821:ℝ)/10709813928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3183
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_198
