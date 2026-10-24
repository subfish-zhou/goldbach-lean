import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints015
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_015 (j : Fin 16) : lowerPayment (16*15+j.val) ≤
    lowerValue ((point 2 split 4096 (16*15+j.val)+point 2 split 4096 (16*15+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 240 ≤ lowerValue ((point 2 split 4096 240+point 2 split 4096 241)/2)
    have hp : lowerPayment 240 = (37121492232:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 240+point 2 split 4096 241)/2 = (351522411:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((351522411:ℝ)/168755200)/ClassicalSixthBranch.v ((351522411:ℝ)/168755200) = (795421238107:ℝ)/409032562584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_240
  · change lowerPayment 241 ≤ lowerValue ((point 2 split 4096 241+point 2 split 4096 242)/2)
    have hp : lowerPayment 241 = (37267605227:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 241+point 2 split 4096 242)/2 = (351580673:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((351580673:ℝ)/168755200)/ClassicalSixthBranch.v ((351580673:ℝ)/168755200) = (795343924433:ℝ)/408984554696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_241
  · change lowerPayment 242 ≤ lowerValue ((point 2 split 4096 242+point 2 split 4096 243)/2)
    have hp : lowerPayment 242 = (37413654885:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 242+point 2 split 4096 243)/2 = (70327787:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((70327787:ℝ)/33751040)/ClassicalSixthBranch.v ((70327787:ℝ)/33751040) = (795266610759:ℝ)/408936546808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_242
  · change lowerPayment 243 ≤ lowerValue ((point 2 split 4096 243+point 2 split 4096 244)/2)
    have hp : lowerPayment 243 = (37559641262:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 243+point 2 split 4096 244)/2 = (351697197:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((351697197:ℝ)/168755200)/ClassicalSixthBranch.v ((351697197:ℝ)/168755200) = (159037859417:ℝ)/81777707784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_243
  · change lowerPayment 244 ≤ lowerValue ((point 2 split 4096 244+point 2 split 4096 245)/2)
    have hp : lowerPayment 244 = (37705564414:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 244+point 2 split 4096 245)/2 = (351755459:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((351755459:ℝ)/168755200)/ClassicalSixthBranch.v ((351755459:ℝ)/168755200) = (795111983411:ℝ)/408840531032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_244
  · change lowerPayment 245 ≤ lowerValue ((point 2 split 4096 245+point 2 split 4096 246)/2)
    have hp : lowerPayment 245 = (37851424400:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 245+point 2 split 4096 246)/2 = (351813721:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((351813721:ℝ)/168755200)/ClassicalSixthBranch.v ((351813721:ℝ)/168755200) = (795034669737:ℝ)/408792523144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_245
  · change lowerPayment 246 ≤ lowerValue ((point 2 split 4096 246+point 2 split 4096 247)/2)
    have hp : lowerPayment 246 = (37997221275:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 246+point 2 split 4096 247)/2 = (351871983:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((351871983:ℝ)/168755200)/ClassicalSixthBranch.v ((351871983:ℝ)/168755200) = (794957356063:ℝ)/408744515256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_246
  · change lowerPayment 247 ≤ lowerValue ((point 2 split 4096 247+point 2 split 4096 248)/2)
    have hp : lowerPayment 247 = (38142955096:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 247+point 2 split 4096 248)/2 = (70386049:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((70386049:ℝ)/33751040)/ClassicalSixthBranch.v ((70386049:ℝ)/33751040) = (794880042389:ℝ)/408696507368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_247
  · change lowerPayment 248 ≤ lowerValue ((point 2 split 4096 248+point 2 split 4096 249)/2)
    have hp : lowerPayment 248 = (38288625920:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 248+point 2 split 4096 249)/2 = (351988507:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((351988507:ℝ)/168755200)/ClassicalSixthBranch.v ((351988507:ℝ)/168755200) = (158960545743:ℝ)/81729699896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_248
  · change lowerPayment 249 ≤ lowerValue ((point 2 split 4096 249+point 2 split 4096 250)/2)
    have hp : lowerPayment 249 = (38434233804:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 249+point 2 split 4096 250)/2 = (352046769:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((352046769:ℝ)/168755200)/ClassicalSixthBranch.v ((352046769:ℝ)/168755200) = (794725415041:ℝ)/408600491592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_249
  · change lowerPayment 250 ≤ lowerValue ((point 2 split 4096 250+point 2 split 4096 251)/2)
    have hp : lowerPayment 250 = (38579778803:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 250+point 2 split 4096 251)/2 = (352105031:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((352105031:ℝ)/168755200)/ClassicalSixthBranch.v ((352105031:ℝ)/168755200) = (794648101367:ℝ)/408552483704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_250
  · change lowerPayment 251 ≤ lowerValue ((point 2 split 4096 251+point 2 split 4096 252)/2)
    have hp : lowerPayment 251 = (38725260974:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 251+point 2 split 4096 252)/2 = (352163293:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((352163293:ℝ)/168755200)/ClassicalSixthBranch.v ((352163293:ℝ)/168755200) = (794570787693:ℝ)/408504475816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_251
  · change lowerPayment 252 ≤ lowerValue ((point 2 split 4096 252+point 2 split 4096 253)/2)
    have hp : lowerPayment 252 = (38870680373:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 252+point 2 split 4096 253)/2 = (70444311:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((70444311:ℝ)/33751040)/ClassicalSixthBranch.v ((70444311:ℝ)/33751040) = (794493474019:ℝ)/408456467928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_252
  · change lowerPayment 253 ≤ lowerValue ((point 2 split 4096 253+point 2 split 4096 254)/2)
    have hp : lowerPayment 253 = (39016037057:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 253+point 2 split 4096 254)/2 = (352279817:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((352279817:ℝ)/168755200)/ClassicalSixthBranch.v ((352279817:ℝ)/168755200) = (158883232069:ℝ)/81681692008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_253
  · change lowerPayment 254 ≤ lowerValue ((point 2 split 4096 254+point 2 split 4096 255)/2)
    have hp : lowerPayment 254 = (39161331083:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 254+point 2 split 4096 255)/2 = (352338079:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((352338079:ℝ)/168755200)/ClassicalSixthBranch.v ((352338079:ℝ)/168755200) = (794338846671:ℝ)/408360452152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_254
  · change lowerPayment 255 ≤ lowerValue ((point 2 split 4096 255+point 2 split 4096 256)/2)
    have hp : lowerPayment 255 = (39306562505:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 255+point 2 split 4096 256)/2 = (352396341:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((352396341:ℝ)/168755200)/ClassicalSixthBranch.v ((352396341:ℝ)/168755200) = (794261532997:ℝ)/408312444264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_255
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_015
