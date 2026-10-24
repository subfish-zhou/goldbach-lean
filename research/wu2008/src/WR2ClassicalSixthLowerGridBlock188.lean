import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints188
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_188 (j : Fin 16) : lowerPayment (16*188+j.val) ≤
    lowerValue ((point 2 split 4096 (16*188+j.val)+point 2 split 4096 (16*188+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3008 ≤ lowerValue ((point 2 split 4096 3008+point 2 split 4096 3009)/2)
    have hp : lowerPayment 3008 = (321992240660:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3008+point 2 split 4096 3009)/2 = (512791627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((512791627:ℝ)/168755200)/ClassicalSixthBranch.v ((512791627:ℝ)/168755200) = (23256679539:ℝ)/11045869144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3008
  · change lowerPayment 3009 ≤ lowerValue ((point 2 split 4096 3009+point 2 split 4096 3010)/2)
    have hp : lowerPayment 3009 = (322080800836:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3009+point 2 split 4096 3010)/2 = (512849889:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((512849889:ℝ)/168755200)/ClassicalSixthBranch.v ((512849889:ℝ)/168755200) = (581339674801:ℝ)/276098720712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3009
  · change lowerPayment 3010 ≤ lowerValue ((point 2 split 4096 3010+point 2 split 4096 3011)/2)
    have hp : lowerPayment 3010 = (322169365795:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3010+point 2 split 4096 3011)/2 = (512908151:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((512908151:ℝ)/168755200)/ClassicalSixthBranch.v ((512908151:ℝ)/168755200) = (581262361127:ℝ)/276050712824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3010
  · change lowerPayment 3011 ≤ lowerValue ((point 2 split 4096 3011+point 2 split 4096 3012)/2)
    have hp : lowerPayment 3011 = (322257935552:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3011+point 2 split 4096 3012)/2 = (512966413:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((512966413:ℝ)/168755200)/ClassicalSixthBranch.v ((512966413:ℝ)/168755200) = (581185047453:ℝ)/276002704936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3011
  · change lowerPayment 3012 ≤ lowerValue ((point 2 split 4096 3012+point 2 split 4096 3013)/2)
    have hp : lowerPayment 3012 = (322346510119:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3012+point 2 split 4096 3013)/2 = (20520987:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((20520987:ℝ)/6750208)/ClassicalSixthBranch.v ((20520987:ℝ)/6750208) = (581107733779:ℝ)/275954697048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3012
  · change lowerPayment 3013 ≤ lowerValue ((point 2 split 4096 3013+point 2 split 4096 3014)/2)
    have hp : lowerPayment 3013 = (322435089512:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3013+point 2 split 4096 3014)/2 = (513082937:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((513082937:ℝ)/168755200)/ClassicalSixthBranch.v ((513082937:ℝ)/168755200) = (116206084021:ℝ)/55181337832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3013
  · change lowerPayment 3014 ≤ lowerValue ((point 2 split 4096 3014+point 2 split 4096 3015)/2)
    have hp : lowerPayment 3014 = (322523673745:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3014+point 2 split 4096 3015)/2 = (513141199:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((513141199:ℝ)/168755200)/ClassicalSixthBranch.v ((513141199:ℝ)/168755200) = (580953106431:ℝ)/275858681272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3014
  · change lowerPayment 3015 ≤ lowerValue ((point 2 split 4096 3015+point 2 split 4096 3016)/2)
    have hp : lowerPayment 3015 = (322612262832:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3015+point 2 split 4096 3016)/2 = (513199461:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((513199461:ℝ)/168755200)/ClassicalSixthBranch.v ((513199461:ℝ)/168755200) = (580875792757:ℝ)/275810673384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3015
  · change lowerPayment 3016 ≤ lowerValue ((point 2 split 4096 3016+point 2 split 4096 3017)/2)
    have hp : lowerPayment 3016 = (322700856786:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3016+point 2 split 4096 3017)/2 = (513257723:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((513257723:ℝ)/168755200)/ClassicalSixthBranch.v ((513257723:ℝ)/168755200) = (580798479083:ℝ)/275762665496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3016
  · change lowerPayment 3017 ≤ lowerValue ((point 2 split 4096 3017+point 2 split 4096 3018)/2)
    have hp : lowerPayment 3017 = (322789455623:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3017+point 2 split 4096 3018)/2 = (102663197:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((102663197:ℝ)/33751040)/ClassicalSixthBranch.v ((102663197:ℝ)/33751040) = (580721165409:ℝ)/275714657608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3017
  · change lowerPayment 3018 ≤ lowerValue ((point 2 split 4096 3018+point 2 split 4096 3019)/2)
    have hp : lowerPayment 3018 = (322878059356:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3018+point 2 split 4096 3019)/2 = (513374247:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((513374247:ℝ)/168755200)/ClassicalSixthBranch.v ((513374247:ℝ)/168755200) = (116128770347:ℝ)/55133329944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3018
  · change lowerPayment 3019 ≤ lowerValue ((point 2 split 4096 3019+point 2 split 4096 3020)/2)
    have hp : lowerPayment 3019 = (322966668000:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3019+point 2 split 4096 3020)/2 = (513432509:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((513432509:ℝ)/168755200)/ClassicalSixthBranch.v ((513432509:ℝ)/168755200) = (580566538061:ℝ)/275618641832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3019
  · change lowerPayment 3020 ≤ lowerValue ((point 2 split 4096 3020+point 2 split 4096 3021)/2)
    have hp : lowerPayment 3020 = (323055281569:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3020+point 2 split 4096 3021)/2 = (513490771:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((513490771:ℝ)/168755200)/ClassicalSixthBranch.v ((513490771:ℝ)/168755200) = (580489224387:ℝ)/275570633944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3020
  · change lowerPayment 3021 ≤ lowerValue ((point 2 split 4096 3021+point 2 split 4096 3022)/2)
    have hp : lowerPayment 3021 = (323143900076:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3021+point 2 split 4096 3022)/2 = (513549033:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((513549033:ℝ)/168755200)/ClassicalSixthBranch.v ((513549033:ℝ)/168755200) = (580411910713:ℝ)/275522626056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3021
  · change lowerPayment 3022 ≤ lowerValue ((point 2 split 4096 3022+point 2 split 4096 3023)/2)
    have hp : lowerPayment 3022 = (323232523537:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3022+point 2 split 4096 3023)/2 = (102721459:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((102721459:ℝ)/33751040)/ClassicalSixthBranch.v ((102721459:ℝ)/33751040) = (580334597039:ℝ)/275474618168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3022
  · change lowerPayment 3023 ≤ lowerValue ((point 2 split 4096 3023+point 2 split 4096 3024)/2)
    have hp : lowerPayment 3023 = (323321151965:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3023+point 2 split 4096 3024)/2 = (513665557:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((513665557:ℝ)/168755200)/ClassicalSixthBranch.v ((513665557:ℝ)/168755200) = (116051456673:ℝ)/55085322056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3023
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_188
