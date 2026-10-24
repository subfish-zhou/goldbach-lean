import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints190
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_190 (j : Fin 16) : lowerPayment (16*190+j.val) ≤
    lowerValue ((point 2 split 4096 (16*190+j.val)+point 2 split 4096 (16*190+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3040 ≤ lowerValue ((point 2 split 4096 3040+point 2 split 4096 3041)/2)
    have hp : lowerPayment 3040 = (324828609008:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3040+point 2 split 4096 3041)/2 = (514656011:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((514656011:ℝ)/168755200)/ClassicalSixthBranch.v ((514656011:ℝ)/168755200) = (578942950907:ℝ)/274610476184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3040
  · change lowerPayment 3041 ≤ lowerValue ((point 2 split 4096 3041+point 2 split 4096 3042)/2)
    have hp : lowerPayment 3041 = (324917329277:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3041+point 2 split 4096 3042)/2 = (514714273:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((514714273:ℝ)/168755200)/ClassicalSixthBranch.v ((514714273:ℝ)/168755200) = (578865637233:ℝ)/274562468296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3041
  · change lowerPayment 3042 ≤ lowerValue ((point 2 split 4096 3042+point 2 split 4096 3043)/2)
    have hp : lowerPayment 3042 = (325006054783:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3042+point 2 split 4096 3043)/2 = (102954507:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((102954507:ℝ)/33751040)/ClassicalSixthBranch.v ((102954507:ℝ)/33751040) = (578788323559:ℝ)/274514460408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3042
  · change lowerPayment 3043 ≤ lowerValue ((point 2 split 4096 3043+point 2 split 4096 3044)/2)
    have hp : lowerPayment 3043 = (325094785541:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3043+point 2 split 4096 3044)/2 = (514830797:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((514830797:ℝ)/168755200)/ClassicalSixthBranch.v ((514830797:ℝ)/168755200) = (115742201977:ℝ)/54893290504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3043
  · change lowerPayment 3044 ≤ lowerValue ((point 2 split 4096 3044+point 2 split 4096 3045)/2)
    have hp : lowerPayment 3044 = (325183521564:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3044+point 2 split 4096 3045)/2 = (514889059:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((514889059:ℝ)/168755200)/ClassicalSixthBranch.v ((514889059:ℝ)/168755200) = (578633696211:ℝ)/274418444632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3044
  · change lowerPayment 3045 ≤ lowerValue ((point 2 split 4096 3045+point 2 split 4096 3046)/2)
    have hp : lowerPayment 3045 = (325272262867:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3045+point 2 split 4096 3046)/2 = (514947321:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((514947321:ℝ)/168755200)/ClassicalSixthBranch.v ((514947321:ℝ)/168755200) = (578556382537:ℝ)/274370436744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3045
  · change lowerPayment 3046 ≤ lowerValue ((point 2 split 4096 3046+point 2 split 4096 3047)/2)
    have hp : lowerPayment 3046 = (325361009464:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3046+point 2 split 4096 3047)/2 = (515005583:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((515005583:ℝ)/168755200)/ClassicalSixthBranch.v ((515005583:ℝ)/168755200) = (578479068863:ℝ)/274322428856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3046
  · change lowerPayment 3047 ≤ lowerValue ((point 2 split 4096 3047+point 2 split 4096 3048)/2)
    have hp : lowerPayment 3047 = (325449761370:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3047+point 2 split 4096 3048)/2 = (103012769:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((103012769:ℝ)/33751040)/ClassicalSixthBranch.v ((103012769:ℝ)/33751040) = (578401755189:ℝ)/274274420968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3047
  · change lowerPayment 3048 ≤ lowerValue ((point 2 split 4096 3048+point 2 split 4096 3049)/2)
    have hp : lowerPayment 3048 = (325538518598:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3048+point 2 split 4096 3049)/2 = (515122107:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((515122107:ℝ)/168755200)/ClassicalSixthBranch.v ((515122107:ℝ)/168755200) = (115664888303:ℝ)/54845282616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3048
  · change lowerPayment 3049 ≤ lowerValue ((point 2 split 4096 3049+point 2 split 4096 3050)/2)
    have hp : lowerPayment 3049 = (325627281163:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3049+point 2 split 4096 3050)/2 = (515180369:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((515180369:ℝ)/168755200)/ClassicalSixthBranch.v ((515180369:ℝ)/168755200) = (578247127841:ℝ)/274178405192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3049
  · change lowerPayment 3050 ≤ lowerValue ((point 2 split 4096 3050+point 2 split 4096 3051)/2)
    have hp : lowerPayment 3050 = (325716049079:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3050+point 2 split 4096 3051)/2 = (515238631:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((515238631:ℝ)/168755200)/ClassicalSixthBranch.v ((515238631:ℝ)/168755200) = (578169814167:ℝ)/274130397304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3050
  · change lowerPayment 3051 ≤ lowerValue ((point 2 split 4096 3051+point 2 split 4096 3052)/2)
    have hp : lowerPayment 3051 = (325804822360:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3051+point 2 split 4096 3052)/2 = (515296893:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((515296893:ℝ)/168755200)/ClassicalSixthBranch.v ((515296893:ℝ)/168755200) = (578092500493:ℝ)/274082389416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3051
  · change lowerPayment 3052 ≤ lowerValue ((point 2 split 4096 3052+point 2 split 4096 3053)/2)
    have hp : lowerPayment 3052 = (325893601020:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3052+point 2 split 4096 3053)/2 = (103071031:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((103071031:ℝ)/33751040)/ClassicalSixthBranch.v ((103071031:ℝ)/33751040) = (578015186819:ℝ)/274034381528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3052
  · change lowerPayment 3053 ≤ lowerValue ((point 2 split 4096 3053+point 2 split 4096 3054)/2)
    have hp : lowerPayment 3053 = (325982385074:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3053+point 2 split 4096 3054)/2 = (515413417:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((515413417:ℝ)/168755200)/ClassicalSixthBranch.v ((515413417:ℝ)/168755200) = (115587574629:ℝ)/54797274728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3053
  · change lowerPayment 3054 ≤ lowerValue ((point 2 split 4096 3054+point 2 split 4096 3055)/2)
    have hp : lowerPayment 3054 = (326071174536:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3054+point 2 split 4096 3055)/2 = (515471679:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((515471679:ℝ)/168755200)/ClassicalSixthBranch.v ((515471679:ℝ)/168755200) = (577860559471:ℝ)/273938365752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3054
  · change lowerPayment 3055 ≤ lowerValue ((point 2 split 4096 3055+point 2 split 4096 3056)/2)
    have hp : lowerPayment 3055 = (326159969421:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3055+point 2 split 4096 3056)/2 = (515529941:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((515529941:ℝ)/168755200)/ClassicalSixthBranch.v ((515529941:ℝ)/168755200) = (577783245797:ℝ)/273890357864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3055
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_190
