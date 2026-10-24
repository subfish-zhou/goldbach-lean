import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints192
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_192 (j : Fin 16) : lowerPayment (16*192+j.val) ≤
    lowerValue ((point 2 split 4096 (16*192+j.val)+point 2 split 4096 (16*192+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3072 ≤ lowerValue ((point 2 split 4096 3072+point 2 split 4096 3073)/2)
    have hp : lowerPayment 3072 = (327670325837:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3072+point 2 split 4096 3073)/2 = (103304079:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((103304079:ℝ)/33751040)/ClassicalSixthBranch.v ((103304079:ℝ)/33751040) = (576468913339:ℝ)/273074223768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3072
  · change lowerPayment 3073 ≤ lowerValue ((point 2 split 4096 3073+point 2 split 4096 3074)/2)
    have hp : lowerPayment 3073 = (327759220755:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3073+point 2 split 4096 3074)/2 = (516578657:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((516578657:ℝ)/168755200)/ClassicalSixthBranch.v ((516578657:ℝ)/168755200) = (115278319933:ℝ)/54605243176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3073
  · change lowerPayment 3074 ≤ lowerValue ((point 2 split 4096 3074+point 2 split 4096 3075)/2)
    have hp : lowerPayment 3074 = (327848121365:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3074+point 2 split 4096 3075)/2 = (516636919:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((516636919:ℝ)/168755200)/ClassicalSixthBranch.v ((516636919:ℝ)/168755200) = (576314285991:ℝ)/272978207992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3074
  · change lowerPayment 3075 ≤ lowerValue ((point 2 split 4096 3075+point 2 split 4096 3076)/2)
    have hp : lowerPayment 3075 = (327937027683:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3075+point 2 split 4096 3076)/2 = (516695181:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((516695181:ℝ)/168755200)/ClassicalSixthBranch.v ((516695181:ℝ)/168755200) = (576236972317:ℝ)/272930200104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3075
  · change lowerPayment 3076 ≤ lowerValue ((point 2 split 4096 3076+point 2 split 4096 3077)/2)
    have hp : lowerPayment 3076 = (328025939722:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3076+point 2 split 4096 3077)/2 = (516753443:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((516753443:ℝ)/168755200)/ClassicalSixthBranch.v ((516753443:ℝ)/168755200) = (576159658643:ℝ)/272882192216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3076
  · change lowerPayment 3077 ≤ lowerValue ((point 2 split 4096 3077+point 2 split 4096 3078)/2)
    have hp : lowerPayment 3077 = (328114857496:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3077+point 2 split 4096 3078)/2 = (103362341:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((103362341:ℝ)/33751040)/ClassicalSixthBranch.v ((103362341:ℝ)/33751040) = (576082344969:ℝ)/272834184328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3077
  · change lowerPayment 3078 ≤ lowerValue ((point 2 split 4096 3078+point 2 split 4096 3079)/2)
    have hp : lowerPayment 3078 = (328203781021:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3078+point 2 split 4096 3079)/2 = (516869967:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((516869967:ℝ)/168755200)/ClassicalSixthBranch.v ((516869967:ℝ)/168755200) = (115201006259:ℝ)/54557235288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3078
  · change lowerPayment 3079 ≤ lowerValue ((point 2 split 4096 3079+point 2 split 4096 3080)/2)
    have hp : lowerPayment 3079 = (328292710309:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3079+point 2 split 4096 3080)/2 = (516928229:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((516928229:ℝ)/168755200)/ClassicalSixthBranch.v ((516928229:ℝ)/168755200) = (575927717621:ℝ)/272738168552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3079
  · change lowerPayment 3080 ≤ lowerValue ((point 2 split 4096 3080+point 2 split 4096 3081)/2)
    have hp : lowerPayment 3080 = (328381645376:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3080+point 2 split 4096 3081)/2 = (516986491:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((516986491:ℝ)/168755200)/ClassicalSixthBranch.v ((516986491:ℝ)/168755200) = (575850403947:ℝ)/272690160664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3080
  · change lowerPayment 3081 ≤ lowerValue ((point 2 split 4096 3081+point 2 split 4096 3082)/2)
    have hp : lowerPayment 3081 = (328470586235:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3081+point 2 split 4096 3082)/2 = (517044753:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((517044753:ℝ)/168755200)/ClassicalSixthBranch.v ((517044753:ℝ)/168755200) = (575773090273:ℝ)/272642152776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3081
  · change lowerPayment 3082 ≤ lowerValue ((point 2 split 4096 3082+point 2 split 4096 3083)/2)
    have hp : lowerPayment 3082 = (328559532901:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3082+point 2 split 4096 3083)/2 = (103420603:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((103420603:ℝ)/33751040)/ClassicalSixthBranch.v ((103420603:ℝ)/33751040) = (575695776599:ℝ)/272594144888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3082
  · change lowerPayment 3083 ≤ lowerValue ((point 2 split 4096 3083+point 2 split 4096 3084)/2)
    have hp : lowerPayment 3083 = (328648485389:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3083+point 2 split 4096 3084)/2 = (517161277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((517161277:ℝ)/168755200)/ClassicalSixthBranch.v ((517161277:ℝ)/168755200) = (23024738517:ℝ)/10901845480 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3083
  · change lowerPayment 3084 ≤ lowerValue ((point 2 split 4096 3084+point 2 split 4096 3085)/2)
    have hp : lowerPayment 3084 = (328737443712:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3084+point 2 split 4096 3085)/2 = (517219539:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((517219539:ℝ)/168755200)/ClassicalSixthBranch.v ((517219539:ℝ)/168755200) = (575541149251:ℝ)/272498129112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3084
  · change lowerPayment 3085 ≤ lowerValue ((point 2 split 4096 3085+point 2 split 4096 3086)/2)
    have hp : lowerPayment 3085 = (328826407884:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3085+point 2 split 4096 3086)/2 = (517277801:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((517277801:ℝ)/168755200)/ClassicalSixthBranch.v ((517277801:ℝ)/168755200) = (575463835577:ℝ)/272450121224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3085
  · change lowerPayment 3086 ≤ lowerValue ((point 2 split 4096 3086+point 2 split 4096 3087)/2)
    have hp : lowerPayment 3086 = (328915377921:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3086+point 2 split 4096 3087)/2 = (517336063:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((517336063:ℝ)/168755200)/ClassicalSixthBranch.v ((517336063:ℝ)/168755200) = (575386521903:ℝ)/272402113336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3086
  · change lowerPayment 3087 ≤ lowerValue ((point 2 split 4096 3087+point 2 split 4096 3088)/2)
    have hp : lowerPayment 3087 = (329004353836:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3087+point 2 split 4096 3088)/2 = (20695773:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((20695773:ℝ)/6750208)/ClassicalSixthBranch.v ((20695773:ℝ)/6750208) = (575309208229:ℝ)/272354105448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3087
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_192
