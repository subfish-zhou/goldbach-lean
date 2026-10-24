import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints027
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_027 (j : Fin 16) : lowerPayment (16*27+j.val) ≤
    lowerValue ((point 2 split 4096 (16*27+j.val)+point 2 split 4096 (16*27+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 432 ≤ lowerValue ((point 2 split 4096 432+point 2 split 4096 433)/2)
    have hp : lowerPayment 432 = (64076949274:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 432+point 2 split 4096 433)/2 = (72541743:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((72541743:ℝ)/33751040)/ClassicalSixthBranch.v ((72541743:ℝ)/33751040) = (780577012699:ℝ)/399815048088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_432
  · change lowerPayment 433 ≤ lowerValue ((point 2 split 4096 433+point 2 split 4096 434)/2)
    have hp : lowerPayment 433 = (64211883199:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 433+point 2 split 4096 434)/2 = (362766977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((362766977:ℝ)/168755200)/ClassicalSixthBranch.v ((362766977:ℝ)/168755200) = (31219987961:ℝ)/15990681608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_433
  · change lowerPayment 434 ≤ lowerValue ((point 2 split 4096 434+point 2 split 4096 435)/2)
    have hp : lowerPayment 434 = (64346763761:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 434+point 2 split 4096 435)/2 = (362825239:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((362825239:ℝ)/168755200)/ClassicalSixthBranch.v ((362825239:ℝ)/168755200) = (780422385351:ℝ)/399719032312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_434
  · change lowerPayment 435 ≤ lowerValue ((point 2 split 4096 435+point 2 split 4096 436)/2)
    have hp : lowerPayment 435 = (64481591010:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 435+point 2 split 4096 436)/2 = (362883501:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((362883501:ℝ)/168755200)/ClassicalSixthBranch.v ((362883501:ℝ)/168755200) = (780345071677:ℝ)/399671024424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_435
  · change lowerPayment 436 ≤ lowerValue ((point 2 split 4096 436+point 2 split 4096 437)/2)
    have hp : lowerPayment 436 = (64616364991:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 436+point 2 split 4096 437)/2 = (362941763:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((362941763:ℝ)/168755200)/ClassicalSixthBranch.v ((362941763:ℝ)/168755200) = (780267758003:ℝ)/399623016536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_436
  · change lowerPayment 437 ≤ lowerValue ((point 2 split 4096 437+point 2 split 4096 438)/2)
    have hp : lowerPayment 437 = (64751085753:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 437+point 2 split 4096 438)/2 = (14520001:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((14520001:ℝ)/6750208)/ClassicalSixthBranch.v ((14520001:ℝ)/6750208) = (780190444329:ℝ)/399575008648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_437
  · change lowerPayment 438 ≤ lowerValue ((point 2 split 4096 438+point 2 split 4096 439)/2)
    have hp : lowerPayment 438 = (64885753343:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 438+point 2 split 4096 439)/2 = (363058287:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((363058287:ℝ)/168755200)/ClassicalSixthBranch.v ((363058287:ℝ)/168755200) = (156022626131:ℝ)/79905400152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_438
  · change lowerPayment 439 ≤ lowerValue ((point 2 split 4096 439+point 2 split 4096 440)/2)
    have hp : lowerPayment 439 = (65020367807:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 439+point 2 split 4096 440)/2 = (363116549:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((363116549:ℝ)/168755200)/ClassicalSixthBranch.v ((363116549:ℝ)/168755200) = (780035816981:ℝ)/399478992872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_439
  · change lowerPayment 440 ≤ lowerValue ((point 2 split 4096 440+point 2 split 4096 441)/2)
    have hp : lowerPayment 440 = (65154929193:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 440+point 2 split 4096 441)/2 = (363174811:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((363174811:ℝ)/168755200)/ClassicalSixthBranch.v ((363174811:ℝ)/168755200) = (779958503307:ℝ)/399430984984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_440
  · change lowerPayment 441 ≤ lowerValue ((point 2 split 4096 441+point 2 split 4096 442)/2)
    have hp : lowerPayment 441 = (65289437549:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 441+point 2 split 4096 442)/2 = (363233073:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((363233073:ℝ)/168755200)/ClassicalSixthBranch.v ((363233073:ℝ)/168755200) = (779881189633:ℝ)/399382977096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_441
  · change lowerPayment 442 ≤ lowerValue ((point 2 split 4096 442+point 2 split 4096 443)/2)
    have hp : lowerPayment 442 = (65423892921:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 442+point 2 split 4096 443)/2 = (72658267:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((72658267:ℝ)/33751040)/ClassicalSixthBranch.v ((72658267:ℝ)/33751040) = (779803875959:ℝ)/399334969208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_442
  · change lowerPayment 443 ≤ lowerValue ((point 2 split 4096 443+point 2 split 4096 444)/2)
    have hp : lowerPayment 443 = (65558295356:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 443+point 2 split 4096 444)/2 = (363349597:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((363349597:ℝ)/168755200)/ClassicalSixthBranch.v ((363349597:ℝ)/168755200) = (155945312457:ℝ)/79857392264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_443
  · change lowerPayment 444 ≤ lowerValue ((point 2 split 4096 444+point 2 split 4096 445)/2)
    have hp : lowerPayment 444 = (65692644901:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 444+point 2 split 4096 445)/2 = (363407859:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((363407859:ℝ)/168755200)/ClassicalSixthBranch.v ((363407859:ℝ)/168755200) = (779649248611:ℝ)/399238953432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_444
  · change lowerPayment 445 ≤ lowerValue ((point 2 split 4096 445+point 2 split 4096 446)/2)
    have hp : lowerPayment 445 = (65826941604:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 445+point 2 split 4096 446)/2 = (363466121:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((363466121:ℝ)/168755200)/ClassicalSixthBranch.v ((363466121:ℝ)/168755200) = (779571934937:ℝ)/399190945544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_445
  · change lowerPayment 446 ≤ lowerValue ((point 2 split 4096 446+point 2 split 4096 447)/2)
    have hp : lowerPayment 446 = (65961185511:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 446+point 2 split 4096 447)/2 = (363524383:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((363524383:ℝ)/168755200)/ClassicalSixthBranch.v ((363524383:ℝ)/168755200) = (779494621263:ℝ)/399142937656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_446
  · change lowerPayment 447 ≤ lowerValue ((point 2 split 4096 447+point 2 split 4096 448)/2)
    have hp : lowerPayment 447 = (66095376669:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 447+point 2 split 4096 448)/2 = (72716529:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((72716529:ℝ)/33751040)/ClassicalSixthBranch.v ((72716529:ℝ)/33751040) = (779417307589:ℝ)/399094929768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_447
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_027
