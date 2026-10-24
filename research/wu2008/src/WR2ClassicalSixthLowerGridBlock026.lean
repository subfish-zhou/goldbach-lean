import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints026
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_026 (j : Fin 16) : lowerPayment (16*26+j.val) ≤
    lowerValue ((point 2 split 4096 (16*26+j.val)+point 2 split 4096 (16*26+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 416 ≤ lowerValue ((point 2 split 4096 416+point 2 split 4096 417)/2)
    have hp : lowerPayment 416 = (61910710450:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 416+point 2 split 4096 417)/2 = (361776523:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((361776523:ℝ)/168755200)/ClassicalSixthBranch.v ((361776523:ℝ)/168755200) = (781814031483:ℝ)/400583174296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_416
  · change lowerPayment 417 ≤ lowerValue ((point 2 split 4096 417+point 2 split 4096 418)/2)
    have hp : lowerPayment 417 = (62046504643:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 417+point 2 split 4096 418)/2 = (72366957:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((72366957:ℝ)/33751040)/ClassicalSixthBranch.v ((72366957:ℝ)/33751040) = (781736717809:ℝ)/400535166408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_417
  · change lowerPayment 418 ≤ lowerValue ((point 2 split 4096 418+point 2 split 4096 419)/2)
    have hp : lowerPayment 418 = (62182244710:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 418+point 2 split 4096 419)/2 = (361893047:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((361893047:ℝ)/168755200)/ClassicalSixthBranch.v ((361893047:ℝ)/168755200) = (156331880827:ℝ)/80097431704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_418
  · change lowerPayment 419 ≤ lowerValue ((point 2 split 4096 419+point 2 split 4096 420)/2)
    have hp : lowerPayment 419 = (62317930699:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 419+point 2 split 4096 420)/2 = (361951309:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((361951309:ℝ)/168755200)/ClassicalSixthBranch.v ((361951309:ℝ)/168755200) = (781582090461:ℝ)/400439150632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_419
  · change lowerPayment 420 ≤ lowerValue ((point 2 split 4096 420+point 2 split 4096 421)/2)
    have hp : lowerPayment 420 = (62453562659:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 420+point 2 split 4096 421)/2 = (362009571:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((362009571:ℝ)/168755200)/ClassicalSixthBranch.v ((362009571:ℝ)/168755200) = (1553687429:ℝ)/796006248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_420
  · change lowerPayment 421 ≤ lowerValue ((point 2 split 4096 421+point 2 split 4096 422)/2)
    have hp : lowerPayment 421 = (62589140636:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 421+point 2 split 4096 422)/2 = (362067833:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((362067833:ℝ)/168755200)/ClassicalSixthBranch.v ((362067833:ℝ)/168755200) = (781427463113:ℝ)/400343134856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_421
  · change lowerPayment 422 ≤ lowerValue ((point 2 split 4096 422+point 2 split 4096 423)/2)
    have hp : lowerPayment 422 = (62724664680:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 422+point 2 split 4096 423)/2 = (72425219:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((72425219:ℝ)/33751040)/ClassicalSixthBranch.v ((72425219:ℝ)/33751040) = (781350149439:ℝ)/400295126968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_422
  · change lowerPayment 423 ≤ lowerValue ((point 2 split 4096 423+point 2 split 4096 424)/2)
    have hp : lowerPayment 423 = (62860134837:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 423+point 2 split 4096 424)/2 = (362184357:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((362184357:ℝ)/168755200)/ClassicalSixthBranch.v ((362184357:ℝ)/168755200) = (156254567153:ℝ)/80049423816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_423
  · change lowerPayment 424 ≤ lowerValue ((point 2 split 4096 424+point 2 split 4096 425)/2)
    have hp : lowerPayment 424 = (62995551157:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 424+point 2 split 4096 425)/2 = (362242619:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((362242619:ℝ)/168755200)/ClassicalSixthBranch.v ((362242619:ℝ)/168755200) = (781195522091:ℝ)/400199111192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_424
  · change lowerPayment 425 ≤ lowerValue ((point 2 split 4096 425+point 2 split 4096 426)/2)
    have hp : lowerPayment 425 = (63130913686:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 425+point 2 split 4096 426)/2 = (362300881:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((362300881:ℝ)/168755200)/ClassicalSixthBranch.v ((362300881:ℝ)/168755200) = (781118208417:ℝ)/400151103304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_425
  · change lowerPayment 426 ≤ lowerValue ((point 2 split 4096 426+point 2 split 4096 427)/2)
    have hp : lowerPayment 426 = (63266222473:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 426+point 2 split 4096 427)/2 = (362359143:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((362359143:ℝ)/168755200)/ClassicalSixthBranch.v ((362359143:ℝ)/168755200) = (781040894743:ℝ)/400103095416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_426
  · change lowerPayment 427 ≤ lowerValue ((point 2 split 4096 427+point 2 split 4096 428)/2)
    have hp : lowerPayment 427 = (63401477565:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 427+point 2 split 4096 428)/2 = (72483481:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((72483481:ℝ)/33751040)/ClassicalSixthBranch.v ((72483481:ℝ)/33751040) = (780963581069:ℝ)/400055087528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_427
  · change lowerPayment 428 ≤ lowerValue ((point 2 split 4096 428+point 2 split 4096 429)/2)
    have hp : lowerPayment 428 = (63536679011:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 428+point 2 split 4096 429)/2 = (362475667:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((362475667:ℝ)/168755200)/ClassicalSixthBranch.v ((362475667:ℝ)/168755200) = (156177253479:ℝ)/80001415928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_428
  · change lowerPayment 429 ≤ lowerValue ((point 2 split 4096 429+point 2 split 4096 430)/2)
    have hp : lowerPayment 429 = (63671826857:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 429+point 2 split 4096 430)/2 = (362533929:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((362533929:ℝ)/168755200)/ClassicalSixthBranch.v ((362533929:ℝ)/168755200) = (780808953721:ℝ)/399959071752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_429
  · change lowerPayment 430 ≤ lowerValue ((point 2 split 4096 430+point 2 split 4096 431)/2)
    have hp : lowerPayment 430 = (63806921151:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 430+point 2 split 4096 431)/2 = (362592191:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((362592191:ℝ)/168755200)/ClassicalSixthBranch.v ((362592191:ℝ)/168755200) = (780731640047:ℝ)/399911063864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_430
  · change lowerPayment 431 ≤ lowerValue ((point 2 split 4096 431+point 2 split 4096 432)/2)
    have hp : lowerPayment 431 = (63941961941:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 431+point 2 split 4096 432)/2 = (362650453:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((362650453:ℝ)/168755200)/ClassicalSixthBranch.v ((362650453:ℝ)/168755200) = (780654326373:ℝ)/399863055976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_431
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_026
