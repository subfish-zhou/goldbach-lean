import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints039
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_039 (j : Fin 16) : lowerPayment (16*39+j.val) ≤
    lowerValue ((point 2 split 4096 (16*39+j.val)+point 2 split 4096 (16*39+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 624 ≤ lowerValue ((point 2 split 4096 624+point 2 split 4096 625)/2)
    have hp : lowerPayment 624 = (89058588255:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 624+point 2 split 4096 625)/2 = (373895019:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((373895019:ℝ)/168755200)/ClassicalSixthBranch.v ((373895019:ℝ)/168755200) = (765732787291:ℝ)/390597533592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_624
  · change lowerPayment 625 ≤ lowerValue ((point 2 split 4096 625+point 2 split 4096 626)/2)
    have hp : lowerPayment 625 = (89184098202:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 625+point 2 split 4096 626)/2 = (373953281:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((373953281:ℝ)/168755200)/ClassicalSixthBranch.v ((373953281:ℝ)/168755200) = (765655473617:ℝ)/390549525704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_625
  · change lowerPayment 626 ≤ lowerValue ((point 2 split 4096 626+point 2 split 4096 627)/2)
    have hp : lowerPayment 626 = (89309563150:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 626+point 2 split 4096 627)/2 = (374011543:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((374011543:ℝ)/168755200)/ClassicalSixthBranch.v ((374011543:ℝ)/168755200) = (765578159943:ℝ)/390501517816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_626
  · change lowerPayment 627 ≤ lowerValue ((point 2 split 4096 627+point 2 split 4096 628)/2)
    have hp : lowerPayment 627 = (89434983139:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 627+point 2 split 4096 628)/2 = (74813961:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((74813961:ℝ)/33751040)/ClassicalSixthBranch.v ((74813961:ℝ)/33751040) = (765500846269:ℝ)/390453509928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_627
  · change lowerPayment 628 ≤ lowerValue ((point 2 split 4096 628+point 2 split 4096 629)/2)
    have hp : lowerPayment 628 = (89560358209:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 628+point 2 split 4096 629)/2 = (374128067:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((374128067:ℝ)/168755200)/ClassicalSixthBranch.v ((374128067:ℝ)/168755200) = (153084706519:ℝ)/78081100408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_628
  · change lowerPayment 629 ≤ lowerValue ((point 2 split 4096 629+point 2 split 4096 630)/2)
    have hp : lowerPayment 629 = (89685688401:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 629+point 2 split 4096 630)/2 = (374186329:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((374186329:ℝ)/168755200)/ClassicalSixthBranch.v ((374186329:ℝ)/168755200) = (765346218921:ℝ)/390357494152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_629
  · change lowerPayment 630 ≤ lowerValue ((point 2 split 4096 630+point 2 split 4096 631)/2)
    have hp : lowerPayment 630 = (89810973753:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 630+point 2 split 4096 631)/2 = (374244591:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((374244591:ℝ)/168755200)/ClassicalSixthBranch.v ((374244591:ℝ)/168755200) = (765268905247:ℝ)/390309486264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_630
  · change lowerPayment 631 ≤ lowerValue ((point 2 split 4096 631+point 2 split 4096 632)/2)
    have hp : lowerPayment 631 = (89936214307:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 631+point 2 split 4096 632)/2 = (374302853:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((374302853:ℝ)/168755200)/ClassicalSixthBranch.v ((374302853:ℝ)/168755200) = (765191591573:ℝ)/390261478376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_631
  · change lowerPayment 632 ≤ lowerValue ((point 2 split 4096 632+point 2 split 4096 633)/2)
    have hp : lowerPayment 632 = (90061410101:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 632+point 2 split 4096 633)/2 = (74872223:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((74872223:ℝ)/33751040)/ClassicalSixthBranch.v ((74872223:ℝ)/33751040) = (765114277899:ℝ)/390213470488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_632
  · change lowerPayment 633 ≤ lowerValue ((point 2 split 4096 633+point 2 split 4096 634)/2)
    have hp : lowerPayment 633 = (90186561175:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 633+point 2 split 4096 634)/2 = (374419377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((374419377:ℝ)/168755200)/ClassicalSixthBranch.v ((374419377:ℝ)/168755200) = (30601478569:ℝ)/15606618504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_633
  · change lowerPayment 634 ≤ lowerValue ((point 2 split 4096 634+point 2 split 4096 635)/2)
    have hp : lowerPayment 634 = (90311667570:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 634+point 2 split 4096 635)/2 = (374477639:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((374477639:ℝ)/168755200)/ClassicalSixthBranch.v ((374477639:ℝ)/168755200) = (764959650551:ℝ)/390117454712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_634
  · change lowerPayment 635 ≤ lowerValue ((point 2 split 4096 635+point 2 split 4096 636)/2)
    have hp : lowerPayment 635 = (90436729325:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 635+point 2 split 4096 636)/2 = (374535901:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((374535901:ℝ)/168755200)/ClassicalSixthBranch.v ((374535901:ℝ)/168755200) = (764882336877:ℝ)/390069446824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_635
  · change lowerPayment 636 ≤ lowerValue ((point 2 split 4096 636+point 2 split 4096 637)/2)
    have hp : lowerPayment 636 = (90561746479:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 636+point 2 split 4096 637)/2 = (374594163:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((374594163:ℝ)/168755200)/ClassicalSixthBranch.v ((374594163:ℝ)/168755200) = (764805023203:ℝ)/390021438936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_636
  · change lowerPayment 637 ≤ lowerValue ((point 2 split 4096 637+point 2 split 4096 638)/2)
    have hp : lowerPayment 637 = (90686719072:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 637+point 2 split 4096 638)/2 = (14986097:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((14986097:ℝ)/6750208)/ClassicalSixthBranch.v ((14986097:ℝ)/6750208) = (764727709529:ℝ)/389973431048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_637
  · change lowerPayment 638 ≤ lowerValue ((point 2 split 4096 638+point 2 split 4096 639)/2)
    have hp : lowerPayment 638 = (90811647144:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 638+point 2 split 4096 639)/2 = (374710687:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((374710687:ℝ)/168755200)/ClassicalSixthBranch.v ((374710687:ℝ)/168755200) = (152930079171:ℝ)/77985084632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_638
  · change lowerPayment 639 ≤ lowerValue ((point 2 split 4096 639+point 2 split 4096 640)/2)
    have hp : lowerPayment 639 = (90936530735:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 639+point 2 split 4096 640)/2 = (374768949:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((374768949:ℝ)/168755200)/ClassicalSixthBranch.v ((374768949:ℝ)/168755200) = (764573082181:ℝ)/389877415272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_639
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_039
