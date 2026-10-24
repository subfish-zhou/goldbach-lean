import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints172
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_172 (j : Fin 16) : lowerPayment (16*172+j.val) ≤
    lowerValue ((point 2 split 4096 (16*172+j.val)+point 2 split 4096 (16*172+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2752 ≤ lowerValue ((point 2 split 4096 2752+point 2 split 4096 2753)/2)
    have hp : lowerPayment 2752 = (299438179619:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2752+point 2 split 4096 2753)/2 = (99575311:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((99575311:ℝ)/33751040)/ClassicalSixthBranch.v ((99575311:ℝ)/33751040) = (601209289019:ℝ)/288436747928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2752
  · change lowerPayment 2753 ≤ lowerValue ((point 2 split 4096 2753+point 2 split 4096 2754)/2)
    have hp : lowerPayment 2753 = (299525980204:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2753+point 2 split 4096 2754)/2 = (497934817:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((497934817:ℝ)/168755200)/ClassicalSixthBranch.v ((497934817:ℝ)/168755200) = (120226395069:ℝ)/57677748008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2753
  · change lowerPayment 2754 ≤ lowerValue ((point 2 split 4096 2754+point 2 split 4096 2755)/2)
    have hp : lowerPayment 2754 = (299613781956:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2754+point 2 split 4096 2755)/2 = (497993079:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((497993079:ℝ)/168755200)/ClassicalSixthBranch.v ((497993079:ℝ)/168755200) = (601054661671:ℝ)/288340732152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2754
  · change lowerPayment 2755 ≤ lowerValue ((point 2 split 4096 2755+point 2 split 4096 2756)/2)
    have hp : lowerPayment 2755 = (299701584890:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2755+point 2 split 4096 2756)/2 = (498051341:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((498051341:ℝ)/168755200)/ClassicalSixthBranch.v ((498051341:ℝ)/168755200) = (600977347997:ℝ)/288292724264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2755
  · change lowerPayment 2756 ≤ lowerValue ((point 2 split 4096 2756+point 2 split 4096 2757)/2)
    have hp : lowerPayment 2756 = (299789389019:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2756+point 2 split 4096 2757)/2 = (498109603:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((498109603:ℝ)/168755200)/ClassicalSixthBranch.v ((498109603:ℝ)/168755200) = (600900034323:ℝ)/288244716376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2756
  · change lowerPayment 2757 ≤ lowerValue ((point 2 split 4096 2757+point 2 split 4096 2758)/2)
    have hp : lowerPayment 2757 = (299877194357:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2757+point 2 split 4096 2758)/2 = (99633573:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((99633573:ℝ)/33751040)/ClassicalSixthBranch.v ((99633573:ℝ)/33751040) = (600822720649:ℝ)/288196708488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2757
  · change lowerPayment 2758 ≤ lowerValue ((point 2 split 4096 2758+point 2 split 4096 2759)/2)
    have hp : lowerPayment 2758 = (299965000919:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2758+point 2 split 4096 2759)/2 = (498226127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((498226127:ℝ)/168755200)/ClassicalSixthBranch.v ((498226127:ℝ)/168755200) = (24029816279:ℝ)/11525948024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2758
  · change lowerPayment 2759 ≤ lowerValue ((point 2 split 4096 2759+point 2 split 4096 2760)/2)
    have hp : lowerPayment 2759 = (300052808719:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2759+point 2 split 4096 2760)/2 = (498284389:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((498284389:ℝ)/168755200)/ClassicalSixthBranch.v ((498284389:ℝ)/168755200) = (600668093301:ℝ)/288100692712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2759
  · change lowerPayment 2760 ≤ lowerValue ((point 2 split 4096 2760+point 2 split 4096 2761)/2)
    have hp : lowerPayment 2760 = (300140617771:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2760+point 2 split 4096 2761)/2 = (498342651:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((498342651:ℝ)/168755200)/ClassicalSixthBranch.v ((498342651:ℝ)/168755200) = (600590779627:ℝ)/288052684824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2760
  · change lowerPayment 2761 ≤ lowerValue ((point 2 split 4096 2761+point 2 split 4096 2762)/2)
    have hp : lowerPayment 2761 = (300228428089:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2761+point 2 split 4096 2762)/2 = (498400913:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((498400913:ℝ)/168755200)/ClassicalSixthBranch.v ((498400913:ℝ)/168755200) = (600513465953:ℝ)/288004676936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2761
  · change lowerPayment 2762 ≤ lowerValue ((point 2 split 4096 2762+point 2 split 4096 2763)/2)
    have hp : lowerPayment 2762 = (300316239688:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2762+point 2 split 4096 2763)/2 = (19938367:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19938367:ℝ)/6750208)/ClassicalSixthBranch.v ((19938367:ℝ)/6750208) = (600436152279:ℝ)/287956669048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2762
  · change lowerPayment 2763 ≤ lowerValue ((point 2 split 4096 2763+point 2 split 4096 2764)/2)
    have hp : lowerPayment 2763 = (300404052580:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2763+point 2 split 4096 2764)/2 = (498517437:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((498517437:ℝ)/168755200)/ClassicalSixthBranch.v ((498517437:ℝ)/168755200) = (120071767721:ℝ)/57581732232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2763
  · change lowerPayment 2764 ≤ lowerValue ((point 2 split 4096 2764+point 2 split 4096 2765)/2)
    have hp : lowerPayment 2764 = (300491866782:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2764+point 2 split 4096 2765)/2 = (498575699:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((498575699:ℝ)/168755200)/ClassicalSixthBranch.v ((498575699:ℝ)/168755200) = (600281524931:ℝ)/287860653272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2764
  · change lowerPayment 2765 ≤ lowerValue ((point 2 split 4096 2765+point 2 split 4096 2766)/2)
    have hp : lowerPayment 2765 = (300579682305:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2765+point 2 split 4096 2766)/2 = (498633961:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((498633961:ℝ)/168755200)/ClassicalSixthBranch.v ((498633961:ℝ)/168755200) = (600204211257:ℝ)/287812645384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2765
  · change lowerPayment 2766 ≤ lowerValue ((point 2 split 4096 2766+point 2 split 4096 2767)/2)
    have hp : lowerPayment 2766 = (300667499166:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2766+point 2 split 4096 2767)/2 = (498692223:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((498692223:ℝ)/168755200)/ClassicalSixthBranch.v ((498692223:ℝ)/168755200) = (600126897583:ℝ)/287764637496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2766
  · change lowerPayment 2767 ≤ lowerValue ((point 2 split 4096 2767+point 2 split 4096 2768)/2)
    have hp : lowerPayment 2767 = (300755317377:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2767+point 2 split 4096 2768)/2 = (99750097:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((99750097:ℝ)/33751040)/ClassicalSixthBranch.v ((99750097:ℝ)/33751040) = (600049583909:ℝ)/287716629608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2767
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_172
