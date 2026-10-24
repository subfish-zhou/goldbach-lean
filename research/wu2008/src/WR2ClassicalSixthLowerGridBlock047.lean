import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints047
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_047 (j : Fin 16) : lowerPayment (16*47+j.val) ≤
    lowerValue ((point 2 split 4096 (16*47+j.val)+point 2 split 4096 (16*47+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 752 ≤ lowerValue ((point 2 split 4096 752+point 2 split 4096 753)/2)
    have hp : lowerPayment 752 = (104771403453:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 752+point 2 split 4096 753)/2 = (76270511:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((76270511:ℝ)/33751040)/ClassicalSixthBranch.v ((76270511:ℝ)/33751040) = (755836637019:ℝ)/384452523928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_752
  · change lowerPayment 753 ≤ lowerValue ((point 2 split 4096 753+point 2 split 4096 754)/2)
    have hp : lowerPayment 753 = (104891467208:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 753+point 2 split 4096 754)/2 = (381410817:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((381410817:ℝ)/168755200)/ClassicalSixthBranch.v ((381410817:ℝ)/168755200) = (151151864669:ℝ)/76880903208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_753
  · change lowerPayment 754 ≤ lowerValue ((point 2 split 4096 754+point 2 split 4096 755)/2)
    have hp : lowerPayment 754 = (105011490816:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 754+point 2 split 4096 755)/2 = (381469079:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((381469079:ℝ)/168755200)/ClassicalSixthBranch.v ((381469079:ℝ)/168755200) = (755682009671:ℝ)/384356508152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_754
  · change lowerPayment 755 ≤ lowerValue ((point 2 split 4096 755+point 2 split 4096 756)/2)
    have hp : lowerPayment 755 = (105131474313:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 755+point 2 split 4096 756)/2 = (381527341:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((381527341:ℝ)/168755200)/ClassicalSixthBranch.v ((381527341:ℝ)/168755200) = (755604695997:ℝ)/384308500264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_755
  · change lowerPayment 756 ≤ lowerValue ((point 2 split 4096 756+point 2 split 4096 757)/2)
    have hp : lowerPayment 756 = (105251417735:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 756+point 2 split 4096 757)/2 = (381585603:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((381585603:ℝ)/168755200)/ClassicalSixthBranch.v ((381585603:ℝ)/168755200) = (755527382323:ℝ)/384260492376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_756
  · change lowerPayment 757 ≤ lowerValue ((point 2 split 4096 757+point 2 split 4096 758)/2)
    have hp : lowerPayment 757 = (105371321118:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 757+point 2 split 4096 758)/2 = (76328773:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((76328773:ℝ)/33751040)/ClassicalSixthBranch.v ((76328773:ℝ)/33751040) = (755450068649:ℝ)/384212484488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_757
  · change lowerPayment 758 ≤ lowerValue ((point 2 split 4096 758+point 2 split 4096 759)/2)
    have hp : lowerPayment 758 = (105491184497:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 758+point 2 split 4096 759)/2 = (381702127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((381702127:ℝ)/168755200)/ClassicalSixthBranch.v ((381702127:ℝ)/168755200) = (30214910199:ℝ)/15366579064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_758
  · change lowerPayment 759 ≤ lowerValue ((point 2 split 4096 759+point 2 split 4096 760)/2)
    have hp : lowerPayment 759 = (105611007909:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 759+point 2 split 4096 760)/2 = (381760389:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((381760389:ℝ)/168755200)/ClassicalSixthBranch.v ((381760389:ℝ)/168755200) = (755295441301:ℝ)/384116468712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_759
  · change lowerPayment 760 ≤ lowerValue ((point 2 split 4096 760+point 2 split 4096 761)/2)
    have hp : lowerPayment 760 = (105730791388:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 760+point 2 split 4096 761)/2 = (381818651:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((381818651:ℝ)/168755200)/ClassicalSixthBranch.v ((381818651:ℝ)/168755200) = (755218127627:ℝ)/384068460824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_760
  · change lowerPayment 761 ≤ lowerValue ((point 2 split 4096 761+point 2 split 4096 762)/2)
    have hp : lowerPayment 761 = (105850534972:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 761+point 2 split 4096 762)/2 = (381876913:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((381876913:ℝ)/168755200)/ClassicalSixthBranch.v ((381876913:ℝ)/168755200) = (755140813953:ℝ)/384020452936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_761
  · change lowerPayment 762 ≤ lowerValue ((point 2 split 4096 762+point 2 split 4096 763)/2)
    have hp : lowerPayment 762 = (105970238695:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 762+point 2 split 4096 763)/2 = (15277407:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((15277407:ℝ)/6750208)/ClassicalSixthBranch.v ((15277407:ℝ)/6750208) = (755063500279:ℝ)/383972445048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_762
  · change lowerPayment 763 ≤ lowerValue ((point 2 split 4096 763+point 2 split 4096 764)/2)
    have hp : lowerPayment 763 = (106089902593:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 763+point 2 split 4096 764)/2 = (381993437:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((381993437:ℝ)/168755200)/ClassicalSixthBranch.v ((381993437:ℝ)/168755200) = (150997237321:ℝ)/76784887432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_763
  · change lowerPayment 764 ≤ lowerValue ((point 2 split 4096 764+point 2 split 4096 765)/2)
    have hp : lowerPayment 764 = (106209526702:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 764+point 2 split 4096 765)/2 = (382051699:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((382051699:ℝ)/168755200)/ClassicalSixthBranch.v ((382051699:ℝ)/168755200) = (754908872931:ℝ)/383876429272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_764
  · change lowerPayment 765 ≤ lowerValue ((point 2 split 4096 765+point 2 split 4096 766)/2)
    have hp : lowerPayment 765 = (106329111058:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 765+point 2 split 4096 766)/2 = (382109961:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((382109961:ℝ)/168755200)/ClassicalSixthBranch.v ((382109961:ℝ)/168755200) = (754831559257:ℝ)/383828421384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_765
  · change lowerPayment 766 ≤ lowerValue ((point 2 split 4096 766+point 2 split 4096 767)/2)
    have hp : lowerPayment 766 = (106448655695:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 766+point 2 split 4096 767)/2 = (382168223:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((382168223:ℝ)/168755200)/ClassicalSixthBranch.v ((382168223:ℝ)/168755200) = (754754245583:ℝ)/383780413496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_766
  · change lowerPayment 767 ≤ lowerValue ((point 2 split 4096 767+point 2 split 4096 768)/2)
    have hp : lowerPayment 767 = (106568160651:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 767+point 2 split 4096 768)/2 = (76445297:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((76445297:ℝ)/33751040)/ClassicalSixthBranch.v ((76445297:ℝ)/33751040) = (754676931909:ℝ)/383732405608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_767
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_047
