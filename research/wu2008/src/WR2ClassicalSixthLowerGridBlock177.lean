import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints177
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_177 (j : Fin 16) : lowerPayment (16*177+j.val) ≤
    lowerValue ((point 2 split 4096 (16*177+j.val)+point 2 split 4096 (16*177+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2832 ≤ lowerValue ((point 2 split 4096 2832+point 2 split 4096 2833)/2)
    have hp : lowerPayment 2832 = (306467075431:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2832+point 2 split 4096 2833)/2 = (975801:ℝ)/327680 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((975801:ℝ)/327680)/ClassicalSixthBranch.v ((975801:ℝ)/327680) = (5776933933:ℝ)/2763069096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2832
  · change lowerPayment 2833 ≤ lowerValue ((point 2 split 4096 2833+point 2 split 4096 2834)/2)
    have hp : lowerPayment 2833 = (306555014025:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2833+point 2 split 4096 2834)/2 = (502595777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((502595777:ℝ)/168755200)/ClassicalSixthBranch.v ((502595777:ℝ)/168755200) = (23797875257:ℝ)/11381924360 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2833
  · change lowerPayment 2834 ≤ lowerValue ((point 2 split 4096 2834+point 2 split 4096 2835)/2)
    have hp : lowerPayment 2834 = (306642954916:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2834+point 2 split 4096 2835)/2 = (502654039:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((502654039:ℝ)/168755200)/ClassicalSixthBranch.v ((502654039:ℝ)/168755200) = (594869567751:ℝ)/284500101112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2834
  · change lowerPayment 2835 ≤ lowerValue ((point 2 split 4096 2835+point 2 split 4096 2836)/2)
    have hp : lowerPayment 2835 = (306730898118:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2835+point 2 split 4096 2836)/2 = (502712301:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((502712301:ℝ)/168755200)/ClassicalSixthBranch.v ((502712301:ℝ)/168755200) = (594792254077:ℝ)/284452093224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2835
  · change lowerPayment 2836 ≤ lowerValue ((point 2 split 4096 2836+point 2 split 4096 2837)/2)
    have hp : lowerPayment 2836 = (306818843645:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2836+point 2 split 4096 2837)/2 = (502770563:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((502770563:ℝ)/168755200)/ClassicalSixthBranch.v ((502770563:ℝ)/168755200) = (594714940403:ℝ)/284404085336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2836
  · change lowerPayment 2837 ≤ lowerValue ((point 2 split 4096 2837+point 2 split 4096 2838)/2)
    have hp : lowerPayment 2837 = (306906791511:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2837+point 2 split 4096 2838)/2 = (20113153:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((20113153:ℝ)/6750208)/ClassicalSixthBranch.v ((20113153:ℝ)/6750208) = (594637626729:ℝ)/284356077448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2837
  · change lowerPayment 2838 ≤ lowerValue ((point 2 split 4096 2838+point 2 split 4096 2839)/2)
    have hp : lowerPayment 2838 = (306994741730:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2838+point 2 split 4096 2839)/2 = (502887087:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((502887087:ℝ)/168755200)/ClassicalSixthBranch.v ((502887087:ℝ)/168755200) = (118912062611:ℝ)/56861613912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2838
  · change lowerPayment 2839 ≤ lowerValue ((point 2 split 4096 2839+point 2 split 4096 2840)/2)
    have hp : lowerPayment 2839 = (307082694316:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2839+point 2 split 4096 2840)/2 = (502945349:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((502945349:ℝ)/168755200)/ClassicalSixthBranch.v ((502945349:ℝ)/168755200) = (594482999381:ℝ)/284260061672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2839
  · change lowerPayment 2840 ≤ lowerValue ((point 2 split 4096 2840+point 2 split 4096 2841)/2)
    have hp : lowerPayment 2840 = (307170649284:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2840+point 2 split 4096 2841)/2 = (503003611:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((503003611:ℝ)/168755200)/ClassicalSixthBranch.v ((503003611:ℝ)/168755200) = (594405685707:ℝ)/284212053784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2840
  · change lowerPayment 2841 ≤ lowerValue ((point 2 split 4096 2841+point 2 split 4096 2842)/2)
    have hp : lowerPayment 2841 = (307258606647:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2841+point 2 split 4096 2842)/2 = (503061873:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((503061873:ℝ)/168755200)/ClassicalSixthBranch.v ((503061873:ℝ)/168755200) = (594328372033:ℝ)/284164045896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2841
  · change lowerPayment 2842 ≤ lowerValue ((point 2 split 4096 2842+point 2 split 4096 2843)/2)
    have hp : lowerPayment 2842 = (307346566420:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2842+point 2 split 4096 2843)/2 = (100624027:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((100624027:ℝ)/33751040)/ClassicalSixthBranch.v ((100624027:ℝ)/33751040) = (594251058359:ℝ)/284116038008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2842
  · change lowerPayment 2843 ≤ lowerValue ((point 2 split 4096 2843+point 2 split 4096 2844)/2)
    have hp : lowerPayment 2843 = (307434528617:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2843+point 2 split 4096 2844)/2 = (503178397:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((503178397:ℝ)/168755200)/ClassicalSixthBranch.v ((503178397:ℝ)/168755200) = (118834748937:ℝ)/56813606024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2843
  · change lowerPayment 2844 ≤ lowerValue ((point 2 split 4096 2844+point 2 split 4096 2845)/2)
    have hp : lowerPayment 2844 = (307522493252:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2844+point 2 split 4096 2845)/2 = (503236659:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((503236659:ℝ)/168755200)/ClassicalSixthBranch.v ((503236659:ℝ)/168755200) = (594096431011:ℝ)/284020022232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2844
  · change lowerPayment 2845 ≤ lowerValue ((point 2 split 4096 2845+point 2 split 4096 2846)/2)
    have hp : lowerPayment 2845 = (307610460338:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2845+point 2 split 4096 2846)/2 = (503294921:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((503294921:ℝ)/168755200)/ClassicalSixthBranch.v ((503294921:ℝ)/168755200) = (594019117337:ℝ)/283972014344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2845
  · change lowerPayment 2846 ≤ lowerValue ((point 2 split 4096 2846+point 2 split 4096 2847)/2)
    have hp : lowerPayment 2846 = (307698429890:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2846+point 2 split 4096 2847)/2 = (503353183:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((503353183:ℝ)/168755200)/ClassicalSixthBranch.v ((503353183:ℝ)/168755200) = (593941803663:ℝ)/283924006456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2846
  · change lowerPayment 2847 ≤ lowerValue ((point 2 split 4096 2847+point 2 split 4096 2848)/2)
    have hp : lowerPayment 2847 = (307786401923:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2847+point 2 split 4096 2848)/2 = (100682289:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((100682289:ℝ)/33751040)/ClassicalSixthBranch.v ((100682289:ℝ)/33751040) = (593864489989:ℝ)/283875998568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2847
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_177
