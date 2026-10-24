import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints127
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_127 (j : Fin 16) : lowerPayment (16*127+j.val) ≤
    lowerValue ((point 2 split 4096 (16*127+j.val)+point 2 split 4096 (16*127+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2032 ≤ lowerValue ((point 2 split 4096 2032+point 2 split 4096 2033)/2)
    have hp : lowerPayment 2032 = (235622255890:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2032+point 2 split 4096 2033)/2 = (91185583:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((91185583:ℝ)/33751040)/ClassicalSixthBranch.v ((91185583:ℝ)/33751040) = (656875134299:ℝ)/323002427288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2032
  · change lowerPayment 2033 ≤ lowerValue ((point 2 split 4096 2033+point 2 split 4096 2034)/2)
    have hp : lowerPayment 2033 = (235713008165:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2033+point 2 split 4096 2034)/2 = (455986177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((455986177:ℝ)/168755200)/ClassicalSixthBranch.v ((455986177:ℝ)/168755200) = (26271912825:ℝ)/12918176776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2033
  · change lowerPayment 2034 ≤ lowerValue ((point 2 split 4096 2034+point 2 split 4096 2035)/2)
    have hp : lowerPayment 2034 = (235803750807:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2034+point 2 split 4096 2035)/2 = (456044439:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((456044439:ℝ)/168755200)/ClassicalSixthBranch.v ((456044439:ℝ)/168755200) = (656720506951:ℝ)/322906411512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2034
  · change lowerPayment 2035 ≤ lowerValue ((point 2 split 4096 2035+point 2 split 4096 2036)/2)
    have hp : lowerPayment 2035 = (235894483833:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2035+point 2 split 4096 2036)/2 = (456102701:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((456102701:ℝ)/168755200)/ClassicalSixthBranch.v ((456102701:ℝ)/168755200) = (656643193277:ℝ)/322858403624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2035
  · change lowerPayment 2036 ≤ lowerValue ((point 2 split 4096 2036+point 2 split 4096 2037)/2)
    have hp : lowerPayment 2036 = (235985207259:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2036+point 2 split 4096 2037)/2 = (456160963:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((456160963:ℝ)/168755200)/ClassicalSixthBranch.v ((456160963:ℝ)/168755200) = (656565879603:ℝ)/322810395736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2036
  · change lowerPayment 2037 ≤ lowerValue ((point 2 split 4096 2037+point 2 split 4096 2038)/2)
    have hp : lowerPayment 2037 = (236075921103:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2037+point 2 split 4096 2038)/2 = (18248769:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((18248769:ℝ)/6750208)/ClassicalSixthBranch.v ((18248769:ℝ)/6750208) = (656488565929:ℝ)/322762387848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2037
  · change lowerPayment 2038 ≤ lowerValue ((point 2 split 4096 2038+point 2 split 4096 2039)/2)
    have hp : lowerPayment 2038 = (236166625380:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2038+point 2 split 4096 2039)/2 = (456277487:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((456277487:ℝ)/168755200)/ClassicalSixthBranch.v ((456277487:ℝ)/168755200) = (131282250451:ℝ)/64542875992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2038
  · change lowerPayment 2039 ≤ lowerValue ((point 2 split 4096 2039+point 2 split 4096 2040)/2)
    have hp : lowerPayment 2039 = (236257320107:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2039+point 2 split 4096 2040)/2 = (456335749:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((456335749:ℝ)/168755200)/ClassicalSixthBranch.v ((456335749:ℝ)/168755200) = (656333938581:ℝ)/322666372072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2039
  · change lowerPayment 2040 ≤ lowerValue ((point 2 split 4096 2040+point 2 split 4096 2041)/2)
    have hp : lowerPayment 2040 = (236348005301:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2040+point 2 split 4096 2041)/2 = (456394011:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((456394011:ℝ)/168755200)/ClassicalSixthBranch.v ((456394011:ℝ)/168755200) = (656256624907:ℝ)/322618364184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2040
  · change lowerPayment 2041 ≤ lowerValue ((point 2 split 4096 2041+point 2 split 4096 2042)/2)
    have hp : lowerPayment 2041 = (236438680978:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2041+point 2 split 4096 2042)/2 = (456452273:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((456452273:ℝ)/168755200)/ClassicalSixthBranch.v ((456452273:ℝ)/168755200) = (656179311233:ℝ)/322570356296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2041
  · change lowerPayment 2042 ≤ lowerValue ((point 2 split 4096 2042+point 2 split 4096 2043)/2)
    have hp : lowerPayment 2042 = (236529347154:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2042+point 2 split 4096 2043)/2 = (91302107:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((91302107:ℝ)/33751040)/ClassicalSixthBranch.v ((91302107:ℝ)/33751040) = (656101997559:ℝ)/322522348408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2042
  · change lowerPayment 2043 ≤ lowerValue ((point 2 split 4096 2043+point 2 split 4096 2044)/2)
    have hp : lowerPayment 2043 = (236620003846:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2043+point 2 split 4096 2044)/2 = (456568797:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((456568797:ℝ)/168755200)/ClassicalSixthBranch.v ((456568797:ℝ)/168755200) = (131204936777:ℝ)/64494868104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2043
  · change lowerPayment 2044 ≤ lowerValue ((point 2 split 4096 2044+point 2 split 4096 2045)/2)
    have hp : lowerPayment 2044 = (236710651070:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2044+point 2 split 4096 2045)/2 = (456627059:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((456627059:ℝ)/168755200)/ClassicalSixthBranch.v ((456627059:ℝ)/168755200) = (655947370211:ℝ)/322426332632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2044
  · change lowerPayment 2045 ≤ lowerValue ((point 2 split 4096 2045+point 2 split 4096 2046)/2)
    have hp : lowerPayment 2045 = (236801288844:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2045+point 2 split 4096 2046)/2 = (456685321:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((456685321:ℝ)/168755200)/ClassicalSixthBranch.v ((456685321:ℝ)/168755200) = (655870056537:ℝ)/322378324744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2045
  · change lowerPayment 2046 ≤ lowerValue ((point 2 split 4096 2046+point 2 split 4096 2047)/2)
    have hp : lowerPayment 2046 = (236891917182:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2046+point 2 split 4096 2047)/2 = (456743583:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((456743583:ℝ)/168755200)/ClassicalSixthBranch.v ((456743583:ℝ)/168755200) = (655792742863:ℝ)/322330316856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2046
  · change lowerPayment 2047 ≤ lowerValue ((point 2 split 4096 2047+point 2 split 4096 2048)/2)
    have hp : lowerPayment 2047 = (236982536102:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2047+point 2 split 4096 2048)/2 = (91360369:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((91360369:ℝ)/33751040)/ClassicalSixthBranch.v ((91360369:ℝ)/33751040) = (655715429189:ℝ)/322282308968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2047
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_127
