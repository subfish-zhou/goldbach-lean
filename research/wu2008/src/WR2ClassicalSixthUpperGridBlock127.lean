import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints127
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_127 (j : Fin 16) : upperPayment (16*127+j.val) ≤
    upperValue ((point split endpoint 4096 (16*127+j.val)+point split endpoint 4096 (16*127+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2032 ≤ upperValue ((point split endpoint 4096 2032+point split endpoint 4096 2033)/2)
    have hp : upperPayment 2032 = (270812454304:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2032+point split endpoint 4096 2033)/2 = (627268927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627268927:ℝ)/168755200)*ClassicalSixthBranch.v ((627268927:ℝ)/168755200)/ClassicalSixthBranch.r = (114268417543185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2032
  · change upperPayment 2033 ≤ upperValue ((point split endpoint 4096 2033+point split endpoint 4096 2034)/2)
    have hp : upperPayment 2033 = (270713069693:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2033+point split endpoint 4096 2034)/2 = (627294077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627294077:ℝ)/168755200)*ClassicalSixthBranch.v ((627294077:ℝ)/168755200)/ClassicalSixthBranch.r = (114246515164697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2033
  · change upperPayment 2034 ≤ upperValue ((point split endpoint 4096 2034+point split endpoint 4096 2035)/2)
    have hp : upperPayment 2034 = (270613658689:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2034+point split endpoint 4096 2035)/2 = (627319227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627319227:ℝ)/168755200)*ClassicalSixthBranch.v ((627319227:ℝ)/168755200)/ClassicalSixthBranch.r = (114224614810281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2034
  · change upperPayment 2035 ≤ upperValue ((point split endpoint 4096 2035+point split endpoint 4096 2036)/2)
    have hp : upperPayment 2035 = (270514221288:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2035+point split endpoint 4096 2036)/2 = (627344377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627344377:ℝ)/168755200)*ClassicalSixthBranch.v ((627344377:ℝ)/168755200)/ClassicalSixthBranch.r = (114202716479937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2035
  · change upperPayment 2036 ≤ upperValue ((point split endpoint 4096 2036+point split endpoint 4096 2037)/2)
    have hp : upperPayment 2036 = (270414757483:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2036+point split endpoint 4096 2037)/2 = (627369527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627369527:ℝ)/168755200)*ClassicalSixthBranch.v ((627369527:ℝ)/168755200)/ClassicalSixthBranch.r = (114180820173665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2036
  · change upperPayment 2037 ≤ upperValue ((point split endpoint 4096 2037+point split endpoint 4096 2038)/2)
    have hp : upperPayment 2037 = (270315267270:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2037+point split endpoint 4096 2038)/2 = (627394677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627394677:ℝ)/168755200)*ClassicalSixthBranch.v ((627394677:ℝ)/168755200)/ClassicalSixthBranch.r = (114158925891465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2037
  · change upperPayment 2038 ≤ upperValue ((point split endpoint 4096 2038+point split endpoint 4096 2039)/2)
    have hp : upperPayment 2038 = (270215750643:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2038+point split endpoint 4096 2039)/2 = (627419827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627419827:ℝ)/168755200)*ClassicalSixthBranch.v ((627419827:ℝ)/168755200)/ClassicalSixthBranch.r = (114137033633337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2038
  · change upperPayment 2039 ≤ upperValue ((point split endpoint 4096 2039+point split endpoint 4096 2040)/2)
    have hp : upperPayment 2039 = (270116207597:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2039+point split endpoint 4096 2040)/2 = (627444977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627444977:ℝ)/168755200)*ClassicalSixthBranch.v ((627444977:ℝ)/168755200)/ClassicalSixthBranch.r = (114115143399281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2039
  · change upperPayment 2040 ≤ upperValue ((point split endpoint 4096 2040+point split endpoint 4096 2041)/2)
    have hp : upperPayment 2040 = (270016638128:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2040+point split endpoint 4096 2041)/2 = (627470127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627470127:ℝ)/168755200)*ClassicalSixthBranch.v ((627470127:ℝ)/168755200)/ClassicalSixthBranch.r = (114093255189297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2040
  · change upperPayment 2041 ≤ upperValue ((point split endpoint 4096 2041+point split endpoint 4096 2042)/2)
    have hp : upperPayment 2041 = (269917042228:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2041+point split endpoint 4096 2042)/2 = (627495277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627495277:ℝ)/168755200)*ClassicalSixthBranch.v ((627495277:ℝ)/168755200)/ClassicalSixthBranch.r = (114071369003385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2041
  · change upperPayment 2042 ≤ upperValue ((point split endpoint 4096 2042+point split endpoint 4096 2043)/2)
    have hp : upperPayment 2042 = (269817419894:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2042+point split endpoint 4096 2043)/2 = (627520427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627520427:ℝ)/168755200)*ClassicalSixthBranch.v ((627520427:ℝ)/168755200)/ClassicalSixthBranch.r = (114049484841545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2042
  · change upperPayment 2043 ≤ upperValue ((point split endpoint 4096 2043+point split endpoint 4096 2044)/2)
    have hp : upperPayment 2043 = (269717771120:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2043+point split endpoint 4096 2044)/2 = (627545577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627545577:ℝ)/168755200)*ClassicalSixthBranch.v ((627545577:ℝ)/168755200)/ClassicalSixthBranch.r = (114027602703777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2043
  · change upperPayment 2044 ≤ upperValue ((point split endpoint 4096 2044+point split endpoint 4096 2045)/2)
    have hp : upperPayment 2044 = (269618095901:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2044+point split endpoint 4096 2045)/2 = (627570727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627570727:ℝ)/168755200)*ClassicalSixthBranch.v ((627570727:ℝ)/168755200)/ClassicalSixthBranch.r = (114005722590081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2044
  · change upperPayment 2045 ≤ upperValue ((point split endpoint 4096 2045+point split endpoint 4096 2046)/2)
    have hp : upperPayment 2045 = (269518394232:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2045+point split endpoint 4096 2046)/2 = (627595877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627595877:ℝ)/168755200)*ClassicalSixthBranch.v ((627595877:ℝ)/168755200)/ClassicalSixthBranch.r = (113983844500457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2045
  · change upperPayment 2046 ≤ upperValue ((point split endpoint 4096 2046+point split endpoint 4096 2047)/2)
    have hp : upperPayment 2046 = (269418666107:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2046+point split endpoint 4096 2047)/2 = (627621027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627621027:ℝ)/168755200)*ClassicalSixthBranch.v ((627621027:ℝ)/168755200)/ClassicalSixthBranch.r = (113961968434905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2046
  · change upperPayment 2047 ≤ upperValue ((point split endpoint 4096 2047+point split endpoint 4096 2048)/2)
    have hp : upperPayment 2047 = (269318911520:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2047+point split endpoint 4096 2048)/2 = (627646177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627646177:ℝ)/168755200)*ClassicalSixthBranch.v ((627646177:ℝ)/168755200)/ClassicalSixthBranch.r = (113940094393425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2047
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_127
