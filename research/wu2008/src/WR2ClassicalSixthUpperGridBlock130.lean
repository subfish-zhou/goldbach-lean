import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints130
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_130 (j : Fin 16) : upperPayment (16*130+j.val) ≤
    upperValue ((point split endpoint 4096 (16*130+j.val)+point split endpoint 4096 (16*130+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2080 ≤ upperValue ((point split endpoint 4096 2080+point split endpoint 4096 2081)/2)
    have hp : upperPayment 2080 = (266012130925:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2080+point split endpoint 4096 2081)/2 = (628476127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628476127:ℝ)/168755200)*ClassicalSixthBranch.v ((628476127:ℝ)/168755200)/ClassicalSixthBranch.r = (113219386528977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2080
  · change upperPayment 2081 ≤ upperValue ((point split endpoint 4096 2081+point split endpoint 4096 2082)/2)
    have hp : upperPayment 2081 = (265911473513:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2081+point split endpoint 4096 2082)/2 = (628501277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628501277:ℝ)/168755200)*ClassicalSixthBranch.v ((628501277:ℝ)/168755200)/ClassicalSixthBranch.r = (113197581305945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2081
  · change upperPayment 2082 ≤ upperValue ((point split endpoint 4096 2082+point split endpoint 4096 2083)/2)
    have hp : upperPayment 2082 = (265810789455:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2082+point split endpoint 4096 2083)/2 = (628526427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628526427:ℝ)/168755200)*ClassicalSixthBranch.v ((628526427:ℝ)/168755200)/ClassicalSixthBranch.r = (113175778106985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2082
  · change upperPayment 2083 ≤ upperValue ((point split endpoint 4096 2083+point split endpoint 4096 2084)/2)
    have hp : upperPayment 2083 = (265710078744:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2083+point split endpoint 4096 2084)/2 = (628551577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628551577:ℝ)/168755200)*ClassicalSixthBranch.v ((628551577:ℝ)/168755200)/ClassicalSixthBranch.r = (113153976932097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2083
  · change upperPayment 2084 ≤ upperValue ((point split endpoint 4096 2084+point split endpoint 4096 2085)/2)
    have hp : upperPayment 2084 = (265609341375:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2084+point split endpoint 4096 2085)/2 = (628576727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628576727:ℝ)/168755200)*ClassicalSixthBranch.v ((628576727:ℝ)/168755200)/ClassicalSixthBranch.r = (113132177781281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2084
  · change upperPayment 2085 ≤ upperValue ((point split endpoint 4096 2085+point split endpoint 4096 2086)/2)
    have hp : upperPayment 2085 = (265508577344:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2085+point split endpoint 4096 2086)/2 = (628601877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628601877:ℝ)/168755200)*ClassicalSixthBranch.v ((628601877:ℝ)/168755200)/ClassicalSixthBranch.r = (113110380654537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2085
  · change upperPayment 2086 ≤ upperValue ((point split endpoint 4096 2086+point split endpoint 4096 2087)/2)
    have hp : upperPayment 2086 = (265407786644:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2086+point split endpoint 4096 2087)/2 = (628627027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628627027:ℝ)/168755200)*ClassicalSixthBranch.v ((628627027:ℝ)/168755200)/ClassicalSixthBranch.r = (113088585551865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2086
  · change upperPayment 2087 ≤ upperValue ((point split endpoint 4096 2087+point split endpoint 4096 2088)/2)
    have hp : upperPayment 2087 = (265306969271:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2087+point split endpoint 4096 2088)/2 = (628652177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628652177:ℝ)/168755200)*ClassicalSixthBranch.v ((628652177:ℝ)/168755200)/ClassicalSixthBranch.r = (1097735849255:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2087
  · change upperPayment 2088 ≤ upperValue ((point split endpoint 4096 2088+point split endpoint 4096 2089)/2)
    have hp : upperPayment 2088 = (265206125219:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2088+point split endpoint 4096 2089)/2 = (628677327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628677327:ℝ)/168755200)*ClassicalSixthBranch.v ((628677327:ℝ)/168755200)/ClassicalSixthBranch.r = (113045001418737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2088
  · change upperPayment 2089 ≤ upperValue ((point split endpoint 4096 2089+point split endpoint 4096 2090)/2)
    have hp : upperPayment 2089 = (265105254482:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2089+point split endpoint 4096 2090)/2 = (628702477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628702477:ℝ)/168755200)*ClassicalSixthBranch.v ((628702477:ℝ)/168755200)/ClassicalSixthBranch.r = (113023212388281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2089
  · change upperPayment 2090 ≤ upperValue ((point split endpoint 4096 2090+point split endpoint 4096 2091)/2)
    have hp : upperPayment 2090 = (265004357056:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2090+point split endpoint 4096 2091)/2 = (628727627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628727627:ℝ)/168755200)*ClassicalSixthBranch.v ((628727627:ℝ)/168755200)/ClassicalSixthBranch.r = (113001425381897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2090
  · change upperPayment 2091 ≤ upperValue ((point split endpoint 4096 2091+point split endpoint 4096 2092)/2)
    have hp : upperPayment 2091 = (264903432935:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2091+point split endpoint 4096 2092)/2 = (628752777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628752777:ℝ)/168755200)*ClassicalSixthBranch.v ((628752777:ℝ)/168755200)/ClassicalSixthBranch.r = (112979640399585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2091
  · change upperPayment 2092 ≤ upperValue ((point split endpoint 4096 2092+point split endpoint 4096 2093)/2)
    have hp : upperPayment 2092 = (264802482113:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2092+point split endpoint 4096 2093)/2 = (628777927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628777927:ℝ)/168755200)*ClassicalSixthBranch.v ((628777927:ℝ)/168755200)/ClassicalSixthBranch.r = (112957857441345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2092
  · change upperPayment 2093 ≤ upperValue ((point split endpoint 4096 2093+point split endpoint 4096 2094)/2)
    have hp : upperPayment 2093 = (264701504586:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2093+point split endpoint 4096 2094)/2 = (628803077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628803077:ℝ)/168755200)*ClassicalSixthBranch.v ((628803077:ℝ)/168755200)/ClassicalSixthBranch.r = (112936076507177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2093
  · change upperPayment 2094 ≤ upperValue ((point split endpoint 4096 2094+point split endpoint 4096 2095)/2)
    have hp : upperPayment 2094 = (264600500347:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2094+point split endpoint 4096 2095)/2 = (628828227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628828227:ℝ)/168755200)*ClassicalSixthBranch.v ((628828227:ℝ)/168755200)/ClassicalSixthBranch.r = (112914297597081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2094
  · change upperPayment 2095 ≤ upperValue ((point split endpoint 4096 2095+point split endpoint 4096 2096)/2)
    have hp : upperPayment 2095 = (264499469392:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2095+point split endpoint 4096 2096)/2 = (628853377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628853377:ℝ)/168755200)*ClassicalSixthBranch.v ((628853377:ℝ)/168755200)/ClassicalSixthBranch.r = (112892520711057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2095
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_130
