import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints132
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_132 (j : Fin 16) : upperPayment (16*132+j.val) ≤
    upperValue ((point split endpoint 4096 (16*132+j.val)+point split endpoint 4096 (16*132+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2112 ≤ upperValue ((point split endpoint 4096 2112+point split endpoint 4096 2113)/2)
    have hp : upperPayment 2112 = (262777850308:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2112+point split endpoint 4096 2113)/2 = (629280927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629280927:ℝ)/168755200)*ClassicalSixthBranch.v ((629280927:ℝ)/168755200)/ClassicalSixthBranch.r = (112522623331665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2112
  · change upperPayment 2113 ≤ upperValue ((point split endpoint 4096 2113+point split endpoint 4096 2114)/2)
    have hp : upperPayment 2113 = (262676337534:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2113+point split endpoint 4096 2114)/2 = (629306077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629306077:ℝ)/168755200)*ClassicalSixthBranch.v ((629306077:ℝ)/168755200)/ClassicalSixthBranch.r = (112500882878937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2113
  · change upperPayment 2114 ≤ upperValue ((point split endpoint 4096 2114+point split endpoint 4096 2115)/2)
    have hp : upperPayment 2114 = (262574797940:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2114+point split endpoint 4096 2115)/2 = (629331227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629331227:ℝ)/168755200)*ClassicalSixthBranch.v ((629331227:ℝ)/168755200)/ClassicalSixthBranch.r = (112479144450281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2114
  · change upperPayment 2115 ≤ upperValue ((point split endpoint 4096 2115+point split endpoint 4096 2116)/2)
    have hp : upperPayment 2115 = (262473231523:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2115+point split endpoint 4096 2116)/2 = (629356377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629356377:ℝ)/168755200)*ClassicalSixthBranch.v ((629356377:ℝ)/168755200)/ClassicalSixthBranch.r = (112457408045697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2115
  · change upperPayment 2116 ≤ upperValue ((point split endpoint 4096 2116+point split endpoint 4096 2117)/2)
    have hp : upperPayment 2116 = (262371638275:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2116+point split endpoint 4096 2117)/2 = (629381527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629381527:ℝ)/168755200)*ClassicalSixthBranch.v ((629381527:ℝ)/168755200)/ClassicalSixthBranch.r = (112435673665185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2116
  · change upperPayment 2117 ≤ upperValue ((point split endpoint 4096 2117+point split endpoint 4096 2118)/2)
    have hp : upperPayment 2117 = (262270018192:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2117+point split endpoint 4096 2118)/2 = (629406677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629406677:ℝ)/168755200)*ClassicalSixthBranch.v ((629406677:ℝ)/168755200)/ClassicalSixthBranch.r = (112413941308745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2117
  · change upperPayment 2118 ≤ upperValue ((point split endpoint 4096 2118+point split endpoint 4096 2119)/2)
    have hp : upperPayment 2118 = (262168371269:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2118+point split endpoint 4096 2119)/2 = (629431827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629431827:ℝ)/168755200)*ClassicalSixthBranch.v ((629431827:ℝ)/168755200)/ClassicalSixthBranch.r = (112392210976377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2118
  · change upperPayment 2119 ≤ upperValue ((point split endpoint 4096 2119+point split endpoint 4096 2120)/2)
    have hp : upperPayment 2119 = (262066697499:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2119+point split endpoint 4096 2120)/2 = (629456977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629456977:ℝ)/168755200)*ClassicalSixthBranch.v ((629456977:ℝ)/168755200)/ClassicalSixthBranch.r = (112370482668081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2119
  · change upperPayment 2120 ≤ upperValue ((point split endpoint 4096 2120+point split endpoint 4096 2121)/2)
    have hp : upperPayment 2120 = (261964996878:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2120+point split endpoint 4096 2121)/2 = (629482127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629482127:ℝ)/168755200)*ClassicalSixthBranch.v ((629482127:ℝ)/168755200)/ClassicalSixthBranch.r = (112348756383857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2120
  · change upperPayment 2121 ≤ upperValue ((point split endpoint 4096 2121+point split endpoint 4096 2122)/2)
    have hp : upperPayment 2121 = (261863269399:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2121+point split endpoint 4096 2122)/2 = (629507277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629507277:ℝ)/168755200)*ClassicalSixthBranch.v ((629507277:ℝ)/168755200)/ClassicalSixthBranch.r = (112327032123705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2121
  · change upperPayment 2122 ≤ upperValue ((point split endpoint 4096 2122+point split endpoint 4096 2123)/2)
    have hp : upperPayment 2122 = (261761515059:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2122+point split endpoint 4096 2123)/2 = (629532427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629532427:ℝ)/168755200)*ClassicalSixthBranch.v ((629532427:ℝ)/168755200)/ClassicalSixthBranch.r = (112305309887625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2122
  · change upperPayment 2123 ≤ upperValue ((point split endpoint 4096 2123+point split endpoint 4096 2124)/2)
    have hp : upperPayment 2123 = (261659733850:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2123+point split endpoint 4096 2124)/2 = (629557577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629557577:ℝ)/168755200)*ClassicalSixthBranch.v ((629557577:ℝ)/168755200)/ClassicalSixthBranch.r = (112283589675617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2123
  · change upperPayment 2124 ≤ upperValue ((point split endpoint 4096 2124+point split endpoint 4096 2125)/2)
    have hp : upperPayment 2124 = (261557925768:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2124+point split endpoint 4096 2125)/2 = (629582727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629582727:ℝ)/168755200)*ClassicalSixthBranch.v ((629582727:ℝ)/168755200)/ClassicalSixthBranch.r = (112261871487681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2124
  · change upperPayment 2125 ≤ upperValue ((point split endpoint 4096 2125+point split endpoint 4096 2126)/2)
    have hp : upperPayment 2125 = (261456090807:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2125+point split endpoint 4096 2126)/2 = (629607877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629607877:ℝ)/168755200)*ClassicalSixthBranch.v ((629607877:ℝ)/168755200)/ClassicalSixthBranch.r = (112240155323817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2125
  · change upperPayment 2126 ≤ upperValue ((point split endpoint 4096 2126+point split endpoint 4096 2127)/2)
    have hp : upperPayment 2126 = (261354228962:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2126+point split endpoint 4096 2127)/2 = (629633027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629633027:ℝ)/168755200)*ClassicalSixthBranch.v ((629633027:ℝ)/168755200)/ClassicalSixthBranch.r = (112218441184025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2126
  · change upperPayment 2127 ≤ upperValue ((point split endpoint 4096 2127+point split endpoint 4096 2128)/2)
    have hp : upperPayment 2127 = (261252340228:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2127+point split endpoint 4096 2128)/2 = (629658177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629658177:ℝ)/168755200)*ClassicalSixthBranch.v ((629658177:ℝ)/168755200)/ClassicalSixthBranch.r = (112196729068305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2127
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_132
