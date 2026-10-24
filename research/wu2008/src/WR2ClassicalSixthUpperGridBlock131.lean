import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints131
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_131 (j : Fin 16) : upperPayment (16*131+j.val) ≤
    upperValue ((point split endpoint 4096 (16*131+j.val)+point split endpoint 4096 (16*131+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2096 ≤ upperValue ((point split endpoint 4096 2096+point split endpoint 4096 2097)/2)
    have hp : upperPayment 2096 = (264398411715:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2096+point split endpoint 4096 2097)/2 = (628878527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628878527:ℝ)/168755200)*ClassicalSixthBranch.v ((628878527:ℝ)/168755200)/ClassicalSixthBranch.r = (112870745849105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2096
  · change upperPayment 2097 ≤ upperValue ((point split endpoint 4096 2097+point split endpoint 4096 2098)/2)
    have hp : upperPayment 2097 = (264297327311:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2097+point split endpoint 4096 2098)/2 = (628903677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628903677:ℝ)/168755200)*ClassicalSixthBranch.v ((628903677:ℝ)/168755200)/ClassicalSixthBranch.r = (112848973011225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2097
  · change upperPayment 2098 ≤ upperValue ((point split endpoint 4096 2098+point split endpoint 4096 2099)/2)
    have hp : upperPayment 2098 = (264196216174:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2098+point split endpoint 4096 2099)/2 = (628928827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628928827:ℝ)/168755200)*ClassicalSixthBranch.v ((628928827:ℝ)/168755200)/ClassicalSixthBranch.r = (112827202197417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2098
  · change upperPayment 2099 ≤ upperValue ((point split endpoint 4096 2099+point split endpoint 4096 2100)/2)
    have hp : upperPayment 2099 = (264095078299:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2099+point split endpoint 4096 2100)/2 = (628953977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628953977:ℝ)/168755200)*ClassicalSixthBranch.v ((628953977:ℝ)/168755200)/ClassicalSixthBranch.r = (112805433407681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2099
  · change upperPayment 2100 ≤ upperValue ((point split endpoint 4096 2100+point split endpoint 4096 2101)/2)
    have hp : upperPayment 2100 = (263993913680:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2100+point split endpoint 4096 2101)/2 = (628979127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628979127:ℝ)/168755200)*ClassicalSixthBranch.v ((628979127:ℝ)/168755200)/ClassicalSixthBranch.r = (112783666642017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2100
  · change upperPayment 2101 ≤ upperValue ((point split endpoint 4096 2101+point split endpoint 4096 2102)/2)
    have hp : upperPayment 2101 = (263892722313:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2101+point split endpoint 4096 2102)/2 = (629004277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629004277:ℝ)/168755200)*ClassicalSixthBranch.v ((629004277:ℝ)/168755200)/ClassicalSixthBranch.r = (112761901900425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2101
  · change upperPayment 2102 ≤ upperValue ((point split endpoint 4096 2102+point split endpoint 4096 2103)/2)
    have hp : upperPayment 2102 = (263791504191:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2102+point split endpoint 4096 2103)/2 = (629029427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629029427:ℝ)/168755200)*ClassicalSixthBranch.v ((629029427:ℝ)/168755200)/ClassicalSixthBranch.r = (112740139182905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2102
  · change upperPayment 2103 ≤ upperValue ((point split endpoint 4096 2103+point split endpoint 4096 2104)/2)
    have hp : upperPayment 2103 = (263690259310:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2103+point split endpoint 4096 2104)/2 = (629054577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629054577:ℝ)/168755200)*ClassicalSixthBranch.v ((629054577:ℝ)/168755200)/ClassicalSixthBranch.r = (112718378489457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2103
  · change upperPayment 2104 ≤ upperValue ((point split endpoint 4096 2104+point split endpoint 4096 2105)/2)
    have hp : upperPayment 2104 = (263588987664:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2104+point split endpoint 4096 2105)/2 = (629079727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629079727:ℝ)/168755200)*ClassicalSixthBranch.v ((629079727:ℝ)/168755200)/ClassicalSixthBranch.r = (112696619820081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2104
  · change upperPayment 2105 ≤ upperValue ((point split endpoint 4096 2105+point split endpoint 4096 2106)/2)
    have hp : upperPayment 2105 = (263487689248:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2105+point split endpoint 4096 2106)/2 = (629104877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629104877:ℝ)/168755200)*ClassicalSixthBranch.v ((629104877:ℝ)/168755200)/ClassicalSixthBranch.r = (84909467351:ℝ)/55297703936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2105
  · change upperPayment 2106 ≤ upperValue ((point split endpoint 4096 2106+point split endpoint 4096 2107)/2)
    have hp : upperPayment 2106 = (263386364055:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2106+point split endpoint 4096 2107)/2 = (629130027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629130027:ℝ)/168755200)*ClassicalSixthBranch.v ((629130027:ℝ)/168755200)/ClassicalSixthBranch.r = (112653108553545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2106
  · change upperPayment 2107 ≤ upperValue ((point split endpoint 4096 2107+point split endpoint 4096 2108)/2)
    have hp : upperPayment 2107 = (263285012082:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2107+point split endpoint 4096 2108)/2 = (629155177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629155177:ℝ)/168755200)*ClassicalSixthBranch.v ((629155177:ℝ)/168755200)/ClassicalSixthBranch.r = (112631355956385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2107
  · change upperPayment 2108 ≤ upperValue ((point split endpoint 4096 2108+point split endpoint 4096 2109)/2)
    have hp : upperPayment 2108 = (263183633322:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2108+point split endpoint 4096 2109)/2 = (629180327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629180327:ℝ)/168755200)*ClassicalSixthBranch.v ((629180327:ℝ)/168755200)/ClassicalSixthBranch.r = (112609605383297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2108
  · change upperPayment 2109 ≤ upperValue ((point split endpoint 4096 2109+point split endpoint 4096 2110)/2)
    have hp : upperPayment 2109 = (263082227770:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2109+point split endpoint 4096 2110)/2 = (629205477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629205477:ℝ)/168755200)*ClassicalSixthBranch.v ((629205477:ℝ)/168755200)/ClassicalSixthBranch.r = (112587856834281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2109
  · change upperPayment 2110 ≤ upperValue ((point split endpoint 4096 2110+point split endpoint 4096 2111)/2)
    have hp : upperPayment 2110 = (262980795420:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2110+point split endpoint 4096 2111)/2 = (629230627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629230627:ℝ)/168755200)*ClassicalSixthBranch.v ((629230627:ℝ)/168755200)/ClassicalSixthBranch.r = (112566110309337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2110
  · change upperPayment 2111 ≤ upperValue ((point split endpoint 4096 2111+point split endpoint 4096 2112)/2)
    have hp : upperPayment 2111 = (262879336268:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2111+point split endpoint 4096 2112)/2 = (629255777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((629255777:ℝ)/168755200)*ClassicalSixthBranch.v ((629255777:ℝ)/168755200)/ClassicalSixthBranch.r = (112544365808465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2111
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_131
