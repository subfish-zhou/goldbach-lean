import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints129
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_129 (j : Fin 16) : upperPayment (16*129+j.val) ≤
    upperValue ((point split endpoint 4096 (16*129+j.val)+point split endpoint 4096 (16*129+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2064 ≤ upperValue ((point split endpoint 4096 2064+point split endpoint 4096 2065)/2)
    have hp : upperPayment 2064 = (267619029902:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2064+point split endpoint 4096 2065)/2 = (628073727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628073727:ℝ)/168755200)*ClassicalSixthBranch.v ((628073727:ℝ)/168755200)/ClassicalSixthBranch.r = (113568545371281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2064
  · change upperPayment 2065 ≤ upperValue ((point split endpoint 4096 2065+point split endpoint 4096 2066)/2)
    have hp : upperPayment 2065 = (267518798114:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2065+point split endpoint 4096 2066)/2 = (628098877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628098877:ℝ)/168755200)*ClassicalSixthBranch.v ((628098877:ℝ)/168755200)/ClassicalSixthBranch.r = (113546707763097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2065
  · change upperPayment 2066 ≤ upperValue ((point split endpoint 4096 2066+point split endpoint 4096 2067)/2)
    have hp : upperPayment 2066 = (267418539764:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2066+point split endpoint 4096 2067)/2 = (628124027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628124027:ℝ)/168755200)*ClassicalSixthBranch.v ((628124027:ℝ)/168755200)/ClassicalSixthBranch.r = (113524872178985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2066
  · change upperPayment 2067 ≤ upperValue ((point split endpoint 4096 2067+point split endpoint 4096 2068)/2)
    have hp : upperPayment 2067 = (267318254848:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2067+point split endpoint 4096 2068)/2 = (628149177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628149177:ℝ)/168755200)*ClassicalSixthBranch.v ((628149177:ℝ)/168755200)/ClassicalSixthBranch.r = (113503038618945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2067
  · change upperPayment 2068 ≤ upperValue ((point split endpoint 4096 2068+point split endpoint 4096 2069)/2)
    have hp : upperPayment 2068 = (267217943359:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2068+point split endpoint 4096 2069)/2 = (628174327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628174327:ℝ)/168755200)*ClassicalSixthBranch.v ((628174327:ℝ)/168755200)/ClassicalSixthBranch.r = (113481207082977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2068
  · change upperPayment 2069 ≤ upperValue ((point split endpoint 4096 2069+point split endpoint 4096 2070)/2)
    have hp : upperPayment 2069 = (267117605293:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2069+point split endpoint 4096 2070)/2 = (628199477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628199477:ℝ)/168755200)*ClassicalSixthBranch.v ((628199477:ℝ)/168755200)/ClassicalSixthBranch.r = (113459377571081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2069
  · change upperPayment 2070 ≤ upperValue ((point split endpoint 4096 2070+point split endpoint 4096 2071)/2)
    have hp : upperPayment 2070 = (267017240644:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2070+point split endpoint 4096 2071)/2 = (628224627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628224627:ℝ)/168755200)*ClassicalSixthBranch.v ((628224627:ℝ)/168755200)/ClassicalSixthBranch.r = (113437550083257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2070
  · change upperPayment 2071 ≤ upperValue ((point split endpoint 4096 2071+point split endpoint 4096 2072)/2)
    have hp : upperPayment 2071 = (266916849407:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2071+point split endpoint 4096 2072)/2 = (628249777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628249777:ℝ)/168755200)*ClassicalSixthBranch.v ((628249777:ℝ)/168755200)/ClassicalSixthBranch.r = (113415724619505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2071
  · change upperPayment 2072 ≤ upperValue ((point split endpoint 4096 2072+point split endpoint 4096 2073)/2)
    have hp : upperPayment 2072 = (266816431576:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2072+point split endpoint 4096 2073)/2 = (628274927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628274927:ℝ)/168755200)*ClassicalSixthBranch.v ((628274927:ℝ)/168755200)/ClassicalSixthBranch.r = (113393901179825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2072
  · change upperPayment 2073 ≤ upperValue ((point split endpoint 4096 2073+point split endpoint 4096 2074)/2)
    have hp : upperPayment 2073 = (266715987146:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2073+point split endpoint 4096 2074)/2 = (628300077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628300077:ℝ)/168755200)*ClassicalSixthBranch.v ((628300077:ℝ)/168755200)/ClassicalSixthBranch.r = (113372079764217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2073
  · change upperPayment 2074 ≤ upperValue ((point split endpoint 4096 2074+point split endpoint 4096 2075)/2)
    have hp : upperPayment 2074 = (266615516113:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2074+point split endpoint 4096 2075)/2 = (628325227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628325227:ℝ)/168755200)*ClassicalSixthBranch.v ((628325227:ℝ)/168755200)/ClassicalSixthBranch.r = (113350260372681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2074
  · change upperPayment 2075 ≤ upperValue ((point split endpoint 4096 2075+point split endpoint 4096 2076)/2)
    have hp : upperPayment 2075 = (266515018470:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2075+point split endpoint 4096 2076)/2 = (628350377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628350377:ℝ)/168755200)*ClassicalSixthBranch.v ((628350377:ℝ)/168755200)/ClassicalSixthBranch.r = (113328443005217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2075
  · change upperPayment 2076 ≤ upperValue ((point split endpoint 4096 2076+point split endpoint 4096 2077)/2)
    have hp : upperPayment 2076 = (266414494212:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2076+point split endpoint 4096 2077)/2 = (628375527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628375527:ℝ)/168755200)*ClassicalSixthBranch.v ((628375527:ℝ)/168755200)/ClassicalSixthBranch.r = (113306627661825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2076
  · change upperPayment 2077 ≤ upperValue ((point split endpoint 4096 2077+point split endpoint 4096 2078)/2)
    have hp : upperPayment 2077 = (266313943334:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2077+point split endpoint 4096 2078)/2 = (628400677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628400677:ℝ)/168755200)*ClassicalSixthBranch.v ((628400677:ℝ)/168755200)/ClassicalSixthBranch.r = (113284814342505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2077
  · change upperPayment 2078 ≤ upperValue ((point split endpoint 4096 2078+point split endpoint 4096 2079)/2)
    have hp : upperPayment 2078 = (266213365830:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2078+point split endpoint 4096 2079)/2 = (628425827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628425827:ℝ)/168755200)*ClassicalSixthBranch.v ((628425827:ℝ)/168755200)/ClassicalSixthBranch.r = (113263003047257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2078
  · change upperPayment 2079 ≤ upperValue ((point split endpoint 4096 2079+point split endpoint 4096 2080)/2)
    have hp : upperPayment 2079 = (266112761696:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2079+point split endpoint 4096 2080)/2 = (628450977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628450977:ℝ)/168755200)*ClassicalSixthBranch.v ((628450977:ℝ)/168755200)/ClassicalSixthBranch.r = (113241193776081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2079
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_129
