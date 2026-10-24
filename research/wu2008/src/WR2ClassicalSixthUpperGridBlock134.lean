import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints134
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_134 (j : Fin 16) : upperPayment (16*134+j.val) ≤
    upperValue ((point split endpoint 4096 (16*134+j.val)+point split endpoint 4096 (16*134+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2144 ≤ upperValue ((point split endpoint 4096 2144+point split endpoint 4096 2145)/2)
    have hp : upperPayment 2144 = (259516112338:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2144+point split endpoint 4096 2145)/2 = (630085727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630085727:ℝ)/168755200)*ClassicalSixthBranch.v ((630085727:ℝ)/168755200)/ClassicalSixthBranch.r = (111827932784081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2144
  · change upperPayment 2145 ≤ upperValue ((point split endpoint 4096 2145+point split endpoint 4096 2146)/2)
    have hp : upperPayment 2145 = (259413738656:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2145+point split endpoint 4096 2146)/2 = (630110877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630110877:ℝ)/168755200)*ClassicalSixthBranch.v ((630110877:ℝ)/168755200)/ClassicalSixthBranch.r = (111806257101657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2145
  · change upperPayment 2146 ≤ upperValue ((point split endpoint 4096 2146+point split endpoint 4096 2147)/2)
    have hp : upperPayment 2146 = (259311337981:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2146+point split endpoint 4096 2147)/2 = (630136027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630136027:ℝ)/168755200)*ClassicalSixthBranch.v ((630136027:ℝ)/168755200)/ClassicalSixthBranch.r = (111784583443305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2146
  · change upperPayment 2147 ≤ upperValue ((point split endpoint 4096 2147+point split endpoint 4096 2148)/2)
    have hp : upperPayment 2147 = (259208910307:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2147+point split endpoint 4096 2148)/2 = (630161177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630161177:ℝ)/168755200)*ClassicalSixthBranch.v ((630161177:ℝ)/168755200)/ClassicalSixthBranch.r = (111762911809025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2147
  · change upperPayment 2148 ≤ upperValue ((point split endpoint 4096 2148+point split endpoint 4096 2149)/2)
    have hp : upperPayment 2148 = (259106455628:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2148+point split endpoint 4096 2149)/2 = (630186327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630186327:ℝ)/168755200)*ClassicalSixthBranch.v ((630186327:ℝ)/168755200)/ClassicalSixthBranch.r = (111741242198817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2148
  · change upperPayment 2149 ≤ upperValue ((point split endpoint 4096 2149+point split endpoint 4096 2150)/2)
    have hp : upperPayment 2149 = (259003973940:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2149+point split endpoint 4096 2150)/2 = (630211477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630211477:ℝ)/168755200)*ClassicalSixthBranch.v ((630211477:ℝ)/168755200)/ClassicalSixthBranch.r = (111719574612681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2149
  · change upperPayment 2150 ≤ upperValue ((point split endpoint 4096 2150+point split endpoint 4096 2151)/2)
    have hp : upperPayment 2150 = (258901465236:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2150+point split endpoint 4096 2151)/2 = (630236627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630236627:ℝ)/168755200)*ClassicalSixthBranch.v ((630236627:ℝ)/168755200)/ClassicalSixthBranch.r = (111697909050617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2150
  · change upperPayment 2151 ≤ upperValue ((point split endpoint 4096 2151+point split endpoint 4096 2152)/2)
    have hp : upperPayment 2151 = (258798929511:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2151+point split endpoint 4096 2152)/2 = (630261777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630261777:ℝ)/168755200)*ClassicalSixthBranch.v ((630261777:ℝ)/168755200)/ClassicalSixthBranch.r = (111676245512625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2151
  · change upperPayment 2152 ≤ upperValue ((point split endpoint 4096 2152+point split endpoint 4096 2153)/2)
    have hp : upperPayment 2152 = (258696366759:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2152+point split endpoint 4096 2153)/2 = (630286927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630286927:ℝ)/168755200)*ClassicalSixthBranch.v ((630286927:ℝ)/168755200)/ClassicalSixthBranch.r = (111654583998705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2152
  · change upperPayment 2153 ≤ upperValue ((point split endpoint 4096 2153+point split endpoint 4096 2154)/2)
    have hp : upperPayment 2153 = (258593776976:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2153+point split endpoint 4096 2154)/2 = (630312077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630312077:ℝ)/168755200)*ClassicalSixthBranch.v ((630312077:ℝ)/168755200)/ClassicalSixthBranch.r = (111632924508857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2153
  · change upperPayment 2154 ≤ upperValue ((point split endpoint 4096 2154+point split endpoint 4096 2155)/2)
    have hp : upperPayment 2154 = (258491160155:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2154+point split endpoint 4096 2155)/2 = (630337227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630337227:ℝ)/168755200)*ClassicalSixthBranch.v ((630337227:ℝ)/168755200)/ClassicalSixthBranch.r = (111611267043081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2154
  · change upperPayment 2155 ≤ upperValue ((point split endpoint 4096 2155+point split endpoint 4096 2156)/2)
    have hp : upperPayment 2155 = (258388516291:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2155+point split endpoint 4096 2156)/2 = (630362377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630362377:ℝ)/168755200)*ClassicalSixthBranch.v ((630362377:ℝ)/168755200)/ClassicalSixthBranch.r = (111589611601377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2155
  · change upperPayment 2156 ≤ upperValue ((point split endpoint 4096 2156+point split endpoint 4096 2157)/2)
    have hp : upperPayment 2156 = (258285845379:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2156+point split endpoint 4096 2157)/2 = (630387527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630387527:ℝ)/168755200)*ClassicalSixthBranch.v ((630387527:ℝ)/168755200)/ClassicalSixthBranch.r = (111567958183745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2156
  · change upperPayment 2157 ≤ upperValue ((point split endpoint 4096 2157+point split endpoint 4096 2158)/2)
    have hp : upperPayment 2157 = (258183147413:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2157+point split endpoint 4096 2158)/2 = (630412677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630412677:ℝ)/168755200)*ClassicalSixthBranch.v ((630412677:ℝ)/168755200)/ClassicalSixthBranch.r = (111546306790185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2157
  · change upperPayment 2158 ≤ upperValue ((point split endpoint 4096 2158+point split endpoint 4096 2159)/2)
    have hp : upperPayment 2158 = (258080422387:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2158+point split endpoint 4096 2159)/2 = (630437827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630437827:ℝ)/168755200)*ClassicalSixthBranch.v ((630437827:ℝ)/168755200)/ClassicalSixthBranch.r = (111524657420697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2158
  · change upperPayment 2159 ≤ upperValue ((point split endpoint 4096 2159+point split endpoint 4096 2160)/2)
    have hp : upperPayment 2159 = (257977670296:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2159+point split endpoint 4096 2160)/2 = (630462977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630462977:ℝ)/168755200)*ClassicalSixthBranch.v ((630462977:ℝ)/168755200)/ClassicalSixthBranch.r = (111503010075281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2159
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_134
