import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints135
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_135 (j : Fin 16) : upperPayment (16*135+j.val) ≤
    upperValue ((point split endpoint 4096 (16*135+j.val)+point split endpoint 4096 (16*135+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2160 ≤ upperValue ((point split endpoint 4096 2160+point split endpoint 4096 2161)/2)
    have hp : upperPayment 2160 = (257874891135:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2160+point split endpoint 4096 2161)/2 = (630488127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630488127:ℝ)/168755200)*ClassicalSixthBranch.v ((630488127:ℝ)/168755200)/ClassicalSixthBranch.r = (111481364753937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2160
  · change upperPayment 2161 ≤ upperValue ((point split endpoint 4096 2161+point split endpoint 4096 2162)/2)
    have hp : upperPayment 2161 = (257772084898:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2161+point split endpoint 4096 2162)/2 = (630513277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630513277:ℝ)/168755200)*ClassicalSixthBranch.v ((630513277:ℝ)/168755200)/ClassicalSixthBranch.r = (111459721456665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2161
  · change upperPayment 2162 ≤ upperValue ((point split endpoint 4096 2162+point split endpoint 4096 2163)/2)
    have hp : upperPayment 2162 = (257669251579:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2162+point split endpoint 4096 2163)/2 = (630538427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630538427:ℝ)/168755200)*ClassicalSixthBranch.v ((630538427:ℝ)/168755200)/ClassicalSixthBranch.r = (111438080183465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2162
  · change upperPayment 2163 ≤ upperValue ((point split endpoint 4096 2163+point split endpoint 4096 2164)/2)
    have hp : upperPayment 2163 = (257566391173:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2163+point split endpoint 4096 2164)/2 = (630563577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630563577:ℝ)/168755200)*ClassicalSixthBranch.v ((630563577:ℝ)/168755200)/ClassicalSixthBranch.r = (111416440934337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2163
  · change upperPayment 2164 ≤ upperValue ((point split endpoint 4096 2164+point split endpoint 4096 2165)/2)
    have hp : upperPayment 2164 = (257463503674:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2164+point split endpoint 4096 2165)/2 = (630588727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630588727:ℝ)/168755200)*ClassicalSixthBranch.v ((630588727:ℝ)/168755200)/ClassicalSixthBranch.r = (111394803709281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2164
  · change upperPayment 2165 ≤ upperValue ((point split endpoint 4096 2165+point split endpoint 4096 2166)/2)
    have hp : upperPayment 2165 = (257360589078:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2165+point split endpoint 4096 2166)/2 = (630613877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630613877:ℝ)/168755200)*ClassicalSixthBranch.v ((630613877:ℝ)/168755200)/ClassicalSixthBranch.r = (111373168508297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2165
  · change upperPayment 2166 ≤ upperValue ((point split endpoint 4096 2166+point split endpoint 4096 2167)/2)
    have hp : upperPayment 2166 = (257257647377:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2166+point split endpoint 4096 2167)/2 = (6122709:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6122709:ℝ)/1638400)*ClassicalSixthBranch.v ((6122709:ℝ)/1638400)/ClassicalSixthBranch.r = (1081082867295:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2166
  · change upperPayment 2167 ≤ upperValue ((point split endpoint 4096 2167+point split endpoint 4096 2168)/2)
    have hp : upperPayment 2167 = (257154678568:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2167+point split endpoint 4096 2168)/2 = (630664177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630664177:ℝ)/168755200)*ClassicalSixthBranch.v ((630664177:ℝ)/168755200)/ClassicalSixthBranch.r = (111329904178545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2167
  · change upperPayment 2168 ≤ upperValue ((point split endpoint 4096 2168+point split endpoint 4096 2169)/2)
    have hp : upperPayment 2168 = (257051682643:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2168+point split endpoint 4096 2169)/2 = (630689327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630689327:ℝ)/168755200)*ClassicalSixthBranch.v ((630689327:ℝ)/168755200)/ClassicalSixthBranch.r = (111308275049777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2168
  · change upperPayment 2169 ≤ upperValue ((point split endpoint 4096 2169+point split endpoint 4096 2170)/2)
    have hp : upperPayment 2169 = (256948659599:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2169+point split endpoint 4096 2170)/2 = (630714477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630714477:ℝ)/168755200)*ClassicalSixthBranch.v ((630714477:ℝ)/168755200)/ClassicalSixthBranch.r = (111286647945081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2169
  · change upperPayment 2170 ≤ upperValue ((point split endpoint 4096 2170+point split endpoint 4096 2171)/2)
    have hp : upperPayment 2170 = (256845609428:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2170+point split endpoint 4096 2171)/2 = (630739627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630739627:ℝ)/168755200)*ClassicalSixthBranch.v ((630739627:ℝ)/168755200)/ClassicalSixthBranch.r = (111265022864457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2170
  · change upperPayment 2171 ≤ upperValue ((point split endpoint 4096 2171+point split endpoint 4096 2172)/2)
    have hp : upperPayment 2171 = (256742532127:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2171+point split endpoint 4096 2172)/2 = (630764777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630764777:ℝ)/168755200)*ClassicalSixthBranch.v ((630764777:ℝ)/168755200)/ClassicalSixthBranch.r = (111243399807905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2171
  · change upperPayment 2172 ≤ upperValue ((point split endpoint 4096 2172+point split endpoint 4096 2173)/2)
    have hp : upperPayment 2172 = (256639427688:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2172+point split endpoint 4096 2173)/2 = (630789927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630789927:ℝ)/168755200)*ClassicalSixthBranch.v ((630789927:ℝ)/168755200)/ClassicalSixthBranch.r = (111221778775425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2172
  · change upperPayment 2173 ≤ upperValue ((point split endpoint 4096 2173+point split endpoint 4096 2174)/2)
    have hp : upperPayment 2173 = (256536296107:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2173+point split endpoint 4096 2174)/2 = (630815077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630815077:ℝ)/168755200)*ClassicalSixthBranch.v ((630815077:ℝ)/168755200)/ClassicalSixthBranch.r = (111200159767017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2173
  · change upperPayment 2174 ≤ upperValue ((point split endpoint 4096 2174+point split endpoint 4096 2175)/2)
    have hp : upperPayment 2174 = (256433137378:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2174+point split endpoint 4096 2175)/2 = (630840227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630840227:ℝ)/168755200)*ClassicalSixthBranch.v ((630840227:ℝ)/168755200)/ClassicalSixthBranch.r = (111178542782681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2174
  · change upperPayment 2175 ≤ upperValue ((point split endpoint 4096 2175+point split endpoint 4096 2176)/2)
    have hp : upperPayment 2175 = (256329951495:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2175+point split endpoint 4096 2176)/2 = (630865377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((630865377:ℝ)/168755200)*ClassicalSixthBranch.v ((630865377:ℝ)/168755200)/ClassicalSixthBranch.r = (111156927822417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2175
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_135
