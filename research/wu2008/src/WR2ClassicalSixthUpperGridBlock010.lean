import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints010
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_010 (j : Fin 16) : upperPayment (16*10+j.val) ≤
    upperValue ((point split endpoint 4096 (16*10+j.val)+point split endpoint 4096 (16*10+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 160 ≤ upperValue ((point split endpoint 4096 160+point split endpoint 4096 161)/2)
    have hp : upperPayment 160 = (415378780354:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 160+point split endpoint 4096 161)/2 = (580188127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580188127:ℝ)/168755200)*ClassicalSixthBranch.v ((580188127:ℝ)/168755200)/ClassicalSixthBranch.r = (158818127369937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_160
  · change upperPayment 161 ≤ upperValue ((point split endpoint 4096 161+point split endpoint 4096 162)/2)
    have hp : upperPayment 161 = (415321588947:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 161+point split endpoint 4096 162)/2 = (580213277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580213277:ℝ)/168755200)*ClassicalSixthBranch.v ((580213277:ℝ)/168755200)/ClassicalSixthBranch.r = (158792435928665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_161
  · change upperPayment 162 ≤ upperValue ((point split endpoint 4096 162+point split endpoint 4096 163)/2)
    have hp : upperPayment 162 = (415264377939:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 162+point split endpoint 4096 163)/2 = (580238427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580238427:ℝ)/168755200)*ClassicalSixthBranch.v ((580238427:ℝ)/168755200)/ClassicalSixthBranch.r = (158766746511465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_162
  · change upperPayment 163 ≤ upperValue ((point split endpoint 4096 163+point split endpoint 4096 164)/2)
    have hp : upperPayment 163 = (415207147328:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 163+point split endpoint 4096 164)/2 = (580263577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580263577:ℝ)/168755200)*ClassicalSixthBranch.v ((580263577:ℝ)/168755200)/ClassicalSixthBranch.r = (158741059118337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_163
  · change upperPayment 164 ≤ upperValue ((point split endpoint 4096 164+point split endpoint 4096 165)/2)
    have hp : upperPayment 164 = (415149897112:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 164+point split endpoint 4096 165)/2 = (580288727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580288727:ℝ)/168755200)*ClassicalSixthBranch.v ((580288727:ℝ)/168755200)/ClassicalSixthBranch.r = (158715373749281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_164
  · change upperPayment 165 ≤ upperValue ((point split endpoint 4096 165+point split endpoint 4096 166)/2)
    have hp : upperPayment 165 = (415092627288:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 165+point split endpoint 4096 166)/2 = (580313877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580313877:ℝ)/168755200)*ClassicalSixthBranch.v ((580313877:ℝ)/168755200)/ClassicalSixthBranch.r = (158689690404297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_165
  · change upperPayment 166 ≤ upperValue ((point split endpoint 4096 166+point split endpoint 4096 167)/2)
    have hp : upperPayment 166 = (415035337853:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 166+point split endpoint 4096 167)/2 = (580339027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580339027:ℝ)/168755200)*ClassicalSixthBranch.v ((580339027:ℝ)/168755200)/ClassicalSixthBranch.r = (158664009083385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_166
  · change upperPayment 167 ≤ upperValue ((point split endpoint 4096 167+point split endpoint 4096 168)/2)
    have hp : upperPayment 167 = (414978028807:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 167+point split endpoint 4096 168)/2 = (580364177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580364177:ℝ)/168755200)*ClassicalSixthBranch.v ((580364177:ℝ)/168755200)/ClassicalSixthBranch.r = (158638329786545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_167
  · change upperPayment 168 ≤ upperValue ((point split endpoint 4096 168+point split endpoint 4096 169)/2)
    have hp : upperPayment 168 = (414920700146:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 168+point split endpoint 4096 169)/2 = (580389327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580389327:ℝ)/168755200)*ClassicalSixthBranch.v ((580389327:ℝ)/168755200)/ClassicalSixthBranch.r = (158612652513777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_168
  · change upperPayment 169 ≤ upperValue ((point split endpoint 4096 169+point split endpoint 4096 170)/2)
    have hp : upperPayment 169 = (414863351868:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 169+point split endpoint 4096 170)/2 = (580414477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580414477:ℝ)/168755200)*ClassicalSixthBranch.v ((580414477:ℝ)/168755200)/ClassicalSixthBranch.r = (158586977265081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_169
  · change upperPayment 170 ≤ upperValue ((point split endpoint 4096 170+point split endpoint 4096 171)/2)
    have hp : upperPayment 170 = (414805983971:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 170+point split endpoint 4096 171)/2 = (580439627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580439627:ℝ)/168755200)*ClassicalSixthBranch.v ((580439627:ℝ)/168755200)/ClassicalSixthBranch.r = (158561304040457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_170
  · change upperPayment 171 ≤ upperValue ((point split endpoint 4096 171+point split endpoint 4096 172)/2)
    have hp : upperPayment 171 = (414748596453:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 171+point split endpoint 4096 172)/2 = (580464777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580464777:ℝ)/168755200)*ClassicalSixthBranch.v ((580464777:ℝ)/168755200)/ClassicalSixthBranch.r = (158535632839905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_171
  · change upperPayment 172 ≤ upperValue ((point split endpoint 4096 172+point split endpoint 4096 173)/2)
    have hp : upperPayment 172 = (414691189310:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 172+point split endpoint 4096 173)/2 = (580489927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580489927:ℝ)/168755200)*ClassicalSixthBranch.v ((580489927:ℝ)/168755200)/ClassicalSixthBranch.r = (158509963663425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_172
  · change upperPayment 173 ≤ upperValue ((point split endpoint 4096 173+point split endpoint 4096 174)/2)
    have hp : upperPayment 173 = (414633762542:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 173+point split endpoint 4096 174)/2 = (580515077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580515077:ℝ)/168755200)*ClassicalSixthBranch.v ((580515077:ℝ)/168755200)/ClassicalSixthBranch.r = (158484296511017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_173
  · change upperPayment 174 ≤ upperValue ((point split endpoint 4096 174+point split endpoint 4096 175)/2)
    have hp : upperPayment 174 = (414576316145:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 174+point split endpoint 4096 175)/2 = (580540227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580540227:ℝ)/168755200)*ClassicalSixthBranch.v ((580540227:ℝ)/168755200)/ClassicalSixthBranch.r = (158458631382681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_174
  · change upperPayment 175 ≤ upperValue ((point split endpoint 4096 175+point split endpoint 4096 176)/2)
    have hp : upperPayment 175 = (414518850117:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 175+point split endpoint 4096 176)/2 = (580565377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580565377:ℝ)/168755200)*ClassicalSixthBranch.v ((580565377:ℝ)/168755200)/ClassicalSixthBranch.r = (158432968278417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_175
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_010
