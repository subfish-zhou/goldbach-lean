import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints010
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_010 (j : Fin 16) : lowerPayment (16*10+j.val) ≤
    lowerValue ((point 2 split 4096 (16*10+j.val)+point 2 split 4096 (16*10+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 160 ≤ lowerValue ((point 2 split 4096 160+point 2 split 4096 161)/2)
    have hp : lowerPayment 160 = (25222098772:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 160+point 2 split 4096 161)/2 = (346861451:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((346861451:ℝ)/168755200)/ClassicalSixthBranch.v ((346861451:ℝ)/168755200) = (801606332027:ℝ)/412873193624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_160
  · change lowerPayment 161 ≤ lowerValue ((point 2 split 4096 161+point 2 split 4096 162)/2)
    have hp : lowerPayment 161 = (25373468064:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 161+point 2 split 4096 162)/2 = (346919713:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((346919713:ℝ)/168755200)/ClassicalSixthBranch.v ((346919713:ℝ)/168755200) = (801529018353:ℝ)/412825185736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_161
  · change lowerPayment 162 ≤ lowerValue ((point 2 split 4096 162+point 2 split 4096 163)/2)
    have hp : lowerPayment 162 = (25524769284:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 162+point 2 split 4096 163)/2 = (13879119:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((13879119:ℝ)/6750208)/ClassicalSixthBranch.v ((13879119:ℝ)/6750208) = (801451704679:ℝ)/412777177848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_162
  · change lowerPayment 163 ≤ lowerValue ((point 2 split 4096 163+point 2 split 4096 164)/2)
    have hp : lowerPayment 163 = (25676002491:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 163+point 2 split 4096 164)/2 = (347036237:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((347036237:ℝ)/168755200)/ClassicalSixthBranch.v ((347036237:ℝ)/168755200) = (160274878201:ℝ)/82545833992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_163
  · change lowerPayment 164 ≤ lowerValue ((point 2 split 4096 164+point 2 split 4096 165)/2)
    have hp : lowerPayment 164 = (25827167748:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 164+point 2 split 4096 165)/2 = (347094499:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((347094499:ℝ)/168755200)/ClassicalSixthBranch.v ((347094499:ℝ)/168755200) = (801297077331:ℝ)/412681162072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_164
  · change lowerPayment 165 ≤ lowerValue ((point 2 split 4096 165+point 2 split 4096 166)/2)
    have hp : lowerPayment 165 = (25978265117:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 165+point 2 split 4096 166)/2 = (347152761:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((347152761:ℝ)/168755200)/ClassicalSixthBranch.v ((347152761:ℝ)/168755200) = (801219763657:ℝ)/412633154184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_165
  · change lowerPayment 166 ≤ lowerValue ((point 2 split 4096 166+point 2 split 4096 167)/2)
    have hp : lowerPayment 166 = (26129294658:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 166+point 2 split 4096 167)/2 = (347211023:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((347211023:ℝ)/168755200)/ClassicalSixthBranch.v ((347211023:ℝ)/168755200) = (801142449983:ℝ)/412585146296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_166
  · change lowerPayment 167 ≤ lowerValue ((point 2 split 4096 167+point 2 split 4096 168)/2)
    have hp : lowerPayment 167 = (26280256433:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 167+point 2 split 4096 168)/2 = (69453857:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((69453857:ℝ)/33751040)/ClassicalSixthBranch.v ((69453857:ℝ)/33751040) = (801065136309:ℝ)/412537138408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_167
  · change lowerPayment 168 ≤ lowerValue ((point 2 split 4096 168+point 2 split 4096 169)/2)
    have hp : lowerPayment 168 = (26431150503:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 168+point 2 split 4096 169)/2 = (347327547:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((347327547:ℝ)/168755200)/ClassicalSixthBranch.v ((347327547:ℝ)/168755200) = (160197564527:ℝ)/82497826104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_168
  · change lowerPayment 169 ≤ lowerValue ((point 2 split 4096 169+point 2 split 4096 170)/2)
    have hp : lowerPayment 169 = (26581976929:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 169+point 2 split 4096 170)/2 = (347385809:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((347385809:ℝ)/168755200)/ClassicalSixthBranch.v ((347385809:ℝ)/168755200) = (800910508961:ℝ)/412441122632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_169
  · change lowerPayment 170 ≤ lowerValue ((point 2 split 4096 170+point 2 split 4096 171)/2)
    have hp : lowerPayment 170 = (26732735773:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 170+point 2 split 4096 171)/2 = (347444071:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((347444071:ℝ)/168755200)/ClassicalSixthBranch.v ((347444071:ℝ)/168755200) = (800833195287:ℝ)/412393114744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_170
  · change lowerPayment 171 ≤ lowerValue ((point 2 split 4096 171+point 2 split 4096 172)/2)
    have hp : lowerPayment 171 = (26883427095:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 171+point 2 split 4096 172)/2 = (347502333:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((347502333:ℝ)/168755200)/ClassicalSixthBranch.v ((347502333:ℝ)/168755200) = (800755881613:ℝ)/412345106856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_171
  · change lowerPayment 172 ≤ lowerValue ((point 2 split 4096 172+point 2 split 4096 173)/2)
    have hp : lowerPayment 172 = (27034050957:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 172+point 2 split 4096 173)/2 = (69512119:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((69512119:ℝ)/33751040)/ClassicalSixthBranch.v ((69512119:ℝ)/33751040) = (800678567939:ℝ)/412297098968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_172
  · change lowerPayment 173 ≤ lowerValue ((point 2 split 4096 173+point 2 split 4096 174)/2)
    have hp : lowerPayment 173 = (27184607420:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 173+point 2 split 4096 174)/2 = (347618857:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((347618857:ℝ)/168755200)/ClassicalSixthBranch.v ((347618857:ℝ)/168755200) = (160120250853:ℝ)/82449818216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_173
  · change lowerPayment 174 ≤ lowerValue ((point 2 split 4096 174+point 2 split 4096 175)/2)
    have hp : lowerPayment 174 = (27335096543:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 174+point 2 split 4096 175)/2 = (347677119:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((347677119:ℝ)/168755200)/ClassicalSixthBranch.v ((347677119:ℝ)/168755200) = (800523940591:ℝ)/412201083192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_174
  · change lowerPayment 175 ≤ lowerValue ((point 2 split 4096 175+point 2 split 4096 176)/2)
    have hp : lowerPayment 175 = (27485518389:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 175+point 2 split 4096 176)/2 = (347735381:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((347735381:ℝ)/168755200)/ClassicalSixthBranch.v ((347735381:ℝ)/168755200) = (800446626917:ℝ)/412153075304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_175
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_010
