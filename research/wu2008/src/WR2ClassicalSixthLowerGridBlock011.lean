import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints011
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_011 (j : Fin 16) : lowerPayment (16*11+j.val) ≤
    lowerValue ((point 2 split 4096 (16*11+j.val)+point 2 split 4096 (16*11+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 176 ≤ lowerValue ((point 2 split 4096 176+point 2 split 4096 177)/2)
    have hp : lowerPayment 176 = (27635873018:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 176+point 2 split 4096 177)/2 = (347793643:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((347793643:ℝ)/168755200)/ClassicalSixthBranch.v ((347793643:ℝ)/168755200) = (800369313243:ℝ)/412105067416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_176
  · change lowerPayment 177 ≤ lowerValue ((point 2 split 4096 177+point 2 split 4096 178)/2)
    have hp : lowerPayment 177 = (27786160490:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 177+point 2 split 4096 178)/2 = (69570381:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((69570381:ℝ)/33751040)/ClassicalSixthBranch.v ((69570381:ℝ)/33751040) = (800291999569:ℝ)/412057059528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_177
  · change lowerPayment 178 ≤ lowerValue ((point 2 split 4096 178+point 2 split 4096 179)/2)
    have hp : lowerPayment 178 = (27936380867:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 178+point 2 split 4096 179)/2 = (347910167:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((347910167:ℝ)/168755200)/ClassicalSixthBranch.v ((347910167:ℝ)/168755200) = (160042937179:ℝ)/82401810328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_178
  · change lowerPayment 179 ≤ lowerValue ((point 2 split 4096 179+point 2 split 4096 180)/2)
    have hp : lowerPayment 179 = (28086534208:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 179+point 2 split 4096 180)/2 = (347968429:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((347968429:ℝ)/168755200)/ClassicalSixthBranch.v ((347968429:ℝ)/168755200) = (800137372221:ℝ)/411961043752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_179
  · change lowerPayment 180 ≤ lowerValue ((point 2 split 4096 180+point 2 split 4096 181)/2)
    have hp : lowerPayment 180 = (28236620575:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 180+point 2 split 4096 181)/2 = (348026691:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((348026691:ℝ)/168755200)/ClassicalSixthBranch.v ((348026691:ℝ)/168755200) = (800060058547:ℝ)/411913035864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_180
  · change lowerPayment 181 ≤ lowerValue ((point 2 split 4096 181+point 2 split 4096 182)/2)
    have hp : lowerPayment 181 = (28386640027:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 181+point 2 split 4096 182)/2 = (348084953:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((348084953:ℝ)/168755200)/ClassicalSixthBranch.v ((348084953:ℝ)/168755200) = (799982744873:ℝ)/411865027976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_181
  · change lowerPayment 182 ≤ lowerValue ((point 2 split 4096 182+point 2 split 4096 183)/2)
    have hp : lowerPayment 182 = (28536592626:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 182+point 2 split 4096 183)/2 = (69628643:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((69628643:ℝ)/33751040)/ClassicalSixthBranch.v ((69628643:ℝ)/33751040) = (799905431199:ℝ)/411817020088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_182
  · change lowerPayment 183 ≤ lowerValue ((point 2 split 4096 183+point 2 split 4096 184)/2)
    have hp : lowerPayment 183 = (28686478431:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 183+point 2 split 4096 184)/2 = (348201477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((348201477:ℝ)/168755200)/ClassicalSixthBranch.v ((348201477:ℝ)/168755200) = (31993124701:ℝ)/16470760488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_183
  · change lowerPayment 184 ≤ lowerValue ((point 2 split 4096 184+point 2 split 4096 185)/2)
    have hp : lowerPayment 184 = (28836297503:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 184+point 2 split 4096 185)/2 = (348259739:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((348259739:ℝ)/168755200)/ClassicalSixthBranch.v ((348259739:ℝ)/168755200) = (799750803851:ℝ)/411721004312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_184
  · change lowerPayment 185 ≤ lowerValue ((point 2 split 4096 185+point 2 split 4096 186)/2)
    have hp : lowerPayment 185 = (28986049902:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 185+point 2 split 4096 186)/2 = (348318001:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((348318001:ℝ)/168755200)/ClassicalSixthBranch.v ((348318001:ℝ)/168755200) = (799673490177:ℝ)/411672996424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_185
  · change lowerPayment 186 ≤ lowerValue ((point 2 split 4096 186+point 2 split 4096 187)/2)
    have hp : lowerPayment 186 = (29135735689:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 186+point 2 split 4096 187)/2 = (348376263:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((348376263:ℝ)/168755200)/ClassicalSixthBranch.v ((348376263:ℝ)/168755200) = (799596176503:ℝ)/411624988536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_186
  · change lowerPayment 187 ≤ lowerValue ((point 2 split 4096 187+point 2 split 4096 188)/2)
    have hp : lowerPayment 187 = (29285354922:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 187+point 2 split 4096 188)/2 = (13937381:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((13937381:ℝ)/6750208)/ClassicalSixthBranch.v ((13937381:ℝ)/6750208) = (799518862829:ℝ)/411576980648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_187
  · change lowerPayment 188 ≤ lowerValue ((point 2 split 4096 188+point 2 split 4096 189)/2)
    have hp : lowerPayment 188 = (29434907663:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 188+point 2 split 4096 189)/2 = (348492787:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((348492787:ℝ)/168755200)/ClassicalSixthBranch.v ((348492787:ℝ)/168755200) = (159888309831:ℝ)/82305794552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_188
  · change lowerPayment 189 ≤ lowerValue ((point 2 split 4096 189+point 2 split 4096 190)/2)
    have hp : lowerPayment 189 = (29584393971:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 189+point 2 split 4096 190)/2 = (348551049:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((348551049:ℝ)/168755200)/ClassicalSixthBranch.v ((348551049:ℝ)/168755200) = (799364235481:ℝ)/411480964872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_189
  · change lowerPayment 190 ≤ lowerValue ((point 2 split 4096 190+point 2 split 4096 191)/2)
    have hp : lowerPayment 190 = (29733813907:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 190+point 2 split 4096 191)/2 = (348609311:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((348609311:ℝ)/168755200)/ClassicalSixthBranch.v ((348609311:ℝ)/168755200) = (799286921807:ℝ)/411432956984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_190
  · change lowerPayment 191 ≤ lowerValue ((point 2 split 4096 191+point 2 split 4096 192)/2)
    have hp : lowerPayment 191 = (29883167529:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 191+point 2 split 4096 192)/2 = (348667573:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((348667573:ℝ)/168755200)/ClassicalSixthBranch.v ((348667573:ℝ)/168755200) = (799209608133:ℝ)/411384949096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_191
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_011
