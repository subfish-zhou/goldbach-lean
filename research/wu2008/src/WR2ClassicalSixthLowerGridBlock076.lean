import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints076
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_076 (j : Fin 16) : lowerPayment (16*76+j.val) ≤
    lowerValue ((point 2 split 4096 (16*76+j.val)+point 2 split 4096 (16*76+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1216 ≤ lowerValue ((point 2 split 4096 1216+point 2 split 4096 1217)/2)
    have hp : lowerPayment 1216 = (156712166797:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1216+point 2 split 4096 1217)/2 = (408386123:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((408386123:ℝ)/168755200)/ClassicalSixthBranch.v ((408386123:ℝ)/168755200) = (719963092283:ℝ)/362176863896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1216
  · change lowerPayment 1217 ≤ lowerValue ((point 2 split 4096 1217+point 2 split 4096 1218)/2)
    have hp : lowerPayment 1217 = (156817033358:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1217+point 2 split 4096 1218)/2 = (81688877:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((81688877:ℝ)/33751040)/ClassicalSixthBranch.v ((81688877:ℝ)/33751040) = (719885778609:ℝ)/362128856008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1217
  · change lowerPayment 1218 ≤ lowerValue ((point 2 split 4096 1218+point 2 split 4096 1219)/2)
    have hp : lowerPayment 1218 = (156921873782:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1218+point 2 split 4096 1219)/2 = (408502647:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((408502647:ℝ)/168755200)/ClassicalSixthBranch.v ((408502647:ℝ)/168755200) = (143961692987:ℝ)/72416169624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1218
  · change lowerPayment 1219 ≤ lowerValue ((point 2 split 4096 1219+point 2 split 4096 1220)/2)
    have hp : lowerPayment 1219 = (157026688095:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1219+point 2 split 4096 1220)/2 = (408560909:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((408560909:ℝ)/168755200)/ClassicalSixthBranch.v ((408560909:ℝ)/168755200) = (719731151261:ℝ)/362032840232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1219
  · change lowerPayment 1220 ≤ lowerValue ((point 2 split 4096 1220+point 2 split 4096 1221)/2)
    have hp : lowerPayment 1220 = (157131476321:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1220+point 2 split 4096 1221)/2 = (408619171:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((408619171:ℝ)/168755200)/ClassicalSixthBranch.v ((408619171:ℝ)/168755200) = (719653837587:ℝ)/361984832344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1220
  · change lowerPayment 1221 ≤ lowerValue ((point 2 split 4096 1221+point 2 split 4096 1222)/2)
    have hp : lowerPayment 1221 = (157236238487:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1221+point 2 split 4096 1222)/2 = (408677433:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((408677433:ℝ)/168755200)/ClassicalSixthBranch.v ((408677433:ℝ)/168755200) = (719576523913:ℝ)/361936824456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1221
  · change lowerPayment 1222 ≤ lowerValue ((point 2 split 4096 1222+point 2 split 4096 1223)/2)
    have hp : lowerPayment 1222 = (157340974618:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1222+point 2 split 4096 1223)/2 = (81747139:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((81747139:ℝ)/33751040)/ClassicalSixthBranch.v ((81747139:ℝ)/33751040) = (719499210239:ℝ)/361888816568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1222
  · change lowerPayment 1223 ≤ lowerValue ((point 2 split 4096 1223+point 2 split 4096 1224)/2)
    have hp : lowerPayment 1223 = (157445684739:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1223+point 2 split 4096 1224)/2 = (408793957:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((408793957:ℝ)/168755200)/ClassicalSixthBranch.v ((408793957:ℝ)/168755200) = (143884379313:ℝ)/72368161736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1223
  · change lowerPayment 1224 ≤ lowerValue ((point 2 split 4096 1224+point 2 split 4096 1225)/2)
    have hp : lowerPayment 1224 = (157550368875:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1224+point 2 split 4096 1225)/2 = (408852219:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((408852219:ℝ)/168755200)/ClassicalSixthBranch.v ((408852219:ℝ)/168755200) = (719344582891:ℝ)/361792800792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1224
  · change lowerPayment 1225 ≤ lowerValue ((point 2 split 4096 1225+point 2 split 4096 1226)/2)
    have hp : lowerPayment 1225 = (157655027051:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1225+point 2 split 4096 1226)/2 = (408910481:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((408910481:ℝ)/168755200)/ClassicalSixthBranch.v ((408910481:ℝ)/168755200) = (719267269217:ℝ)/361744792904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1225
  · change lowerPayment 1226 ≤ lowerValue ((point 2 split 4096 1226+point 2 split 4096 1227)/2)
    have hp : lowerPayment 1226 = (157759659294:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1226+point 2 split 4096 1227)/2 = (408968743:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((408968743:ℝ)/168755200)/ClassicalSixthBranch.v ((408968743:ℝ)/168755200) = (719189955543:ℝ)/361696785016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1226
  · change lowerPayment 1227 ≤ lowerValue ((point 2 split 4096 1227+point 2 split 4096 1228)/2)
    have hp : lowerPayment 1227 = (157864265628:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1227+point 2 split 4096 1228)/2 = (81805401:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((81805401:ℝ)/33751040)/ClassicalSixthBranch.v ((81805401:ℝ)/33751040) = (719112641869:ℝ)/361648777128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1227
  · change lowerPayment 1228 ≤ lowerValue ((point 2 split 4096 1228+point 2 split 4096 1229)/2)
    have hp : lowerPayment 1228 = (157968846078:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1228+point 2 split 4096 1229)/2 = (409085267:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((409085267:ℝ)/168755200)/ClassicalSixthBranch.v ((409085267:ℝ)/168755200) = (143807065639:ℝ)/72320153848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1228
  · change lowerPayment 1229 ≤ lowerValue ((point 2 split 4096 1229+point 2 split 4096 1230)/2)
    have hp : lowerPayment 1229 = (158073400670:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1229+point 2 split 4096 1230)/2 = (409143529:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((409143529:ℝ)/168755200)/ClassicalSixthBranch.v ((409143529:ℝ)/168755200) = (718958014521:ℝ)/361552761352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1229
  · change lowerPayment 1230 ≤ lowerValue ((point 2 split 4096 1230+point 2 split 4096 1231)/2)
    have hp : lowerPayment 1230 = (158177929429:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1230+point 2 split 4096 1231)/2 = (409201791:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((409201791:ℝ)/168755200)/ClassicalSixthBranch.v ((409201791:ℝ)/168755200) = (718880700847:ℝ)/361504753464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1230
  · change lowerPayment 1231 ≤ lowerValue ((point 2 split 4096 1231+point 2 split 4096 1232)/2)
    have hp : lowerPayment 1231 = (158282432380:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1231+point 2 split 4096 1232)/2 = (409260053:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((409260053:ℝ)/168755200)/ClassicalSixthBranch.v ((409260053:ℝ)/168755200) = (718803387173:ℝ)/361456745576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1231
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_076
