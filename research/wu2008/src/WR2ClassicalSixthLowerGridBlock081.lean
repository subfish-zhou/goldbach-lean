import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints081
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_081 (j : Fin 16) : lowerPayment (16*81+j.val) ≤
    lowerValue ((point 2 split 4096 (16*81+j.val)+point 2 split 4096 (16*81+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1296 ≤ lowerValue ((point 2 split 4096 1296+point 2 split 4096 1297)/2)
    have hp : lowerPayment 1296 = (165020959919:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1296+point 2 split 4096 1297)/2 = (413047083:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((413047083:ℝ)/168755200)/ClassicalSixthBranch.v ((413047083:ℝ)/168755200) = (713777998363:ℝ)/358336232856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1296
  · change lowerPayment 1297 ≤ lowerValue ((point 2 split 4096 1297+point 2 split 4096 1298)/2)
    have hp : lowerPayment 1297 = (165123814436:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1297+point 2 split 4096 1298)/2 = (82621069:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((82621069:ℝ)/33751040)/ClassicalSixthBranch.v ((82621069:ℝ)/33751040) = (713700684689:ℝ)/358288224968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1297
  · change lowerPayment 1298 ≤ lowerValue ((point 2 split 4096 1298+point 2 split 4096 1299)/2)
    have hp : lowerPayment 1298 = (165226644796:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1298+point 2 split 4096 1299)/2 = (413163607:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((413163607:ℝ)/168755200)/ClassicalSixthBranch.v ((413163607:ℝ)/168755200) = (142724674203:ℝ)/71648043416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1298
  · change lowerPayment 1299 ≤ lowerValue ((point 2 split 4096 1299+point 2 split 4096 1300)/2)
    have hp : lowerPayment 1299 = (165329451023:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1299+point 2 split 4096 1300)/2 = (413221869:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((413221869:ℝ)/168755200)/ClassicalSixthBranch.v ((413221869:ℝ)/168755200) = (713546057341:ℝ)/358192209192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1299
  · change lowerPayment 1300 ≤ lowerValue ((point 2 split 4096 1300+point 2 split 4096 1301)/2)
    have hp : lowerPayment 1300 = (165432233141:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1300+point 2 split 4096 1301)/2 = (413280131:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((413280131:ℝ)/168755200)/ClassicalSixthBranch.v ((413280131:ℝ)/168755200) = (713468743667:ℝ)/358144201304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1300
  · change lowerPayment 1301 ≤ lowerValue ((point 2 split 4096 1301+point 2 split 4096 1302)/2)
    have hp : lowerPayment 1301 = (165534991174:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1301+point 2 split 4096 1302)/2 = (413338393:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((413338393:ℝ)/168755200)/ClassicalSixthBranch.v ((413338393:ℝ)/168755200) = (713391429993:ℝ)/358096193416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1301
  · change lowerPayment 1302 ≤ lowerValue ((point 2 split 4096 1302+point 2 split 4096 1303)/2)
    have hp : lowerPayment 1302 = (165637725147:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1302+point 2 split 4096 1303)/2 = (82679331:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((82679331:ℝ)/33751040)/ClassicalSixthBranch.v ((82679331:ℝ)/33751040) = (713314116319:ℝ)/358048185528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1302
  · change lowerPayment 1303 ≤ lowerValue ((point 2 split 4096 1303+point 2 split 4096 1304)/2)
    have hp : lowerPayment 1303 = (165740435083:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1303+point 2 split 4096 1304)/2 = (413454917:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((413454917:ℝ)/168755200)/ClassicalSixthBranch.v ((413454917:ℝ)/168755200) = (142647360529:ℝ)/71600035528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1303
  · change lowerPayment 1304 ≤ lowerValue ((point 2 split 4096 1304+point 2 split 4096 1305)/2)
    have hp : lowerPayment 1304 = (165843121007:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1304+point 2 split 4096 1305)/2 = (413513179:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((413513179:ℝ)/168755200)/ClassicalSixthBranch.v ((413513179:ℝ)/168755200) = (713159488971:ℝ)/357952169752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1304
  · change lowerPayment 1305 ≤ lowerValue ((point 2 split 4096 1305+point 2 split 4096 1306)/2)
    have hp : lowerPayment 1305 = (165945782942:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1305+point 2 split 4096 1306)/2 = (413571441:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((413571441:ℝ)/168755200)/ClassicalSixthBranch.v ((413571441:ℝ)/168755200) = (713082175297:ℝ)/357904161864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1305
  · change lowerPayment 1306 ≤ lowerValue ((point 2 split 4096 1306+point 2 split 4096 1307)/2)
    have hp : lowerPayment 1306 = (166048420912:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1306+point 2 split 4096 1307)/2 = (413629703:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((413629703:ℝ)/168755200)/ClassicalSixthBranch.v ((413629703:ℝ)/168755200) = (713004861623:ℝ)/357856153976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1306
  · change lowerPayment 1307 ≤ lowerValue ((point 2 split 4096 1307+point 2 split 4096 1308)/2)
    have hp : lowerPayment 1307 = (166151034942:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1307+point 2 split 4096 1308)/2 = (82737593:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((82737593:ℝ)/33751040)/ClassicalSixthBranch.v ((82737593:ℝ)/33751040) = (712927547949:ℝ)/357808146088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1307
  · change lowerPayment 1308 ≤ lowerValue ((point 2 split 4096 1308+point 2 split 4096 1309)/2)
    have hp : lowerPayment 1308 = (166253625055:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1308+point 2 split 4096 1309)/2 = (413746227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((413746227:ℝ)/168755200)/ClassicalSixthBranch.v ((413746227:ℝ)/168755200) = (28514009371:ℝ)/14310405528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1308
  · change lowerPayment 1309 ≤ lowerValue ((point 2 split 4096 1309+point 2 split 4096 1310)/2)
    have hp : lowerPayment 1309 = (166356191275:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1309+point 2 split 4096 1310)/2 = (413804489:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((413804489:ℝ)/168755200)/ClassicalSixthBranch.v ((413804489:ℝ)/168755200) = (712772920601:ℝ)/357712130312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1309
  · change lowerPayment 1310 ≤ lowerValue ((point 2 split 4096 1310+point 2 split 4096 1311)/2)
    have hp : lowerPayment 1310 = (166458733626:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1310+point 2 split 4096 1311)/2 = (413862751:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((413862751:ℝ)/168755200)/ClassicalSixthBranch.v ((413862751:ℝ)/168755200) = (712695606927:ℝ)/357664122424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1310
  · change lowerPayment 1311 ≤ lowerValue ((point 2 split 4096 1311+point 2 split 4096 1312)/2)
    have hp : lowerPayment 1311 = (166561252133:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1311+point 2 split 4096 1312)/2 = (413921013:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((413921013:ℝ)/168755200)/ClassicalSixthBranch.v ((413921013:ℝ)/168755200) = (712618293253:ℝ)/357616114536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1311
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_081
