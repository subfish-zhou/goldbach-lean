import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints079
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_079 (j : Fin 16) : upperPayment (16*79+j.val) ≤
    upperValue ((point split endpoint 4096 (16*79+j.val)+point split endpoint 4096 (16*79+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1264 ≤ upperValue ((point split endpoint 4096 1264+point split endpoint 4096 1265)/2)
    have hp : upperPayment 1264 = (339714529445:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1264+point split endpoint 4096 1265)/2 = (607953727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607953727:ℝ)/168755200)*ClassicalSixthBranch.v ((607953727:ℝ)/168755200)/ClassicalSixthBranch.r = (131687144587281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1264
  · change upperPayment 1265 ≤ upperValue ((point split endpoint 4096 1265+point split endpoint 4096 1266)/2)
    have hp : upperPayment 1265 = (339634015087:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1265+point split endpoint 4096 1266)/2 = (607978877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607978877:ℝ)/168755200)*ClassicalSixthBranch.v ((607978877:ℝ)/168755200)/ClassicalSixthBranch.r = (131663687721497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1265
  · change upperPayment 1266 ≤ upperValue ((point split endpoint 4096 1266+point split endpoint 4096 1267)/2)
    have hp : upperPayment 1266 = (339553477795:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1266+point split endpoint 4096 1267)/2 = (608004027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608004027:ℝ)/168755200)*ClassicalSixthBranch.v ((608004027:ℝ)/168755200)/ClassicalSixthBranch.r = (131640232879785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1266
  · change upperPayment 1267 ≤ upperValue ((point split endpoint 4096 1267+point split endpoint 4096 1268)/2)
    have hp : upperPayment 1267 = (339472917565:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1267+point split endpoint 4096 1268)/2 = (608029177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608029177:ℝ)/168755200)*ClassicalSixthBranch.v ((608029177:ℝ)/168755200)/ClassicalSixthBranch.r = (131616780062145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1267
  · change upperPayment 1268 ≤ upperValue ((point split endpoint 4096 1268+point split endpoint 4096 1269)/2)
    have hp : upperPayment 1268 = (339392334392:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1268+point split endpoint 4096 1269)/2 = (608054327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608054327:ℝ)/168755200)*ClassicalSixthBranch.v ((608054327:ℝ)/168755200)/ClassicalSixthBranch.r = (131593329268577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1268
  · change upperPayment 1269 ≤ upperValue ((point split endpoint 4096 1269+point split endpoint 4096 1270)/2)
    have hp : upperPayment 1269 = (339311728273:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1269+point split endpoint 4096 1270)/2 = (608079477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608079477:ℝ)/168755200)*ClassicalSixthBranch.v ((608079477:ℝ)/168755200)/ClassicalSixthBranch.r = (131569880499081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1269
  · change upperPayment 1270 ≤ upperValue ((point split endpoint 4096 1270+point split endpoint 4096 1271)/2)
    have hp : upperPayment 1270 = (339231099204:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1270+point split endpoint 4096 1271)/2 = (608104627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608104627:ℝ)/168755200)*ClassicalSixthBranch.v ((608104627:ℝ)/168755200)/ClassicalSixthBranch.r = (131546433753657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1270
  · change upperPayment 1271 ≤ upperValue ((point split endpoint 4096 1271+point split endpoint 4096 1272)/2)
    have hp : upperPayment 1271 = (339150447181:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1271+point split endpoint 4096 1272)/2 = (608129777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608129777:ℝ)/168755200)*ClassicalSixthBranch.v ((608129777:ℝ)/168755200)/ClassicalSixthBranch.r = (131522989032305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1271
  · change upperPayment 1272 ≤ upperValue ((point split endpoint 4096 1272+point split endpoint 4096 1273)/2)
    have hp : upperPayment 1272 = (339069772200:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1272+point split endpoint 4096 1273)/2 = (608154927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608154927:ℝ)/168755200)*ClassicalSixthBranch.v ((608154927:ℝ)/168755200)/ClassicalSixthBranch.r = (131499546335025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1272
  · change upperPayment 1273 ≤ upperValue ((point split endpoint 4096 1273+point split endpoint 4096 1274)/2)
    have hp : upperPayment 1273 = (338989074259:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1273+point split endpoint 4096 1274)/2 = (608180077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608180077:ℝ)/168755200)*ClassicalSixthBranch.v ((608180077:ℝ)/168755200)/ClassicalSixthBranch.r = (131476105661817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1273
  · change upperPayment 1274 ≤ upperValue ((point split endpoint 4096 1274+point split endpoint 4096 1275)/2)
    have hp : upperPayment 1274 = (338908353351:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1274+point split endpoint 4096 1275)/2 = (608205227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608205227:ℝ)/168755200)*ClassicalSixthBranch.v ((608205227:ℝ)/168755200)/ClassicalSixthBranch.r = (131452667012681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1274
  · change upperPayment 1275 ≤ upperValue ((point split endpoint 4096 1275+point split endpoint 4096 1276)/2)
    have hp : upperPayment 1275 = (338827609475:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1275+point split endpoint 4096 1276)/2 = (608230377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608230377:ℝ)/168755200)*ClassicalSixthBranch.v ((608230377:ℝ)/168755200)/ClassicalSixthBranch.r = (131429230387617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1275
  · change upperPayment 1276 ≤ upperValue ((point split endpoint 4096 1276+point split endpoint 4096 1277)/2)
    have hp : upperPayment 1276 = (338746842626:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1276+point split endpoint 4096 1277)/2 = (608255527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608255527:ℝ)/168755200)*ClassicalSixthBranch.v ((608255527:ℝ)/168755200)/ClassicalSixthBranch.r = (131405795786625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1276
  · change upperPayment 1277 ≤ upperValue ((point split endpoint 4096 1277+point split endpoint 4096 1278)/2)
    have hp : upperPayment 1277 = (338666052799:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1277+point split endpoint 4096 1278)/2 = (608280677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608280677:ℝ)/168755200)*ClassicalSixthBranch.v ((608280677:ℝ)/168755200)/ClassicalSixthBranch.r = (131382363209705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1277
  · change upperPayment 1278 ≤ upperValue ((point split endpoint 4096 1278+point split endpoint 4096 1279)/2)
    have hp : upperPayment 1278 = (338585239993:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1278+point split endpoint 4096 1279)/2 = (608305827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608305827:ℝ)/168755200)*ClassicalSixthBranch.v ((608305827:ℝ)/168755200)/ClassicalSixthBranch.r = (131358932656857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1278
  · change upperPayment 1279 ≤ upperValue ((point split endpoint 4096 1279+point split endpoint 4096 1280)/2)
    have hp : upperPayment 1279 = (338504404201:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1279+point split endpoint 4096 1280)/2 = (608330977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608330977:ℝ)/168755200)*ClassicalSixthBranch.v ((608330977:ℝ)/168755200)/ClassicalSixthBranch.r = (131335504128081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1279
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_079
