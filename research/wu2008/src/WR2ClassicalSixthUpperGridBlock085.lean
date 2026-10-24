import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints085
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_085 (j : Fin 16) : upperPayment (16*85+j.val) ≤
    upperValue ((point split endpoint 4096 (16*85+j.val)+point split endpoint 4096 (16*85+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1360 ≤ upperValue ((point split endpoint 4096 1360+point split endpoint 4096 1361)/2)
    have hp : upperPayment 1360 = (331880017209:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1360+point split endpoint 4096 1361)/2 = (610368127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610368127:ℝ)/168755200)*ClassicalSixthBranch.v ((610368127:ℝ)/168755200)/ClassicalSixthBranch.r = (129444515240337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1360
  · change upperPayment 1361 ≤ upperValue ((point split endpoint 4096 1361+point split endpoint 4096 1362)/2)
    have hp : upperPayment 1361 = (331797283451:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1361+point split endpoint 4096 1362)/2 = (610393277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610393277:ℝ)/168755200)*ClassicalSixthBranch.v ((610393277:ℝ)/168755200)/ClassicalSixthBranch.r = (129421252685465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1361
  · change upperPayment 1362 ≤ upperValue ((point split endpoint 4096 1362+point split endpoint 4096 1363)/2)
    have hp : upperPayment 1362 = (331714526384:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1362+point split endpoint 4096 1363)/2 = (610418427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610418427:ℝ)/168755200)*ClassicalSixthBranch.v ((610418427:ℝ)/168755200)/ClassicalSixthBranch.r = (129397992154665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1362
  · change upperPayment 1363 ≤ upperValue ((point split endpoint 4096 1363+point split endpoint 4096 1364)/2)
    have hp : upperPayment 1363 = (331631746003:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1363+point split endpoint 4096 1364)/2 = (610443577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610443577:ℝ)/168755200)*ClassicalSixthBranch.v ((610443577:ℝ)/168755200)/ClassicalSixthBranch.r = (129374733647937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1363
  · change upperPayment 1364 ≤ upperValue ((point split endpoint 4096 1364+point split endpoint 4096 1365)/2)
    have hp : upperPayment 1364 = (331548942305:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1364+point split endpoint 4096 1365)/2 = (610468727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610468727:ℝ)/168755200)*ClassicalSixthBranch.v ((610468727:ℝ)/168755200)/ClassicalSixthBranch.r = (129351477165281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1364
  · change upperPayment 1365 ≤ upperValue ((point split endpoint 4096 1365+point split endpoint 4096 1366)/2)
    have hp : upperPayment 1365 = (331466115286:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1365+point split endpoint 4096 1366)/2 = (610493877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610493877:ℝ)/168755200)*ClassicalSixthBranch.v ((610493877:ℝ)/168755200)/ClassicalSixthBranch.r = (129328222706697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1365
  · change upperPayment 1366 ≤ upperValue ((point split endpoint 4096 1366+point split endpoint 4096 1367)/2)
    have hp : upperPayment 1366 = (331383264941:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1366+point split endpoint 4096 1367)/2 = (610519027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610519027:ℝ)/168755200)*ClassicalSixthBranch.v ((610519027:ℝ)/168755200)/ClassicalSixthBranch.r = (1255388060895:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1366
  · change upperPayment 1367 ≤ upperValue ((point split endpoint 4096 1367+point split endpoint 4096 1368)/2)
    have hp : upperPayment 1367 = (331300391268:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1367+point split endpoint 4096 1368)/2 = (610544177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610544177:ℝ)/168755200)*ClassicalSixthBranch.v ((610544177:ℝ)/168755200)/ClassicalSixthBranch.r = (129281719861745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1367
  · change upperPayment 1368 ≤ upperValue ((point split endpoint 4096 1368+point split endpoint 4096 1369)/2)
    have hp : upperPayment 1368 = (331217494261:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1368+point split endpoint 4096 1369)/2 = (610569327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610569327:ℝ)/168755200)*ClassicalSixthBranch.v ((610569327:ℝ)/168755200)/ClassicalSixthBranch.r = (129258471475377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1368
  · change upperPayment 1369 ≤ upperValue ((point split endpoint 4096 1369+point split endpoint 4096 1370)/2)
    have hp : upperPayment 1369 = (331134573917:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1369+point split endpoint 4096 1370)/2 = (610594477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610594477:ℝ)/168755200)*ClassicalSixthBranch.v ((610594477:ℝ)/168755200)/ClassicalSixthBranch.r = (129235225113081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1369
  · change upperPayment 1370 ≤ upperValue ((point split endpoint 4096 1370+point split endpoint 4096 1371)/2)
    have hp : upperPayment 1370 = (331051630232:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1370+point split endpoint 4096 1371)/2 = (610619627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610619627:ℝ)/168755200)*ClassicalSixthBranch.v ((610619627:ℝ)/168755200)/ClassicalSixthBranch.r = (129211980774857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1370
  · change upperPayment 1371 ≤ upperValue ((point split endpoint 4096 1371+point split endpoint 4096 1372)/2)
    have hp : upperPayment 1371 = (330968663201:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1371+point split endpoint 4096 1372)/2 = (610644777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610644777:ℝ)/168755200)*ClassicalSixthBranch.v ((610644777:ℝ)/168755200)/ClassicalSixthBranch.r = (129188738460705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1371
  · change upperPayment 1372 ≤ upperValue ((point split endpoint 4096 1372+point split endpoint 4096 1373)/2)
    have hp : upperPayment 1372 = (330885672822:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1372+point split endpoint 4096 1373)/2 = (610669927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610669927:ℝ)/168755200)*ClassicalSixthBranch.v ((610669927:ℝ)/168755200)/ClassicalSixthBranch.r = (129165498170625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1372
  · change upperPayment 1373 ≤ upperValue ((point split endpoint 4096 1373+point split endpoint 4096 1374)/2)
    have hp : upperPayment 1373 = (330802659089:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1373+point split endpoint 4096 1374)/2 = (610695077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610695077:ℝ)/168755200)*ClassicalSixthBranch.v ((610695077:ℝ)/168755200)/ClassicalSixthBranch.r = (129142259904617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1373
  · change upperPayment 1374 ≤ upperValue ((point split endpoint 4096 1374+point split endpoint 4096 1375)/2)
    have hp : upperPayment 1374 = (330719621999:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1374+point split endpoint 4096 1375)/2 = (610720227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610720227:ℝ)/168755200)*ClassicalSixthBranch.v ((610720227:ℝ)/168755200)/ClassicalSixthBranch.r = (129119023662681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1374
  · change upperPayment 1375 ≤ upperValue ((point split endpoint 4096 1375+point split endpoint 4096 1376)/2)
    have hp : upperPayment 1375 = (330636561548:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1375+point split endpoint 4096 1376)/2 = (610745377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610745377:ℝ)/168755200)*ClassicalSixthBranch.v ((610745377:ℝ)/168755200)/ClassicalSixthBranch.r = (129095789444817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1375
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_085
