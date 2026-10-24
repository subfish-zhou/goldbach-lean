import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints082
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_082 (j : Fin 16) : upperPayment (16*82+j.val) ≤
    upperValue ((point split endpoint 4096 (16*82+j.val)+point split endpoint 4096 (16*82+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1312 ≤ upperValue ((point split endpoint 4096 1312+point split endpoint 4096 1313)/2)
    have hp : upperPayment 1312 = (335823903524:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1312+point split endpoint 4096 1313)/2 = (609160927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609160927:ℝ)/168755200)*ClassicalSixthBranch.v ((609160927:ℝ)/168755200)/ClassicalSixthBranch.r = (130563498182865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1312
  · change upperPayment 1313 ≤ upperValue ((point split endpoint 4096 1313+point split endpoint 4096 1314)/2)
    have hp : upperPayment 1313 = (335742283961:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1313+point split endpoint 4096 1314)/2 = (609186077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609186077:ℝ)/168755200)*ClassicalSixthBranch.v ((609186077:ℝ)/168755200)/ClassicalSixthBranch.r = (130540138472537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1313
  · change upperPayment 1314 ≤ upperValue ((point split endpoint 4096 1314+point split endpoint 4096 1315)/2)
    have hp : upperPayment 1314 = (335660641278:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1314+point split endpoint 4096 1315)/2 = (609211227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609211227:ℝ)/168755200)*ClassicalSixthBranch.v ((609211227:ℝ)/168755200)/ClassicalSixthBranch.r = (130516780786281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1314
  · change upperPayment 1315 ≤ upperValue ((point split endpoint 4096 1315+point split endpoint 4096 1316)/2)
    have hp : upperPayment 1315 = (335578975470:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1315+point split endpoint 4096 1316)/2 = (609236377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609236377:ℝ)/168755200)*ClassicalSixthBranch.v ((609236377:ℝ)/168755200)/ClassicalSixthBranch.r = (130493425124097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1315
  · change upperPayment 1316 ≤ upperValue ((point split endpoint 4096 1316+point split endpoint 4096 1317)/2)
    have hp : upperPayment 1316 = (335497286535:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1316+point split endpoint 4096 1317)/2 = (609261527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609261527:ℝ)/168755200)*ClassicalSixthBranch.v ((609261527:ℝ)/168755200)/ClassicalSixthBranch.r = (130470071485985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1316
  · change upperPayment 1317 ≤ upperValue ((point split endpoint 4096 1317+point split endpoint 4096 1318)/2)
    have hp : upperPayment 1317 = (335415574468:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1317+point split endpoint 4096 1318)/2 = (609286677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609286677:ℝ)/168755200)*ClassicalSixthBranch.v ((609286677:ℝ)/168755200)/ClassicalSixthBranch.r = (130446719871945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1317
  · change upperPayment 1318 ≤ upperValue ((point split endpoint 4096 1318+point split endpoint 4096 1319)/2)
    have hp : upperPayment 1318 = (335333839265:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1318+point split endpoint 4096 1319)/2 = (609311827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609311827:ℝ)/168755200)*ClassicalSixthBranch.v ((609311827:ℝ)/168755200)/ClassicalSixthBranch.r = (130423370281977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1318
  · change upperPayment 1319 ≤ upperValue ((point split endpoint 4096 1319+point split endpoint 4096 1320)/2)
    have hp : upperPayment 1319 = (335252080922:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1319+point split endpoint 4096 1320)/2 = (609336977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609336977:ℝ)/168755200)*ClassicalSixthBranch.v ((609336977:ℝ)/168755200)/ClassicalSixthBranch.r = (130400022716081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1319
  · change upperPayment 1320 ≤ upperValue ((point split endpoint 4096 1320+point split endpoint 4096 1321)/2)
    have hp : upperPayment 1320 = (335170299437:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1320+point split endpoint 4096 1321)/2 = (609362127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609362127:ℝ)/168755200)*ClassicalSixthBranch.v ((609362127:ℝ)/168755200)/ClassicalSixthBranch.r = (130376677174257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1320
  · change upperPayment 1321 ≤ upperValue ((point split endpoint 4096 1321+point split endpoint 4096 1322)/2)
    have hp : upperPayment 1321 = (335088494803:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1321+point split endpoint 4096 1322)/2 = (609387277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609387277:ℝ)/168755200)*ClassicalSixthBranch.v ((609387277:ℝ)/168755200)/ClassicalSixthBranch.r = (130353333656505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1321
  · change upperPayment 1322 ≤ upperValue ((point split endpoint 4096 1322+point split endpoint 4096 1323)/2)
    have hp : upperPayment 1322 = (335006667018:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1322+point split endpoint 4096 1323)/2 = (609412427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609412427:ℝ)/168755200)*ClassicalSixthBranch.v ((609412427:ℝ)/168755200)/ClassicalSixthBranch.r = (130329992162825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1322
  · change upperPayment 1323 ≤ upperValue ((point split endpoint 4096 1323+point split endpoint 4096 1324)/2)
    have hp : upperPayment 1323 = (334924816078:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1323+point split endpoint 4096 1324)/2 = (609437577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609437577:ℝ)/168755200)*ClassicalSixthBranch.v ((609437577:ℝ)/168755200)/ClassicalSixthBranch.r = (130306652693217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1323
  · change upperPayment 1324 ≤ upperValue ((point split endpoint 4096 1324+point split endpoint 4096 1325)/2)
    have hp : upperPayment 1324 = (334842941979:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1324+point split endpoint 4096 1325)/2 = (609462727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609462727:ℝ)/168755200)*ClassicalSixthBranch.v ((609462727:ℝ)/168755200)/ClassicalSixthBranch.r = (130283315247681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1324
  · change upperPayment 1325 ≤ upperValue ((point split endpoint 4096 1325+point split endpoint 4096 1326)/2)
    have hp : upperPayment 1325 = (334761044717:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1325+point split endpoint 4096 1326)/2 = (609487877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609487877:ℝ)/168755200)*ClassicalSixthBranch.v ((609487877:ℝ)/168755200)/ClassicalSixthBranch.r = (130259979826217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1325
  · change upperPayment 1326 ≤ upperValue ((point split endpoint 4096 1326+point split endpoint 4096 1327)/2)
    have hp : upperPayment 1326 = (334679124288:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1326+point split endpoint 4096 1327)/2 = (609513027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609513027:ℝ)/168755200)*ClassicalSixthBranch.v ((609513027:ℝ)/168755200)/ClassicalSixthBranch.r = (130236646428825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1326
  · change upperPayment 1327 ≤ upperValue ((point split endpoint 4096 1327+point split endpoint 4096 1328)/2)
    have hp : upperPayment 1327 = (334597180688:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1327+point split endpoint 4096 1328)/2 = (609538177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609538177:ℝ)/168755200)*ClassicalSixthBranch.v ((609538177:ℝ)/168755200)/ClassicalSixthBranch.r = (130213315055505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1327
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_082
