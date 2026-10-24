import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints085
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_085 (j : Fin 16) : lowerPayment (16*85+j.val) ≤
    lowerValue ((point 2 split 4096 (16*85+j.val)+point 2 split 4096 (16*85+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1360 ≤ lowerValue ((point 2 split 4096 1360+point 2 split 4096 1361)/2)
    have hp : lowerPayment 1360 = (171555942791:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1360+point 2 split 4096 1361)/2 = (416775851:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((416775851:ℝ)/168755200)/ClassicalSixthBranch.v ((416775851:ℝ)/168755200) = (708829923227:ℝ)/355263728024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1360
  · change lowerPayment 1361 ≤ lowerValue ((point 2 split 4096 1361+point 2 split 4096 1362)/2)
    have hp : lowerPayment 1361 = (171657299205:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1361+point 2 split 4096 1362)/2 = (416834113:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((416834113:ℝ)/168755200)/ClassicalSixthBranch.v ((416834113:ℝ)/168755200) = (708752609553:ℝ)/355215720136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1361
  · change lowerPayment 1362 ≤ lowerValue ((point 2 split 4096 1362+point 2 split 4096 1363)/2)
    have hp : lowerPayment 1362 = (171758632974:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1362+point 2 split 4096 1363)/2 = (16675695:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((16675695:ℝ)/6750208)/ClassicalSixthBranch.v ((16675695:ℝ)/6750208) = (708675295879:ℝ)/355167712248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1362
  · change lowerPayment 1363 ≤ lowerValue ((point 2 split 4096 1363+point 2 split 4096 1364)/2)
    have hp : lowerPayment 1363 = (171859944120:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1363+point 2 split 4096 1364)/2 = (416950637:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((416950637:ℝ)/168755200)/ClassicalSixthBranch.v ((416950637:ℝ)/168755200) = (141719596441:ℝ)/71023940872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1363
  · change lowerPayment 1364 ≤ lowerValue ((point 2 split 4096 1364+point 2 split 4096 1365)/2)
    have hp : lowerPayment 1364 = (171961232668:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1364+point 2 split 4096 1365)/2 = (417008899:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((417008899:ℝ)/168755200)/ClassicalSixthBranch.v ((417008899:ℝ)/168755200) = (708520668531:ℝ)/355071696472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1364
  · change lowerPayment 1365 ≤ lowerValue ((point 2 split 4096 1365+point 2 split 4096 1366)/2)
    have hp : lowerPayment 1365 = (172062498639:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1365+point 2 split 4096 1366)/2 = (417067161:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((417067161:ℝ)/168755200)/ClassicalSixthBranch.v ((417067161:ℝ)/168755200) = (708443354857:ℝ)/355023688584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1365
  · change lowerPayment 1366 ≤ lowerValue ((point 2 split 4096 1366+point 2 split 4096 1367)/2)
    have hp : lowerPayment 1366 = (172163742058:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1366+point 2 split 4096 1367)/2 = (417125423:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((417125423:ℝ)/168755200)/ClassicalSixthBranch.v ((417125423:ℝ)/168755200) = (708366041183:ℝ)/354975680696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1366
  · change lowerPayment 1367 ≤ lowerValue ((point 2 split 4096 1367+point 2 split 4096 1368)/2)
    have hp : lowerPayment 1367 = (172264962947:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1367+point 2 split 4096 1368)/2 = (83436737:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((83436737:ℝ)/33751040)/ClassicalSixthBranch.v ((83436737:ℝ)/33751040) = (708288727509:ℝ)/354927672808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1367
  · change lowerPayment 1368 ≤ lowerValue ((point 2 split 4096 1368+point 2 split 4096 1369)/2)
    have hp : lowerPayment 1368 = (172366161329:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1368+point 2 split 4096 1369)/2 = (417241947:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((417241947:ℝ)/168755200)/ClassicalSixthBranch.v ((417241947:ℝ)/168755200) = (141642282767:ℝ)/70975932984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1368
  · change lowerPayment 1369 ≤ lowerValue ((point 2 split 4096 1369+point 2 split 4096 1370)/2)
    have hp : lowerPayment 1369 = (172467337227:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1369+point 2 split 4096 1370)/2 = (417300209:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((417300209:ℝ)/168755200)/ClassicalSixthBranch.v ((417300209:ℝ)/168755200) = (708134100161:ℝ)/354831657032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1369
  · change lowerPayment 1370 ≤ lowerValue ((point 2 split 4096 1370+point 2 split 4096 1371)/2)
    have hp : lowerPayment 1370 = (172568490664:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1370+point 2 split 4096 1371)/2 = (417358471:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((417358471:ℝ)/168755200)/ClassicalSixthBranch.v ((417358471:ℝ)/168755200) = (708056786487:ℝ)/354783649144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1370
  · change lowerPayment 1371 ≤ lowerValue ((point 2 split 4096 1371+point 2 split 4096 1372)/2)
    have hp : lowerPayment 1371 = (172669621664:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1371+point 2 split 4096 1372)/2 = (417416733:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((417416733:ℝ)/168755200)/ClassicalSixthBranch.v ((417416733:ℝ)/168755200) = (707979472813:ℝ)/354735641256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1371
  · change lowerPayment 1372 ≤ lowerValue ((point 2 split 4096 1372+point 2 split 4096 1373)/2)
    have hp : lowerPayment 1372 = (172770730250:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1372+point 2 split 4096 1373)/2 = (83494999:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((83494999:ℝ)/33751040)/ClassicalSixthBranch.v ((83494999:ℝ)/33751040) = (707902159139:ℝ)/354687633368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1372
  · change lowerPayment 1373 ≤ lowerValue ((point 2 split 4096 1373+point 2 split 4096 1374)/2)
    have hp : lowerPayment 1373 = (172871816443:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1373+point 2 split 4096 1374)/2 = (417533257:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((417533257:ℝ)/168755200)/ClassicalSixthBranch.v ((417533257:ℝ)/168755200) = (141564969093:ℝ)/70927925096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1373
  · change lowerPayment 1374 ≤ lowerValue ((point 2 split 4096 1374+point 2 split 4096 1375)/2)
    have hp : lowerPayment 1374 = (172972880268:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1374+point 2 split 4096 1375)/2 = (417591519:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((417591519:ℝ)/168755200)/ClassicalSixthBranch.v ((417591519:ℝ)/168755200) = (707747531791:ℝ)/354591617592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1374
  · change lowerPayment 1375 ≤ lowerValue ((point 2 split 4096 1375+point 2 split 4096 1376)/2)
    have hp : lowerPayment 1375 = (173073921748:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1375+point 2 split 4096 1376)/2 = (417649781:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((417649781:ℝ)/168755200)/ClassicalSixthBranch.v ((417649781:ℝ)/168755200) = (707670218117:ℝ)/354543609704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1375
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_085
