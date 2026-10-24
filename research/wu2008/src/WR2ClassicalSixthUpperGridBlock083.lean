import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints083
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_083 (j : Fin 16) : upperPayment (16*83+j.val) ≤
    upperValue ((point split endpoint 4096 (16*83+j.val)+point split endpoint 4096 (16*83+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1328 ≤ upperValue ((point split endpoint 4096 1328+point split endpoint 4096 1329)/2)
    have hp : upperPayment 1328 = (334515213912:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1328+point split endpoint 4096 1329)/2 = (609563327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609563327:ℝ)/168755200)*ClassicalSixthBranch.v ((609563327:ℝ)/168755200)/ClassicalSixthBranch.r = (130189985706257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1328
  · change upperPayment 1329 ≤ upperValue ((point split endpoint 4096 1329+point split endpoint 4096 1330)/2)
    have hp : upperPayment 1329 = (334433223959:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1329+point split endpoint 4096 1330)/2 = (609588477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609588477:ℝ)/168755200)*ClassicalSixthBranch.v ((609588477:ℝ)/168755200)/ClassicalSixthBranch.r = (130166658381081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1329
  · change upperPayment 1330 ≤ upperValue ((point split endpoint 4096 1330+point split endpoint 4096 1331)/2)
    have hp : upperPayment 1330 = (334351210822:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1330+point split endpoint 4096 1331)/2 = (609613627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609613627:ℝ)/168755200)*ClassicalSixthBranch.v ((609613627:ℝ)/168755200)/ClassicalSixthBranch.r = (130143333079977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1330
  · change upperPayment 1331 ≤ upperValue ((point split endpoint 4096 1331+point split endpoint 4096 1332)/2)
    have hp : upperPayment 1331 = (334269174499:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1331+point split endpoint 4096 1332)/2 = (609638777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609638777:ℝ)/168755200)*ClassicalSixthBranch.v ((609638777:ℝ)/168755200)/ClassicalSixthBranch.r = (130120009802945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1331
  · change upperPayment 1332 ≤ upperValue ((point split endpoint 4096 1332+point split endpoint 4096 1333)/2)
    have hp : upperPayment 1332 = (334187114985:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1332+point split endpoint 4096 1333)/2 = (609663927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609663927:ℝ)/168755200)*ClassicalSixthBranch.v ((609663927:ℝ)/168755200)/ClassicalSixthBranch.r = (130096688549985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1332
  · change upperPayment 1333 ≤ upperValue ((point split endpoint 4096 1333+point split endpoint 4096 1334)/2)
    have hp : upperPayment 1333 = (334105032277:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1333+point split endpoint 4096 1334)/2 = (609689077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609689077:ℝ)/168755200)*ClassicalSixthBranch.v ((609689077:ℝ)/168755200)/ClassicalSixthBranch.r = (130073369321097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1333
  · change upperPayment 1334 ≤ upperValue ((point split endpoint 4096 1334+point split endpoint 4096 1335)/2)
    have hp : upperPayment 1334 = (334022926370:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1334+point split endpoint 4096 1335)/2 = (609714227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609714227:ℝ)/168755200)*ClassicalSixthBranch.v ((609714227:ℝ)/168755200)/ClassicalSixthBranch.r = (130050052116281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1334
  · change upperPayment 1335 ≤ upperValue ((point split endpoint 4096 1335+point split endpoint 4096 1336)/2)
    have hp : upperPayment 1335 = (333940797261:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1335+point split endpoint 4096 1336)/2 = (609739377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609739377:ℝ)/168755200)*ClassicalSixthBranch.v ((609739377:ℝ)/168755200)/ClassicalSixthBranch.r = (130026736935537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1335
  · change upperPayment 1336 ≤ upperValue ((point split endpoint 4096 1336+point split endpoint 4096 1337)/2)
    have hp : upperPayment 1336 = (333858644945:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1336+point split endpoint 4096 1337)/2 = (609764527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609764527:ℝ)/168755200)*ClassicalSixthBranch.v ((609764527:ℝ)/168755200)/ClassicalSixthBranch.r = (130003423778865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1336
  · change upperPayment 1337 ≤ upperValue ((point split endpoint 4096 1337+point split endpoint 4096 1338)/2)
    have hp : upperPayment 1337 = (333776469419:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1337+point split endpoint 4096 1338)/2 = (609789677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609789677:ℝ)/168755200)*ClassicalSixthBranch.v ((609789677:ℝ)/168755200)/ClassicalSixthBranch.r = (129980112646265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1337
  · change upperPayment 1338 ≤ upperValue ((point split endpoint 4096 1338+point split endpoint 4096 1339)/2)
    have hp : upperPayment 1338 = (333694270679:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1338+point split endpoint 4096 1339)/2 = (609814827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609814827:ℝ)/168755200)*ClassicalSixthBranch.v ((609814827:ℝ)/168755200)/ClassicalSixthBranch.r = (129956803537737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1338
  · change upperPayment 1339 ≤ upperValue ((point split endpoint 4096 1339+point split endpoint 4096 1340)/2)
    have hp : upperPayment 1339 = (333612048721:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1339+point split endpoint 4096 1340)/2 = (609839977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609839977:ℝ)/168755200)*ClassicalSixthBranch.v ((609839977:ℝ)/168755200)/ClassicalSixthBranch.r = (129933496453281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1339
  · change upperPayment 1340 ≤ upperValue ((point split endpoint 4096 1340+point split endpoint 4096 1341)/2)
    have hp : upperPayment 1340 = (333529803541:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1340+point split endpoint 4096 1341)/2 = (609865127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609865127:ℝ)/168755200)*ClassicalSixthBranch.v ((609865127:ℝ)/168755200)/ClassicalSixthBranch.r = (129910191392897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1340
  · change upperPayment 1341 ≤ upperValue ((point split endpoint 4096 1341+point split endpoint 4096 1342)/2)
    have hp : upperPayment 1341 = (333447535135:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1341+point split endpoint 4096 1342)/2 = (609890277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609890277:ℝ)/168755200)*ClassicalSixthBranch.v ((609890277:ℝ)/168755200)/ClassicalSixthBranch.r = (129886888356585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1341
  · change upperPayment 1342 ≤ upperValue ((point split endpoint 4096 1342+point split endpoint 4096 1343)/2)
    have hp : upperPayment 1342 = (333365243499:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1342+point split endpoint 4096 1343)/2 = (5921509:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((5921509:ℝ)/1638400)*ClassicalSixthBranch.v ((5921509:ℝ)/1638400)/ClassicalSixthBranch.r = (1260811527615:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1342
  · change upperPayment 1343 ≤ upperValue ((point split endpoint 4096 1343+point split endpoint 4096 1344)/2)
    have hp : upperPayment 1343 = (333282928628:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1343+point split endpoint 4096 1344)/2 = (609940577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609940577:ℝ)/168755200)*ClassicalSixthBranch.v ((609940577:ℝ)/168755200)/ClassicalSixthBranch.r = (129840288356177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1343
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_083
