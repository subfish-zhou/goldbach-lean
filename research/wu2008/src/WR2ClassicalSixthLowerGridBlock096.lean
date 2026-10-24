import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints096
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_096 (j : Fin 16) : lowerPayment (16*96+j.val) ≤
    lowerValue ((point 2 split 4096 (16*96+j.val)+point 2 split 4096 (16*96+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1536 ≤ lowerValue ((point 2 split 4096 1536+point 2 split 4096 1537)/2)
    have hp : lowerPayment 1536 = (189066062961:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1536+point 2 split 4096 1537)/2 = (427029963:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((427029963:ℝ)/168755200)/ClassicalSixthBranch.v ((427029963:ℝ)/168755200) = (695222716603:ℝ)/346814339736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1536
  · change lowerPayment 1537 ≤ lowerValue ((point 2 split 4096 1537+point 2 split 4096 1538)/2)
    have hp : lowerPayment 1537 = (189163777831:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1537+point 2 split 4096 1538)/2 = (17083529:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((17083529:ℝ)/6750208)/ClassicalSixthBranch.v ((17083529:ℝ)/6750208) = (695145402929:ℝ)/346766331848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1537
  · change lowerPayment 1538 ≤ lowerValue ((point 2 split 4096 1538+point 2 split 4096 1539)/2)
    have hp : lowerPayment 1538 = (189261473919:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1538+point 2 split 4096 1539)/2 = (427146487:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((427146487:ℝ)/168755200)/ClassicalSixthBranch.v ((427146487:ℝ)/168755200) = (139013617851:ℝ)/69343664792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1538
  · change lowerPayment 1539 ≤ lowerValue ((point 2 split 4096 1539+point 2 split 4096 1540)/2)
    have hp : lowerPayment 1539 = (189359151247:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1539+point 2 split 4096 1540)/2 = (427204749:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((427204749:ℝ)/168755200)/ClassicalSixthBranch.v ((427204749:ℝ)/168755200) = (694990775581:ℝ)/346670316072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1539
  · change lowerPayment 1540 ≤ lowerValue ((point 2 split 4096 1540+point 2 split 4096 1541)/2)
    have hp : lowerPayment 1540 = (189456809836:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1540+point 2 split 4096 1541)/2 = (427263011:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((427263011:ℝ)/168755200)/ClassicalSixthBranch.v ((427263011:ℝ)/168755200) = (694913461907:ℝ)/346622308184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1540
  · change lowerPayment 1541 ≤ lowerValue ((point 2 split 4096 1541+point 2 split 4096 1542)/2)
    have hp : lowerPayment 1541 = (189554449706:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1541+point 2 split 4096 1542)/2 = (427321273:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((427321273:ℝ)/168755200)/ClassicalSixthBranch.v ((427321273:ℝ)/168755200) = (694836148233:ℝ)/346574300296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1541
  · change lowerPayment 1542 ≤ lowerValue ((point 2 split 4096 1542+point 2 split 4096 1543)/2)
    have hp : lowerPayment 1542 = (189652070877:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1542+point 2 split 4096 1543)/2 = (85475907:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((85475907:ℝ)/33751040)/ClassicalSixthBranch.v ((85475907:ℝ)/33751040) = (694758834559:ℝ)/346526292408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1542
  · change lowerPayment 1543 ≤ lowerValue ((point 2 split 4096 1543+point 2 split 4096 1544)/2)
    have hp : lowerPayment 1543 = (189749673372:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1543+point 2 split 4096 1544)/2 = (427437797:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((427437797:ℝ)/168755200)/ClassicalSixthBranch.v ((427437797:ℝ)/168755200) = (138936304177:ℝ)/69295656904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1543
  · change lowerPayment 1544 ≤ lowerValue ((point 2 split 4096 1544+point 2 split 4096 1545)/2)
    have hp : lowerPayment 1544 = (189847257210:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1544+point 2 split 4096 1545)/2 = (427496059:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((427496059:ℝ)/168755200)/ClassicalSixthBranch.v ((427496059:ℝ)/168755200) = (694604207211:ℝ)/346430276632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1544
  · change lowerPayment 1545 ≤ lowerValue ((point 2 split 4096 1545+point 2 split 4096 1546)/2)
    have hp : lowerPayment 1545 = (189944822413:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1545+point 2 split 4096 1546)/2 = (427554321:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((427554321:ℝ)/168755200)/ClassicalSixthBranch.v ((427554321:ℝ)/168755200) = (694526893537:ℝ)/346382268744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1545
  · change lowerPayment 1546 ≤ lowerValue ((point 2 split 4096 1546+point 2 split 4096 1547)/2)
    have hp : lowerPayment 1546 = (190042369001:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1546+point 2 split 4096 1547)/2 = (427612583:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((427612583:ℝ)/168755200)/ClassicalSixthBranch.v ((427612583:ℝ)/168755200) = (694449579863:ℝ)/346334260856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1546
  · change lowerPayment 1547 ≤ lowerValue ((point 2 split 4096 1547+point 2 split 4096 1548)/2)
    have hp : lowerPayment 1547 = (190139896994:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1547+point 2 split 4096 1548)/2 = (85534169:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((85534169:ℝ)/33751040)/ClassicalSixthBranch.v ((85534169:ℝ)/33751040) = (694372266189:ℝ)/346286252968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1547
  · change lowerPayment 1548 ≤ lowerValue ((point 2 split 4096 1548+point 2 split 4096 1549)/2)
    have hp : lowerPayment 1548 = (190237406415:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1548+point 2 split 4096 1549)/2 = (427729107:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((427729107:ℝ)/168755200)/ClassicalSixthBranch.v ((427729107:ℝ)/168755200) = (138858990503:ℝ)/69247649016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1548
  · change lowerPayment 1549 ≤ lowerValue ((point 2 split 4096 1549+point 2 split 4096 1550)/2)
    have hp : lowerPayment 1549 = (190334897282:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1549+point 2 split 4096 1550)/2 = (427787369:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((427787369:ℝ)/168755200)/ClassicalSixthBranch.v ((427787369:ℝ)/168755200) = (694217638841:ℝ)/346190237192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1549
  · change lowerPayment 1550 ≤ lowerValue ((point 2 split 4096 1550+point 2 split 4096 1551)/2)
    have hp : lowerPayment 1550 = (190432369618:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1550+point 2 split 4096 1551)/2 = (427845631:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((427845631:ℝ)/168755200)/ClassicalSixthBranch.v ((427845631:ℝ)/168755200) = (694140325167:ℝ)/346142229304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1550
  · change lowerPayment 1551 ≤ lowerValue ((point 2 split 4096 1551+point 2 split 4096 1552)/2)
    have hp : lowerPayment 1551 = (190529823442:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1551+point 2 split 4096 1552)/2 = (427903893:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((427903893:ℝ)/168755200)/ClassicalSixthBranch.v ((427903893:ℝ)/168755200) = (694063011493:ℝ)/346094221416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1551
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_096
