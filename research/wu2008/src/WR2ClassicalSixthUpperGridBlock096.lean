import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints096
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_096 (j : Fin 16) : upperPayment (16*96+j.val) ≤
    upperValue ((point split endpoint 4096 (16*96+j.val)+point split endpoint 4096 (16*96+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1536 ≤ upperValue ((point split endpoint 4096 1536+point split endpoint 4096 1537)/2)
    have hp : upperPayment 1536 = (316956290274:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1536+point split endpoint 4096 1537)/2 = (614794527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614794527:ℝ)/168755200)*ClassicalSixthBranch.v ((614794527:ℝ)/168755200)/ClassicalSixthBranch.r = (125381476291665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1536
  · change upperPayment 1537 ≤ upperValue ((point split endpoint 4096 1537+point split endpoint 4096 1538)/2)
    have hp : upperPayment 1537 = (316869391236:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1537+point split endpoint 4096 1538)/2 = (614819677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614819677:ℝ)/168755200)*ClassicalSixthBranch.v ((614819677:ℝ)/168755200)/ClassicalSixthBranch.r = (125358569973465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1537
  · change upperPayment 1538 ≤ upperValue ((point split endpoint 4096 1538+point split endpoint 4096 1539)/2)
    have hp : upperPayment 1538 = (316782468161:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1538+point split endpoint 4096 1539)/2 = (614844827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614844827:ℝ)/168755200)*ClassicalSixthBranch.v ((614844827:ℝ)/168755200)/ClassicalSixthBranch.r = (125335665679337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1538
  · change upperPayment 1539 ≤ upperValue ((point split endpoint 4096 1539+point split endpoint 4096 1540)/2)
    have hp : upperPayment 1539 = (316695521046:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1539+point split endpoint 4096 1540)/2 = (614869977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614869977:ℝ)/168755200)*ClassicalSixthBranch.v ((614869977:ℝ)/168755200)/ClassicalSixthBranch.r = (125312763409281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1539
  · change upperPayment 1540 ≤ upperValue ((point split endpoint 4096 1540+point split endpoint 4096 1541)/2)
    have hp : upperPayment 1540 = (316608549886:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1540+point split endpoint 4096 1541)/2 = (614895127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614895127:ℝ)/168755200)*ClassicalSixthBranch.v ((614895127:ℝ)/168755200)/ClassicalSixthBranch.r = (125289863163297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1540
  · change upperPayment 1541 ≤ upperValue ((point split endpoint 4096 1541+point split endpoint 4096 1542)/2)
    have hp : upperPayment 1541 = (316521554676:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1541+point split endpoint 4096 1542)/2 = (614920277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614920277:ℝ)/168755200)*ClassicalSixthBranch.v ((614920277:ℝ)/168755200)/ClassicalSixthBranch.r = (125266964941385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1541
  · change upperPayment 1542 ≤ upperValue ((point split endpoint 4096 1542+point split endpoint 4096 1543)/2)
    have hp : upperPayment 1542 = (316434535413:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1542+point split endpoint 4096 1543)/2 = (614945427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614945427:ℝ)/168755200)*ClassicalSixthBranch.v ((614945427:ℝ)/168755200)/ClassicalSixthBranch.r = (125244068743545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1542
  · change upperPayment 1543 ≤ upperValue ((point split endpoint 4096 1543+point split endpoint 4096 1544)/2)
    have hp : upperPayment 1543 = (316347492092:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1543+point split endpoint 4096 1544)/2 = (614970577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614970577:ℝ)/168755200)*ClassicalSixthBranch.v ((614970577:ℝ)/168755200)/ClassicalSixthBranch.r = (125221174569777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1543
  · change upperPayment 1544 ≤ upperValue ((point split endpoint 4096 1544+point split endpoint 4096 1545)/2)
    have hp : upperPayment 1544 = (316260424709:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1544+point split endpoint 4096 1545)/2 = (614995727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614995727:ℝ)/168755200)*ClassicalSixthBranch.v ((614995727:ℝ)/168755200)/ClassicalSixthBranch.r = (125198282420081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1544
  · change upperPayment 1545 ≤ upperValue ((point split endpoint 4096 1545+point split endpoint 4096 1546)/2)
    have hp : upperPayment 1545 = (316173333259:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1545+point split endpoint 4096 1546)/2 = (615020877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615020877:ℝ)/168755200)*ClassicalSixthBranch.v ((615020877:ℝ)/168755200)/ClassicalSixthBranch.r = (125175392294457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1545
  · change upperPayment 1546 ≤ upperValue ((point split endpoint 4096 1546+point split endpoint 4096 1547)/2)
    have hp : upperPayment 1546 = (316086217739:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1546+point split endpoint 4096 1547)/2 = (615046027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615046027:ℝ)/168755200)*ClassicalSixthBranch.v ((615046027:ℝ)/168755200)/ClassicalSixthBranch.r = (125152504192905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1546
  · change upperPayment 1547 ≤ upperValue ((point split endpoint 4096 1547+point split endpoint 4096 1548)/2)
    have hp : upperPayment 1547 = (315999078143:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1547+point split endpoint 4096 1548)/2 = (615071177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615071177:ℝ)/168755200)*ClassicalSixthBranch.v ((615071177:ℝ)/168755200)/ClassicalSixthBranch.r = (125129618115425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1547
  · change upperPayment 1548 ≤ upperValue ((point split endpoint 4096 1548+point split endpoint 4096 1549)/2)
    have hp : upperPayment 1548 = (315911914468:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1548+point split endpoint 4096 1549)/2 = (5971809:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((5971809:ℝ)/1638400)*ClassicalSixthBranch.v ((5971809:ℝ)/1638400)/ClassicalSixthBranch.r = (1214628486039:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1548
  · change upperPayment 1549 ≤ upperValue ((point split endpoint 4096 1549+point split endpoint 4096 1550)/2)
    have hp : upperPayment 1549 = (315824726710:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1549+point split endpoint 4096 1550)/2 = (615121477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615121477:ℝ)/168755200)*ClassicalSixthBranch.v ((615121477:ℝ)/168755200)/ClassicalSixthBranch.r = (125083852032681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1549
  · change upperPayment 1550 ≤ upperValue ((point split endpoint 4096 1550+point split endpoint 4096 1551)/2)
    have hp : upperPayment 1550 = (315737514863:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1550+point split endpoint 4096 1551)/2 = (615146627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615146627:ℝ)/168755200)*ClassicalSixthBranch.v ((615146627:ℝ)/168755200)/ClassicalSixthBranch.r = (125060972027417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1550
  · change upperPayment 1551 ≤ upperValue ((point split endpoint 4096 1551+point split endpoint 4096 1552)/2)
    have hp : upperPayment 1551 = (315650278924:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1551+point split endpoint 4096 1552)/2 = (615171777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615171777:ℝ)/168755200)*ClassicalSixthBranch.v ((615171777:ℝ)/168755200)/ClassicalSixthBranch.r = (125038094046225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1551
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_096
