import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints159
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_159 (j : Fin 16) : upperPayment (16*159+j.val) ≤
    upperValue ((point split endpoint 4096 (16*159+j.val)+point split endpoint 4096 (16*159+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2544 ≤ upperValue ((point split endpoint 4096 2544+point split endpoint 4096 2545)/2)
    have hp : upperPayment 2544 = (216352068955:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2544+point split endpoint 4096 2545)/2 = (640145727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640145727:ℝ)/168755200)*ClassicalSixthBranch.v ((640145727:ℝ)/168755200)/ClassicalSixthBranch.r = (103319180760081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2544
  · change upperPayment 2545 ≤ upperValue ((point split endpoint 4096 2545+point split endpoint 4096 2546)/2)
    have hp : upperPayment 2545 = (216238435655:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2545+point split endpoint 4096 2546)/2 = (640170877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640170877:ℝ)/168755200)*ClassicalSixthBranch.v ((640170877:ℝ)/168755200)/ClassicalSixthBranch.r = (103298314706457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2545
  · change upperPayment 2546 ≤ upperValue ((point split endpoint 4096 2546+point split endpoint 4096 2547)/2)
    have hp : upperPayment 2546 = (216124772981:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2546+point split endpoint 4096 2547)/2 = (640196027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640196027:ℝ)/168755200)*ClassicalSixthBranch.v ((640196027:ℝ)/168755200)/ClassicalSixthBranch.r = (103277450676905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2546
  · change upperPayment 2547 ≤ upperValue ((point split endpoint 4096 2547+point split endpoint 4096 2548)/2)
    have hp : upperPayment 2547 = (216011080927:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2547+point split endpoint 4096 2548)/2 = (640221177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640221177:ℝ)/168755200)*ClassicalSixthBranch.v ((640221177:ℝ)/168755200)/ClassicalSixthBranch.r = (103256588671425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2547
  · change upperPayment 2548 ≤ upperValue ((point split endpoint 4096 2548+point split endpoint 4096 2549)/2)
    have hp : upperPayment 2548 = (215897359485:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2548+point split endpoint 4096 2549)/2 = (640246327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640246327:ℝ)/168755200)*ClassicalSixthBranch.v ((640246327:ℝ)/168755200)/ClassicalSixthBranch.r = (103235728690017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2548
  · change upperPayment 2549 ≤ upperValue ((point split endpoint 4096 2549+point split endpoint 4096 2550)/2)
    have hp : upperPayment 2549 = (215783608649:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2549+point split endpoint 4096 2550)/2 = (640271477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640271477:ℝ)/168755200)*ClassicalSixthBranch.v ((640271477:ℝ)/168755200)/ClassicalSixthBranch.r = (103214870732681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2549
  · change upperPayment 2550 ≤ upperValue ((point split endpoint 4096 2550+point split endpoint 4096 2551)/2)
    have hp : upperPayment 2550 = (215669828414:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2550+point split endpoint 4096 2551)/2 = (640296627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640296627:ℝ)/168755200)*ClassicalSixthBranch.v ((640296627:ℝ)/168755200)/ClassicalSixthBranch.r = (103194014799417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2550
  · change upperPayment 2551 ≤ upperValue ((point split endpoint 4096 2551+point split endpoint 4096 2552)/2)
    have hp : upperPayment 2551 = (215556018772:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2551+point split endpoint 4096 2552)/2 = (640321777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640321777:ℝ)/168755200)*ClassicalSixthBranch.v ((640321777:ℝ)/168755200)/ClassicalSixthBranch.r = (103173160890225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2551
  · change upperPayment 2552 ≤ upperValue ((point split endpoint 4096 2552+point split endpoint 4096 2553)/2)
    have hp : upperPayment 2552 = (215442179717:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2552+point split endpoint 4096 2553)/2 = (640346927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640346927:ℝ)/168755200)*ClassicalSixthBranch.v ((640346927:ℝ)/168755200)/ClassicalSixthBranch.r = (103152309005105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2552
  · change upperPayment 2553 ≤ upperValue ((point split endpoint 4096 2553+point split endpoint 4096 2554)/2)
    have hp : upperPayment 2553 = (215328311242:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2553+point split endpoint 4096 2554)/2 = (640372077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640372077:ℝ)/168755200)*ClassicalSixthBranch.v ((640372077:ℝ)/168755200)/ClassicalSixthBranch.r = (103131459144057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2553
  · change upperPayment 2554 ≤ upperValue ((point split endpoint 4096 2554+point split endpoint 4096 2555)/2)
    have hp : upperPayment 2554 = (215214413342:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2554+point split endpoint 4096 2555)/2 = (640397227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640397227:ℝ)/168755200)*ClassicalSixthBranch.v ((640397227:ℝ)/168755200)/ClassicalSixthBranch.r = (103110611307081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2554
  · change upperPayment 2555 ≤ upperValue ((point split endpoint 4096 2555+point split endpoint 4096 2556)/2)
    have hp : upperPayment 2555 = (215100486010:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2555+point split endpoint 4096 2556)/2 = (640422377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640422377:ℝ)/168755200)*ClassicalSixthBranch.v ((640422377:ℝ)/168755200)/ClassicalSixthBranch.r = (103089765494177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2555
  · change upperPayment 2556 ≤ upperValue ((point split endpoint 4096 2556+point split endpoint 4096 2557)/2)
    have hp : upperPayment 2556 = (214986529239:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2556+point split endpoint 4096 2557)/2 = (640447527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640447527:ℝ)/168755200)*ClassicalSixthBranch.v ((640447527:ℝ)/168755200)/ClassicalSixthBranch.r = (103068921705345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2556
  · change upperPayment 2557 ≤ upperValue ((point split endpoint 4096 2557+point split endpoint 4096 2558)/2)
    have hp : upperPayment 2557 = (214872543022:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2557+point split endpoint 4096 2558)/2 = (640472677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640472677:ℝ)/168755200)*ClassicalSixthBranch.v ((640472677:ℝ)/168755200)/ClassicalSixthBranch.r = (103048079940585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2557
  · change upperPayment 2558 ≤ upperValue ((point split endpoint 4096 2558+point split endpoint 4096 2559)/2)
    have hp : upperPayment 2558 = (214758527354:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2558+point split endpoint 4096 2559)/2 = (640497827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640497827:ℝ)/168755200)*ClassicalSixthBranch.v ((640497827:ℝ)/168755200)/ClassicalSixthBranch.r = (103027240199897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2558
  · change upperPayment 2559 ≤ upperValue ((point split endpoint 4096 2559+point split endpoint 4096 2560)/2)
    have hp : upperPayment 2559 = (214644482227:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2559+point split endpoint 4096 2560)/2 = (640522977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640522977:ℝ)/168755200)*ClassicalSixthBranch.v ((640522977:ℝ)/168755200)/ClassicalSixthBranch.r = (103006402483281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2559
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_159
