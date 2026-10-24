import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints226
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_226 (j : Fin 16) : upperPayment (16*226+j.val) ≤
    upperValue ((point split endpoint 4096 (16*226+j.val)+point split endpoint 4096 (16*226+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3616 ≤ upperValue ((point split endpoint 4096 3616+point split endpoint 4096 3617)/2)
    have hp : upperPayment 3616 = (76199913891:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3616+point split endpoint 4096 3617)/2 = (667106527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667106527:ℝ)/168755200)*ClassicalSixthBranch.v ((667106527:ℝ)/168755200)/ClassicalSixthBranch.r = (82112701951185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3616
  · change upperPayment 3617 ≤ upperValue ((point split endpoint 4096 3617+point split endpoint 4096 3618)/2)
    have hp : upperPayment 3617 = (76050496065:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3617+point split endpoint 4096 3618)/2 = (667131677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667131677:ℝ)/168755200)*ClassicalSixthBranch.v ((667131677:ℝ)/168755200)/ClassicalSixthBranch.r = (82094005702745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3617
  · change upperPayment 3618 ≤ upperValue ((point split endpoint 4096 3618+point split endpoint 4096 3619)/2)
    have hp : upperPayment 3618 = (75901040213:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3618+point split endpoint 4096 3619)/2 = (667156827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667156827:ℝ)/168755200)*ClassicalSixthBranch.v ((667156827:ℝ)/168755200)/ClassicalSixthBranch.r = (82075311478377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3618
  · change upperPayment 3619 ≤ upperValue ((point split endpoint 4096 3619+point split endpoint 4096 3620)/2)
    have hp : upperPayment 3619 = (75751546327:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3619+point split endpoint 4096 3620)/2 = (667181977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667181977:ℝ)/168755200)*ClassicalSixthBranch.v ((667181977:ℝ)/168755200)/ClassicalSixthBranch.r = (82056619278081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3619
  · change upperPayment 3620 ≤ upperValue ((point split endpoint 4096 3620+point split endpoint 4096 3621)/2)
    have hp : upperPayment 3620 = (75602014395:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3620+point split endpoint 4096 3621)/2 = (667207127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667207127:ℝ)/168755200)*ClassicalSixthBranch.v ((667207127:ℝ)/168755200)/ClassicalSixthBranch.r = (82037929101857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3620
  · change upperPayment 3621 ≤ upperValue ((point split endpoint 4096 3621+point split endpoint 4096 3622)/2)
    have hp : upperPayment 3621 = (75452444409:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3621+point split endpoint 4096 3622)/2 = (667232277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667232277:ℝ)/168755200)*ClassicalSixthBranch.v ((667232277:ℝ)/168755200)/ClassicalSixthBranch.r = (82019240949705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3621
  · change upperPayment 3622 ≤ upperValue ((point split endpoint 4096 3622+point split endpoint 4096 3623)/2)
    have hp : upperPayment 3622 = (75302836358:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3622+point split endpoint 4096 3623)/2 = (667257427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667257427:ℝ)/168755200)*ClassicalSixthBranch.v ((667257427:ℝ)/168755200)/ClassicalSixthBranch.r = (82000554821625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3622
  · change upperPayment 3623 ≤ upperValue ((point split endpoint 4096 3623+point split endpoint 4096 3624)/2)
    have hp : upperPayment 3623 = (75153190233:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3623+point split endpoint 4096 3624)/2 = (667282577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667282577:ℝ)/168755200)*ClassicalSixthBranch.v ((667282577:ℝ)/168755200)/ClassicalSixthBranch.r = (81981870717617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3623
  · change upperPayment 3624 ≤ upperValue ((point split endpoint 4096 3624+point split endpoint 4096 3625)/2)
    have hp : upperPayment 3624 = (75003506022:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3624+point split endpoint 4096 3625)/2 = (667307727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667307727:ℝ)/168755200)*ClassicalSixthBranch.v ((667307727:ℝ)/168755200)/ClassicalSixthBranch.r = (81963188637681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3624
  · change upperPayment 3625 ≤ upperValue ((point split endpoint 4096 3625+point split endpoint 4096 3626)/2)
    have hp : upperPayment 3625 = (74853783717:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3625+point split endpoint 4096 3626)/2 = (667332877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667332877:ℝ)/168755200)*ClassicalSixthBranch.v ((667332877:ℝ)/168755200)/ClassicalSixthBranch.r = (81944508581817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3625
  · change upperPayment 3626 ≤ upperValue ((point split endpoint 4096 3626+point split endpoint 4096 3627)/2)
    have hp : upperPayment 3626 = (74704023307:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3626+point split endpoint 4096 3627)/2 = (667358027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667358027:ℝ)/168755200)*ClassicalSixthBranch.v ((667358027:ℝ)/168755200)/ClassicalSixthBranch.r = (81925830550025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3626
  · change upperPayment 3627 ≤ upperValue ((point split endpoint 4096 3627+point split endpoint 4096 3628)/2)
    have hp : upperPayment 3627 = (74554224782:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3627+point split endpoint 4096 3628)/2 = (667383177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667383177:ℝ)/168755200)*ClassicalSixthBranch.v ((667383177:ℝ)/168755200)/ClassicalSixthBranch.r = (81907154542305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3627
  · change upperPayment 3628 ≤ upperValue ((point split endpoint 4096 3628+point split endpoint 4096 3629)/2)
    have hp : upperPayment 3628 = (74404388132:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3628+point split endpoint 4096 3629)/2 = (667408327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667408327:ℝ)/168755200)*ClassicalSixthBranch.v ((667408327:ℝ)/168755200)/ClassicalSixthBranch.r = (81888480558657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3628
  · change upperPayment 3629 ≤ upperValue ((point split endpoint 4096 3629+point split endpoint 4096 3630)/2)
    have hp : upperPayment 3629 = (74254513348:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3629+point split endpoint 4096 3630)/2 = (667433477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667433477:ℝ)/168755200)*ClassicalSixthBranch.v ((667433477:ℝ)/168755200)/ClassicalSixthBranch.r = (81869808599081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3629
  · change upperPayment 3630 ≤ upperValue ((point split endpoint 4096 3630+point split endpoint 4096 3631)/2)
    have hp : upperPayment 3630 = (74104600418:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3630+point split endpoint 4096 3631)/2 = (667458627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667458627:ℝ)/168755200)*ClassicalSixthBranch.v ((667458627:ℝ)/168755200)/ClassicalSixthBranch.r = (81851138663577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3630
  · change upperPayment 3631 ≤ upperValue ((point split endpoint 4096 3631+point split endpoint 4096 3632)/2)
    have hp : upperPayment 3631 = (73954649334:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3631+point split endpoint 4096 3632)/2 = (667483777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667483777:ℝ)/168755200)*ClassicalSixthBranch.v ((667483777:ℝ)/168755200)/ClassicalSixthBranch.r = (81832470752145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3631
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_226
