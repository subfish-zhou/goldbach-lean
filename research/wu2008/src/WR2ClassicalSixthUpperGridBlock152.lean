import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints152
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_152 (j : Fin 16) : upperPayment (16*152+j.val) ≤
    upperValue ((point split endpoint 4096 (16*152+j.val)+point split endpoint 4096 (16*152+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2432 ≤ upperValue ((point split endpoint 4096 2432+point split endpoint 4096 2433)/2)
    have hp : upperPayment 2432 = (228894650159:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2432+point split endpoint 4096 2433)/2 = (637328927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637328927:ℝ)/168755200)*ClassicalSixthBranch.v ((637328927:ℝ)/168755200)/ClassicalSixthBranch.r = (105668987093585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2432
  · change upperPayment 2433 ≤ upperValue ((point split endpoint 4096 2433+point split endpoint 4096 2434)/2)
    have hp : upperPayment 2433 = (228784266612:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2433+point split endpoint 4096 2434)/2 = (637354077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637354077:ℝ)/168755200)*ClassicalSixthBranch.v ((637354077:ℝ)/168755200)/ClassicalSixthBranch.r = (105647894343897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2433
  · change upperPayment 2434 ≤ upperValue ((point split endpoint 4096 2434+point split endpoint 4096 2435)/2)
    have hp : upperPayment 2434 = (228673854397:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2434+point split endpoint 4096 2435)/2 = (637379227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637379227:ℝ)/168755200)*ClassicalSixthBranch.v ((637379227:ℝ)/168755200)/ClassicalSixthBranch.r = (105626803618281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2434
  · change upperPayment 2435 ≤ upperValue ((point split endpoint 4096 2435+point split endpoint 4096 2436)/2)
    have hp : upperPayment 2435 = (228563413507:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2435+point split endpoint 4096 2436)/2 = (637404377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637404377:ℝ)/168755200)*ClassicalSixthBranch.v ((637404377:ℝ)/168755200)/ClassicalSixthBranch.r = (105605714916737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2435
  · change upperPayment 2436 ≤ upperValue ((point split endpoint 4096 2436+point split endpoint 4096 2437)/2)
    have hp : upperPayment 2436 = (228452943936:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2436+point split endpoint 4096 2437)/2 = (637429527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637429527:ℝ)/168755200)*ClassicalSixthBranch.v ((637429527:ℝ)/168755200)/ClassicalSixthBranch.r = (105584628239265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2436
  · change upperPayment 2437 ≤ upperValue ((point split endpoint 4096 2437+point split endpoint 4096 2438)/2)
    have hp : upperPayment 2437 = (228342445677:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2437+point split endpoint 4096 2438)/2 = (637454677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637454677:ℝ)/168755200)*ClassicalSixthBranch.v ((637454677:ℝ)/168755200)/ClassicalSixthBranch.r = (105563543585865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2437
  · change upperPayment 2438 ≤ upperValue ((point split endpoint 4096 2438+point split endpoint 4096 2439)/2)
    have hp : upperPayment 2438 = (228231918726:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2438+point split endpoint 4096 2439)/2 = (637479827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637479827:ℝ)/168755200)*ClassicalSixthBranch.v ((637479827:ℝ)/168755200)/ClassicalSixthBranch.r = (105542460956537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2438
  · change upperPayment 2439 ≤ upperValue ((point split endpoint 4096 2439+point split endpoint 4096 2440)/2)
    have hp : upperPayment 2439 = (228121363075:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2439+point split endpoint 4096 2440)/2 = (637504977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637504977:ℝ)/168755200)*ClassicalSixthBranch.v ((637504977:ℝ)/168755200)/ClassicalSixthBranch.r = (105521380351281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2439
  · change upperPayment 2440 ≤ upperValue ((point split endpoint 4096 2440+point split endpoint 4096 2441)/2)
    have hp : upperPayment 2440 = (228010778718:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2440+point split endpoint 4096 2441)/2 = (637530127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637530127:ℝ)/168755200)*ClassicalSixthBranch.v ((637530127:ℝ)/168755200)/ClassicalSixthBranch.r = (105500301770097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2440
  · change upperPayment 2441 ≤ upperValue ((point split endpoint 4096 2441+point split endpoint 4096 2442)/2)
    have hp : upperPayment 2441 = (227900165649:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2441+point split endpoint 4096 2442)/2 = (637555277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637555277:ℝ)/168755200)*ClassicalSixthBranch.v ((637555277:ℝ)/168755200)/ClassicalSixthBranch.r = (105479225212985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2441
  · change upperPayment 2442 ≤ upperValue ((point split endpoint 4096 2442+point split endpoint 4096 2443)/2)
    have hp : upperPayment 2442 = (227789523863:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2442+point split endpoint 4096 2443)/2 = (637580427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637580427:ℝ)/168755200)*ClassicalSixthBranch.v ((637580427:ℝ)/168755200)/ClassicalSixthBranch.r = (105458150679945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2442
  · change upperPayment 2443 ≤ upperValue ((point split endpoint 4096 2443+point split endpoint 4096 2444)/2)
    have hp : upperPayment 2443 = (227678853352:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2443+point split endpoint 4096 2444)/2 = (637605577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637605577:ℝ)/168755200)*ClassicalSixthBranch.v ((637605577:ℝ)/168755200)/ClassicalSixthBranch.r = (105437078170977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2443
  · change upperPayment 2444 ≤ upperValue ((point split endpoint 4096 2444+point split endpoint 4096 2445)/2)
    have hp : upperPayment 2444 = (227568154111:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2444+point split endpoint 4096 2445)/2 = (637630727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637630727:ℝ)/168755200)*ClassicalSixthBranch.v ((637630727:ℝ)/168755200)/ClassicalSixthBranch.r = (105416007686081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2444
  · change upperPayment 2445 ≤ upperValue ((point split endpoint 4096 2445+point split endpoint 4096 2446)/2)
    have hp : upperPayment 2445 = (227457426133:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2445+point split endpoint 4096 2446)/2 = (637655877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637655877:ℝ)/168755200)*ClassicalSixthBranch.v ((637655877:ℝ)/168755200)/ClassicalSixthBranch.r = (105394939225257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2445
  · change upperPayment 2446 ≤ upperValue ((point split endpoint 4096 2446+point split endpoint 4096 2447)/2)
    have hp : upperPayment 2446 = (227346669413:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2446+point split endpoint 4096 2447)/2 = (637681027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637681027:ℝ)/168755200)*ClassicalSixthBranch.v ((637681027:ℝ)/168755200)/ClassicalSixthBranch.r = (105373872788505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2446
  · change upperPayment 2447 ≤ upperValue ((point split endpoint 4096 2447+point split endpoint 4096 2448)/2)
    have hp : upperPayment 2447 = (227235883943:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2447+point split endpoint 4096 2448)/2 = (637706177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637706177:ℝ)/168755200)*ClassicalSixthBranch.v ((637706177:ℝ)/168755200)/ClassicalSixthBranch.r = (105352808375825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2447
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_152
