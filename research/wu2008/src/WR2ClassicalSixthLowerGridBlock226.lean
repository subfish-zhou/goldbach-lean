import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints226
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_226 (j : Fin 16) : lowerPayment (16*226+j.val) ≤
    lowerValue ((point 2 split 4096 (16*226+j.val)+point 2 split 4096 (16*226+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3616 ≤ lowerValue ((point 2 split 4096 3616+point 2 split 4096 3617)/2)
    have hp : lowerPayment 3616 = (377258330380:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3616+point 2 split 4096 3617)/2 = (548214923:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((548214923:ℝ)/168755200)/ClassicalSixthBranch.v ((548214923:ℝ)/168755200) = (534410274683:ℝ)/246957932696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3616
  · change lowerPayment 3617 ≤ lowerValue ((point 2 split 4096 3617+point 2 split 4096 3618)/2)
    have hp : lowerPayment 3617 = (377352491708:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3617+point 2 split 4096 3618)/2 = (109654637:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((109654637:ℝ)/33751040)/ClassicalSixthBranch.v ((109654637:ℝ)/33751040) = (534332961009:ℝ)/246909924808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3617
  · change lowerPayment 3618 ≤ lowerValue ((point 2 split 4096 3618+point 2 split 4096 3619)/2)
    have hp : lowerPayment 3618 = (377446666887:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3618+point 2 split 4096 3619)/2 = (548331447:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((548331447:ℝ)/168755200)/ClassicalSixthBranch.v ((548331447:ℝ)/168755200) = (106851129467:ℝ)/49372383384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3618
  · change lowerPayment 3619 ≤ lowerValue ((point 2 split 4096 3619+point 2 split 4096 3620)/2)
    have hp : lowerPayment 3619 = (377540855933:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3619+point 2 split 4096 3620)/2 = (548389709:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((548389709:ℝ)/168755200)/ClassicalSixthBranch.v ((548389709:ℝ)/168755200) = (534178333661:ℝ)/246813909032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3619
  · change lowerPayment 3620 ≤ lowerValue ((point 2 split 4096 3620+point 2 split 4096 3621)/2)
    have hp : lowerPayment 3620 = (377635058861:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3620+point 2 split 4096 3621)/2 = (548447971:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((548447971:ℝ)/168755200)/ClassicalSixthBranch.v ((548447971:ℝ)/168755200) = (534101019987:ℝ)/246765901144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3620
  · change lowerPayment 3621 ≤ lowerValue ((point 2 split 4096 3621+point 2 split 4096 3622)/2)
    have hp : lowerPayment 3621 = (377729275687:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3621+point 2 split 4096 3622)/2 = (548506233:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((548506233:ℝ)/168755200)/ClassicalSixthBranch.v ((548506233:ℝ)/168755200) = (534023706313:ℝ)/246717893256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3621
  · change lowerPayment 3622 ≤ lowerValue ((point 2 split 4096 3622+point 2 split 4096 3623)/2)
    have hp : lowerPayment 3622 = (377823506429:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3622+point 2 split 4096 3623)/2 = (109712899:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((109712899:ℝ)/33751040)/ClassicalSixthBranch.v ((109712899:ℝ)/33751040) = (533946392639:ℝ)/246669885368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3622
  · change lowerPayment 3623 ≤ lowerValue ((point 2 split 4096 3623+point 2 split 4096 3624)/2)
    have hp : lowerPayment 3623 = (377917751101:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3623+point 2 split 4096 3624)/2 = (548622757:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((548622757:ℝ)/168755200)/ClassicalSixthBranch.v ((548622757:ℝ)/168755200) = (106773815793:ℝ)/49324375496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3623
  · change lowerPayment 3624 ≤ lowerValue ((point 2 split 4096 3624+point 2 split 4096 3625)/2)
    have hp : lowerPayment 3624 = (378012009721:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3624+point 2 split 4096 3625)/2 = (548681019:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((548681019:ℝ)/168755200)/ClassicalSixthBranch.v ((548681019:ℝ)/168755200) = (533791765291:ℝ)/246573869592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3624
  · change lowerPayment 3625 ≤ lowerValue ((point 2 split 4096 3625+point 2 split 4096 3626)/2)
    have hp : lowerPayment 3625 = (378106282303:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3625+point 2 split 4096 3626)/2 = (548739281:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((548739281:ℝ)/168755200)/ClassicalSixthBranch.v ((548739281:ℝ)/168755200) = (533714451617:ℝ)/246525861704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3625
  · change lowerPayment 3626 ≤ lowerValue ((point 2 split 4096 3626+point 2 split 4096 3627)/2)
    have hp : lowerPayment 3626 = (378200568866:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3626+point 2 split 4096 3627)/2 = (548797543:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((548797543:ℝ)/168755200)/ClassicalSixthBranch.v ((548797543:ℝ)/168755200) = (533637137943:ℝ)/246477853816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3626
  · change lowerPayment 3627 ≤ lowerValue ((point 2 split 4096 3627+point 2 split 4096 3628)/2)
    have hp : lowerPayment 3627 = (378294869423:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3627+point 2 split 4096 3628)/2 = (109771161:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((109771161:ℝ)/33751040)/ClassicalSixthBranch.v ((109771161:ℝ)/33751040) = (533559824269:ℝ)/246429845928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3627
  · change lowerPayment 3628 ≤ lowerValue ((point 2 split 4096 3628+point 2 split 4096 3629)/2)
    have hp : lowerPayment 3628 = (378389183992:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3628+point 2 split 4096 3629)/2 = (548914067:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((548914067:ℝ)/168755200)/ClassicalSixthBranch.v ((548914067:ℝ)/168755200) = (106696502119:ℝ)/49276367608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3628
  · change lowerPayment 3629 ≤ lowerValue ((point 2 split 4096 3629+point 2 split 4096 3630)/2)
    have hp : lowerPayment 3629 = (378483512589:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3629+point 2 split 4096 3630)/2 = (548972329:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((548972329:ℝ)/168755200)/ClassicalSixthBranch.v ((548972329:ℝ)/168755200) = (533405196921:ℝ)/246333830152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3629
  · change lowerPayment 3630 ≤ lowerValue ((point 2 split 4096 3630+point 2 split 4096 3631)/2)
    have hp : lowerPayment 3630 = (378577855230:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3630+point 2 split 4096 3631)/2 = (549030591:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((549030591:ℝ)/168755200)/ClassicalSixthBranch.v ((549030591:ℝ)/168755200) = (533327883247:ℝ)/246285822264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3630
  · change lowerPayment 3631 ≤ lowerValue ((point 2 split 4096 3631+point 2 split 4096 3632)/2)
    have hp : lowerPayment 3631 = (378672211931:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3631+point 2 split 4096 3632)/2 = (549088853:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((549088853:ℝ)/168755200)/ClassicalSixthBranch.v ((549088853:ℝ)/168755200) = (533250569573:ℝ)/246237814376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3631
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_226
