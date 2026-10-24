import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints235
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_235 (j : Fin 16) : upperPayment (16*235+j.val) ≤
    upperValue ((point split endpoint 4096 (16*235+j.val)+point split endpoint 4096 (16*235+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3760 ≤ upperValue ((point split endpoint 4096 3760+point split endpoint 4096 3761)/2)
    have hp : upperPayment 3760 = (54287305098:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3760+point split endpoint 4096 3761)/2 = (670728127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670728127:ℝ)/168755200)*ClassicalSixthBranch.v ((670728127:ℝ)/168755200)/ClassicalSixthBranch.r = (79441282021137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3760
  · change upperPayment 3761 ≤ upperValue ((point split endpoint 4096 3761+point split endpoint 4096 3762)/2)
    have hp : upperPayment 3761 = (54132306835:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3761+point split endpoint 4096 3762)/2 = (670753277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670753277:ℝ)/168755200)*ClassicalSixthBranch.v ((670753277:ℝ)/168755200)/ClassicalSixthBranch.r = (79422877239065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3761
  · change upperPayment 3762 ≤ upperValue ((point split endpoint 4096 3762+point split endpoint 4096 3763)/2)
    have hp : upperPayment 3762 = (53977269065:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3762+point split endpoint 4096 3763)/2 = (670778427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670778427:ℝ)/168755200)*ClassicalSixthBranch.v ((670778427:ℝ)/168755200)/ClassicalSixthBranch.r = (79404474481065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3762
  · change upperPayment 3763 ≤ upperValue ((point split endpoint 4096 3763+point split endpoint 4096 3764)/2)
    have hp : upperPayment 3763 = (53822191778:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3763+point split endpoint 4096 3764)/2 = (670803577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670803577:ℝ)/168755200)*ClassicalSixthBranch.v ((670803577:ℝ)/168755200)/ClassicalSixthBranch.r = (79386073747137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3763
  · change upperPayment 3764 ≤ upperValue ((point split endpoint 4096 3764+point split endpoint 4096 3765)/2)
    have hp : upperPayment 3764 = (53667074964:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3764+point split endpoint 4096 3765)/2 = (670828727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670828727:ℝ)/168755200)*ClassicalSixthBranch.v ((670828727:ℝ)/168755200)/ClassicalSixthBranch.r = (79367675037281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3764
  · change upperPayment 3765 ≤ upperValue ((point split endpoint 4096 3765+point split endpoint 4096 3766)/2)
    have hp : upperPayment 3765 = (53511918611:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3765+point split endpoint 4096 3766)/2 = (670853877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670853877:ℝ)/168755200)*ClassicalSixthBranch.v ((670853877:ℝ)/168755200)/ClassicalSixthBranch.r = (79349278351497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3765
  · change upperPayment 3766 ≤ upperValue ((point split endpoint 4096 3766+point split endpoint 4096 3767)/2)
    have hp : upperPayment 3766 = (53356722709:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3766+point split endpoint 4096 3767)/2 = (670879027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670879027:ℝ)/168755200)*ClassicalSixthBranch.v ((670879027:ℝ)/168755200)/ClassicalSixthBranch.r = (79330883689785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3766
  · change upperPayment 3767 ≤ upperValue ((point split endpoint 4096 3767+point split endpoint 4096 3768)/2)
    have hp : upperPayment 3767 = (53201487247:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3767+point split endpoint 4096 3768)/2 = (670904177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670904177:ℝ)/168755200)*ClassicalSixthBranch.v ((670904177:ℝ)/168755200)/ClassicalSixthBranch.r = (79312491052145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3767
  · change upperPayment 3768 ≤ upperValue ((point split endpoint 4096 3768+point split endpoint 4096 3769)/2)
    have hp : upperPayment 3768 = (53046212215:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3768+point split endpoint 4096 3769)/2 = (670929327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670929327:ℝ)/168755200)*ClassicalSixthBranch.v ((670929327:ℝ)/168755200)/ClassicalSixthBranch.r = (79294100438577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3768
  · change upperPayment 3769 ≤ upperValue ((point split endpoint 4096 3769+point split endpoint 4096 3770)/2)
    have hp : upperPayment 3769 = (52890897603:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3769+point split endpoint 4096 3770)/2 = (670954477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670954477:ℝ)/168755200)*ClassicalSixthBranch.v ((670954477:ℝ)/168755200)/ClassicalSixthBranch.r = (79275711849081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3769
  · change upperPayment 3770 ≤ upperValue ((point split endpoint 4096 3770+point split endpoint 4096 3771)/2)
    have hp : upperPayment 3770 = (52735543398:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3770+point split endpoint 4096 3771)/2 = (670979627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670979627:ℝ)/168755200)*ClassicalSixthBranch.v ((670979627:ℝ)/168755200)/ClassicalSixthBranch.r = (79257325283657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3770
  · change upperPayment 3771 ≤ upperValue ((point split endpoint 4096 3771+point split endpoint 4096 3772)/2)
    have hp : upperPayment 3771 = (52580149592:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3771+point split endpoint 4096 3772)/2 = (671004777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671004777:ℝ)/168755200)*ClassicalSixthBranch.v ((671004777:ℝ)/168755200)/ClassicalSixthBranch.r = (79238940742305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3771
  · change upperPayment 3772 ≤ upperValue ((point split endpoint 4096 3772+point split endpoint 4096 3773)/2)
    have hp : upperPayment 3772 = (52424716173:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3772+point split endpoint 4096 3773)/2 = (671029927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671029927:ℝ)/168755200)*ClassicalSixthBranch.v ((671029927:ℝ)/168755200)/ClassicalSixthBranch.r = (79220558225025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3772
  · change upperPayment 3773 ≤ upperValue ((point split endpoint 4096 3773+point split endpoint 4096 3774)/2)
    have hp : upperPayment 3773 = (52269243131:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3773+point split endpoint 4096 3774)/2 = (671055077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671055077:ℝ)/168755200)*ClassicalSixthBranch.v ((671055077:ℝ)/168755200)/ClassicalSixthBranch.r = (79202177731817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3773
  · change upperPayment 3774 ≤ upperValue ((point split endpoint 4096 3774+point split endpoint 4096 3775)/2)
    have hp : upperPayment 3774 = (52113730454:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3774+point split endpoint 4096 3775)/2 = (671080227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671080227:ℝ)/168755200)*ClassicalSixthBranch.v ((671080227:ℝ)/168755200)/ClassicalSixthBranch.r = (79183799262681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3774
  · change upperPayment 3775 ≤ upperValue ((point split endpoint 4096 3775+point split endpoint 4096 3776)/2)
    have hp : upperPayment 3775 = (51958178133:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3775+point split endpoint 4096 3776)/2 = (671105377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671105377:ℝ)/168755200)*ClassicalSixthBranch.v ((671105377:ℝ)/168755200)/ClassicalSixthBranch.r = (79165422817617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3775
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_235
