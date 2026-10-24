import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints191
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_191 (j : Fin 16) : lowerPayment (16*191+j.val) ≤
    lowerValue ((point 2 split 4096 (16*191+j.val)+point 2 split 4096 (16*191+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3056 ≤ lowerValue ((point 2 split 4096 3056+point 2 split 4096 3057)/2)
    have hp : lowerPayment 3056 = (326248769741:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3056+point 2 split 4096 3057)/2 = (515588203:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((515588203:ℝ)/168755200)/ClassicalSixthBranch.v ((515588203:ℝ)/168755200) = (577705932123:ℝ)/273842349976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3056
  · change lowerPayment 3057 ≤ lowerValue ((point 2 split 4096 3057+point 2 split 4096 3058)/2)
    have hp : lowerPayment 3057 = (326337575513:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3057+point 2 split 4096 3058)/2 = (103129293:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((103129293:ℝ)/33751040)/ClassicalSixthBranch.v ((103129293:ℝ)/33751040) = (577628618449:ℝ)/273794342088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3057
  · change lowerPayment 3058 ≤ lowerValue ((point 2 split 4096 3058+point 2 split 4096 3059)/2)
    have hp : lowerPayment 3058 = (326426386749:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3058+point 2 split 4096 3059)/2 = (515704727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((515704727:ℝ)/168755200)/ClassicalSixthBranch.v ((515704727:ℝ)/168755200) = (23102052191:ℝ)/10949853368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3058
  · change lowerPayment 3059 ≤ lowerValue ((point 2 split 4096 3059+point 2 split 4096 3060)/2)
    have hp : lowerPayment 3059 = (326515203464:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3059+point 2 split 4096 3060)/2 = (515762989:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((515762989:ℝ)/168755200)/ClassicalSixthBranch.v ((515762989:ℝ)/168755200) = (577473991101:ℝ)/273698326312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3059
  · change lowerPayment 3060 ≤ lowerValue ((point 2 split 4096 3060+point 2 split 4096 3061)/2)
    have hp : lowerPayment 3060 = (326604025672:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3060+point 2 split 4096 3061)/2 = (515821251:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((515821251:ℝ)/168755200)/ClassicalSixthBranch.v ((515821251:ℝ)/168755200) = (577396677427:ℝ)/273650318424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3060
  · change lowerPayment 3061 ≤ lowerValue ((point 2 split 4096 3061+point 2 split 4096 3062)/2)
    have hp : lowerPayment 3061 = (326692853388:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3061+point 2 split 4096 3062)/2 = (515879513:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((515879513:ℝ)/168755200)/ClassicalSixthBranch.v ((515879513:ℝ)/168755200) = (577319363753:ℝ)/273602310536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3061
  · change lowerPayment 3062 ≤ lowerValue ((point 2 split 4096 3062+point 2 split 4096 3063)/2)
    have hp : lowerPayment 3062 = (326781686626:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3062+point 2 split 4096 3063)/2 = (20637511:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((20637511:ℝ)/6750208)/ClassicalSixthBranch.v ((20637511:ℝ)/6750208) = (577242050079:ℝ)/273554302648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3062
  · change lowerPayment 3063 ≤ lowerValue ((point 2 split 4096 3063+point 2 split 4096 3064)/2)
    have hp : lowerPayment 3063 = (326870525400:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3063+point 2 split 4096 3064)/2 = (515996037:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((515996037:ℝ)/168755200)/ClassicalSixthBranch.v ((515996037:ℝ)/168755200) = (115432947281:ℝ)/54701258952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3063
  · change lowerPayment 3064 ≤ lowerValue ((point 2 split 4096 3064+point 2 split 4096 3065)/2)
    have hp : lowerPayment 3064 = (326959369724:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3064+point 2 split 4096 3065)/2 = (516054299:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((516054299:ℝ)/168755200)/ClassicalSixthBranch.v ((516054299:ℝ)/168755200) = (577087422731:ℝ)/273458286872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3064
  · change lowerPayment 3065 ≤ lowerValue ((point 2 split 4096 3065+point 2 split 4096 3066)/2)
    have hp : lowerPayment 3065 = (327048219613:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3065+point 2 split 4096 3066)/2 = (516112561:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((516112561:ℝ)/168755200)/ClassicalSixthBranch.v ((516112561:ℝ)/168755200) = (577010109057:ℝ)/273410278984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3065
  · change lowerPayment 3066 ≤ lowerValue ((point 2 split 4096 3066+point 2 split 4096 3067)/2)
    have hp : lowerPayment 3066 = (327137075080:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3066+point 2 split 4096 3067)/2 = (516170823:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((516170823:ℝ)/168755200)/ClassicalSixthBranch.v ((516170823:ℝ)/168755200) = (576932795383:ℝ)/273362271096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3066
  · change lowerPayment 3067 ≤ lowerValue ((point 2 split 4096 3067+point 2 split 4096 3068)/2)
    have hp : lowerPayment 3067 = (327225936141:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3067+point 2 split 4096 3068)/2 = (103245817:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((103245817:ℝ)/33751040)/ClassicalSixthBranch.v ((103245817:ℝ)/33751040) = (576855481709:ℝ)/273314263208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3067
  · change lowerPayment 3068 ≤ lowerValue ((point 2 split 4096 3068+point 2 split 4096 3069)/2)
    have hp : lowerPayment 3068 = (327314802808:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3068+point 2 split 4096 3069)/2 = (516287347:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((516287347:ℝ)/168755200)/ClassicalSixthBranch.v ((516287347:ℝ)/168755200) = (115355633607:ℝ)/54653251064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3068
  · change lowerPayment 3069 ≤ lowerValue ((point 2 split 4096 3069+point 2 split 4096 3070)/2)
    have hp : lowerPayment 3069 = (327403675098:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3069+point 2 split 4096 3070)/2 = (516345609:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((516345609:ℝ)/168755200)/ClassicalSixthBranch.v ((516345609:ℝ)/168755200) = (576700854361:ℝ)/273218247432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3069
  · change lowerPayment 3070 ≤ lowerValue ((point 2 split 4096 3070+point 2 split 4096 3071)/2)
    have hp : lowerPayment 3070 = (327492553023:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3070+point 2 split 4096 3071)/2 = (516403871:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((516403871:ℝ)/168755200)/ClassicalSixthBranch.v ((516403871:ℝ)/168755200) = (576623540687:ℝ)/273170239544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3070
  · change lowerPayment 3071 ≤ lowerValue ((point 2 split 4096 3071+point 2 split 4096 3072)/2)
    have hp : lowerPayment 3071 = (327581436598:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3071+point 2 split 4096 3072)/2 = (516462133:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((516462133:ℝ)/168755200)/ClassicalSixthBranch.v ((516462133:ℝ)/168755200) = (576546227013:ℝ)/273122231656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3071
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_191
