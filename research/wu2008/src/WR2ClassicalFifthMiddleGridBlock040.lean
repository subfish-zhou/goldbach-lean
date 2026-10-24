import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints040
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_040 (j : Fin 16) : middlePayment (16*40+j.val) ≤
    middleValue ((point 4 cut 1024 (16*40+j.val)+point 4 cut 1024 (16*40+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 640 ≤ middleValue ((point 4 cut 1024 640+point 4 cut 1024 641)/2)
    have hp : middlePayment 640 = (650736183736:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 640+point 4 cut 1024 641)/2 = (84701693:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84701693:ℝ)/21094400) = (33971200:ℝ)/21288451 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84701693:ℝ)/21094400)-4 = (324093:ℝ)/21094400 by norm_num]
    exact paid_middle_640
  · change middlePayment 641 ≤ middleValue ((point 4 cut 1024 641+point 4 cut 1024 642)/2)
    have hp : middlePayment 641 = (650776041801:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 641+point 4 cut 1024 642)/2 = (84702199:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84702199:ℝ)/21094400) = (6794240:ℝ)/4257589 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84702199:ℝ)/21094400)-4 = (324599:ℝ)/21094400 by norm_num]
    exact paid_middle_641
  · change middlePayment 642 ≤ middleValue ((point 4 cut 1024 642+point 4 cut 1024 643)/2)
    have hp : middlePayment 642 = (650815901418:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 642+point 4 cut 1024 643)/2 = (16940541:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16940541:ℝ)/4218880) = (33971200:ℝ)/21287439 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16940541:ℝ)/4218880)-4 = (65021:ℝ)/4218880 by norm_num]
    exact paid_middle_642
  · change middlePayment 643 ≤ middleValue ((point 4 cut 1024 643+point 4 cut 1024 644)/2)
    have hp : middlePayment 643 = (650855762587:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 643+point 4 cut 1024 644)/2 = (84703211:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84703211:ℝ)/21094400) = (33971200:ℝ)/21286933 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84703211:ℝ)/21094400)-4 = (325611:ℝ)/21094400 by norm_num]
    exact paid_middle_643
  · change middlePayment 644 ≤ middleValue ((point 4 cut 1024 644+point 4 cut 1024 645)/2)
    have hp : middlePayment 644 = (650895625309:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 644+point 4 cut 1024 645)/2 = (84703717:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84703717:ℝ)/21094400) = (33971200:ℝ)/21286427 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84703717:ℝ)/21094400)-4 = (326117:ℝ)/21094400 by norm_num]
    exact paid_middle_644
  · change middlePayment 645 ≤ middleValue ((point 4 cut 1024 645+point 4 cut 1024 646)/2)
    have hp : middlePayment 645 = (650935489583:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 645+point 4 cut 1024 646)/2 = (84704223:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84704223:ℝ)/21094400) = (33971200:ℝ)/21285921 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84704223:ℝ)/21094400)-4 = (326623:ℝ)/21094400 by norm_num]
    exact paid_middle_645
  · change middlePayment 646 ≤ middleValue ((point 4 cut 1024 646+point 4 cut 1024 647)/2)
    have hp : middlePayment 646 = (650975355410:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 646+point 4 cut 1024 647)/2 = (84704729:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84704729:ℝ)/21094400) = (6794240:ℝ)/4257083 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84704729:ℝ)/21094400)-4 = (327129:ℝ)/21094400 by norm_num]
    exact paid_middle_646
  · change middlePayment 647 ≤ middleValue ((point 4 cut 1024 647+point 4 cut 1024 648)/2)
    have hp : middlePayment 647 = (651015222789:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 647+point 4 cut 1024 648)/2 = (16941047:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16941047:ℝ)/4218880) = (33971200:ℝ)/21284909 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16941047:ℝ)/4218880)-4 = (65527:ℝ)/4218880 by norm_num]
    exact paid_middle_647
  · change middlePayment 648 ≤ middleValue ((point 4 cut 1024 648+point 4 cut 1024 649)/2)
    have hp : middlePayment 648 = (651055091722:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 648+point 4 cut 1024 649)/2 = (84705741:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84705741:ℝ)/21094400) = (33971200:ℝ)/21284403 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84705741:ℝ)/21094400)-4 = (328141:ℝ)/21094400 by norm_num]
    exact paid_middle_648
  · change middlePayment 649 ≤ middleValue ((point 4 cut 1024 649+point 4 cut 1024 650)/2)
    have hp : middlePayment 649 = (651094962207:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 649+point 4 cut 1024 650)/2 = (84706247:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84706247:ℝ)/21094400) = (33971200:ℝ)/21283897 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84706247:ℝ)/21094400)-4 = (328647:ℝ)/21094400 by norm_num]
    exact paid_middle_649
  · change middlePayment 650 ≤ middleValue ((point 4 cut 1024 650+point 4 cut 1024 651)/2)
    have hp : middlePayment 650 = (651134834245:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 650+point 4 cut 1024 651)/2 = (84706753:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84706753:ℝ)/21094400) = (33971200:ℝ)/21283391 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84706753:ℝ)/21094400)-4 = (329153:ℝ)/21094400 by norm_num]
    exact paid_middle_650
  · change middlePayment 651 ≤ middleValue ((point 4 cut 1024 651+point 4 cut 1024 652)/2)
    have hp : middlePayment 651 = (651174707836:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 651+point 4 cut 1024 652)/2 = (84707259:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84707259:ℝ)/21094400) = (6794240:ℝ)/4256577 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84707259:ℝ)/21094400)-4 = (329659:ℝ)/21094400 by norm_num]
    exact paid_middle_651
  · change middlePayment 652 ≤ middleValue ((point 4 cut 1024 652+point 4 cut 1024 653)/2)
    have hp : middlePayment 652 = (651214582980:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 652+point 4 cut 1024 653)/2 = (16941553:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16941553:ℝ)/4218880) = (33971200:ℝ)/21282379 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16941553:ℝ)/4218880)-4 = (66033:ℝ)/4218880 by norm_num]
    exact paid_middle_652
  · change middlePayment 653 ≤ middleValue ((point 4 cut 1024 653+point 4 cut 1024 654)/2)
    have hp : middlePayment 653 = (651254459677:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 653+point 4 cut 1024 654)/2 = (84708271:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84708271:ℝ)/21094400) = (33971200:ℝ)/21281873 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84708271:ℝ)/21094400)-4 = (330671:ℝ)/21094400 by norm_num]
    exact paid_middle_653
  · change middlePayment 654 ≤ middleValue ((point 4 cut 1024 654+point 4 cut 1024 655)/2)
    have hp : middlePayment 654 = (651294337927:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 654+point 4 cut 1024 655)/2 = (84708777:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84708777:ℝ)/21094400) = (33971200:ℝ)/21281367 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84708777:ℝ)/21094400)-4 = (331177:ℝ)/21094400 by norm_num]
    exact paid_middle_654
  · change middlePayment 655 ≤ middleValue ((point 4 cut 1024 655+point 4 cut 1024 656)/2)
    have hp : middlePayment 655 = (651334217731:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 655+point 4 cut 1024 656)/2 = (84709283:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84709283:ℝ)/21094400) = (33971200:ℝ)/21280861 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84709283:ℝ)/21094400)-4 = (331683:ℝ)/21094400 by norm_num]
    exact paid_middle_655
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_040
