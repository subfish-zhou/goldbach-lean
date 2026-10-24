import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints060
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_060 (j : Fin 16) : upperPayment (16*60+j.val) ≤
    upperValue ((point split endpoint 4096 (16*60+j.val)+point split endpoint 4096 (16*60+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 960 ≤ upperValue ((point split endpoint 4096 960+point split endpoint 4096 961)/2)
    have hp : upperPayment 960 = (363145151679:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 960+point split endpoint 4096 961)/2 = (600308127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600308127:ℝ)/168755200)*ClassicalSixthBranch.v ((600308127:ℝ)/168755200)/ClassicalSixthBranch.r = (138911867763537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_960
  · change upperPayment 961 ≤ upperValue ((point split endpoint 4096 961+point split endpoint 4096 962)/2)
    have hp : upperPayment 961 = (363071439633:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 961+point split endpoint 4096 962)/2 = (600333277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600333277:ℝ)/168755200)*ClassicalSixthBranch.v ((600333277:ℝ)/168755200)/ClassicalSixthBranch.r = (138887795579865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_961
  · change upperPayment 962 ≤ upperValue ((point split endpoint 4096 962+point split endpoint 4096 963)/2)
    have hp : upperPayment 962 = (362997705742:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 962+point split endpoint 4096 963)/2 = (600358427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600358427:ℝ)/168755200)*ClassicalSixthBranch.v ((600358427:ℝ)/168755200)/ClassicalSixthBranch.r = (138863725420265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_962
  · change upperPayment 963 ≤ upperValue ((point split endpoint 4096 963+point split endpoint 4096 964)/2)
    have hp : upperPayment 963 = (362923950004:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 963+point split endpoint 4096 964)/2 = (600383577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600383577:ℝ)/168755200)*ClassicalSixthBranch.v ((600383577:ℝ)/168755200)/ClassicalSixthBranch.r = (138839657284737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_963
  · change upperPayment 964 ≤ upperValue ((point split endpoint 4096 964+point split endpoint 4096 965)/2)
    have hp : upperPayment 964 = (362850172413:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 964+point split endpoint 4096 965)/2 = (600408727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600408727:ℝ)/168755200)*ClassicalSixthBranch.v ((600408727:ℝ)/168755200)/ClassicalSixthBranch.r = (138815591173281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_964
  · change upperPayment 965 ≤ upperValue ((point split endpoint 4096 965+point split endpoint 4096 966)/2)
    have hp : upperPayment 965 = (362776372968:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 965+point split endpoint 4096 966)/2 = (600433877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600433877:ℝ)/168755200)*ClassicalSixthBranch.v ((600433877:ℝ)/168755200)/ClassicalSixthBranch.r = (138791527085897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_965
  · change upperPayment 966 ≤ upperValue ((point split endpoint 4096 966+point split endpoint 4096 967)/2)
    have hp : upperPayment 966 = (362702551665:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 966+point split endpoint 4096 967)/2 = (600459027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600459027:ℝ)/168755200)*ClassicalSixthBranch.v ((600459027:ℝ)/168755200)/ClassicalSixthBranch.r = (138767465022585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_966
  · change upperPayment 967 ≤ upperValue ((point split endpoint 4096 967+point split endpoint 4096 968)/2)
    have hp : upperPayment 967 = (362628708500:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 967+point split endpoint 4096 968)/2 = (600484177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600484177:ℝ)/168755200)*ClassicalSixthBranch.v ((600484177:ℝ)/168755200)/ClassicalSixthBranch.r = (138743404983345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_967
  · change upperPayment 968 ≤ upperValue ((point split endpoint 4096 968+point split endpoint 4096 969)/2)
    have hp : upperPayment 968 = (362554843470:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 968+point split endpoint 4096 969)/2 = (600509327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600509327:ℝ)/168755200)*ClassicalSixthBranch.v ((600509327:ℝ)/168755200)/ClassicalSixthBranch.r = (138719346968177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_968
  · change upperPayment 969 ≤ upperValue ((point split endpoint 4096 969+point split endpoint 4096 970)/2)
    have hp : upperPayment 969 = (362480956572:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 969+point split endpoint 4096 970)/2 = (600534477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600534477:ℝ)/168755200)*ClassicalSixthBranch.v ((600534477:ℝ)/168755200)/ClassicalSixthBranch.r = (138695290977081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_969
  · change upperPayment 970 ≤ upperValue ((point split endpoint 4096 970+point split endpoint 4096 971)/2)
    have hp : upperPayment 970 = (362407047803:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 970+point split endpoint 4096 971)/2 = (600559627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600559627:ℝ)/168755200)*ClassicalSixthBranch.v ((600559627:ℝ)/168755200)/ClassicalSixthBranch.r = (138671237010057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_970
  · change upperPayment 971 ≤ upperValue ((point split endpoint 4096 971+point split endpoint 4096 972)/2)
    have hp : upperPayment 971 = (362333117158:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 971+point split endpoint 4096 972)/2 = (600584777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600584777:ℝ)/168755200)*ClassicalSixthBranch.v ((600584777:ℝ)/168755200)/ClassicalSixthBranch.r = (138647185067105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_971
  · change upperPayment 972 ≤ upperValue ((point split endpoint 4096 972+point split endpoint 4096 973)/2)
    have hp : upperPayment 972 = (362259164635:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 972+point split endpoint 4096 973)/2 = (600609927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600609927:ℝ)/168755200)*ClassicalSixthBranch.v ((600609927:ℝ)/168755200)/ClassicalSixthBranch.r = (138623135148225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_972
  · change upperPayment 973 ≤ upperValue ((point split endpoint 4096 973+point split endpoint 4096 974)/2)
    have hp : upperPayment 973 = (362185190230:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 973+point split endpoint 4096 974)/2 = (600635077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600635077:ℝ)/168755200)*ClassicalSixthBranch.v ((600635077:ℝ)/168755200)/ClassicalSixthBranch.r = (138599087253417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_973
  · change upperPayment 974 ≤ upperValue ((point split endpoint 4096 974+point split endpoint 4096 975)/2)
    have hp : upperPayment 974 = (362111193940:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 974+point split endpoint 4096 975)/2 = (600660227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600660227:ℝ)/168755200)*ClassicalSixthBranch.v ((600660227:ℝ)/168755200)/ClassicalSixthBranch.r = (138575041382681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_974
  · change upperPayment 975 ≤ upperValue ((point split endpoint 4096 975+point split endpoint 4096 976)/2)
    have hp : upperPayment 975 = (362037175761:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 975+point split endpoint 4096 976)/2 = (600685377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600685377:ℝ)/168755200)*ClassicalSixthBranch.v ((600685377:ℝ)/168755200)/ClassicalSixthBranch.r = (138550997536017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_975
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_060
