import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints247
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_247 (j : Fin 16) : upperPayment (16*247+j.val) ≤
    upperValue ((point split endpoint 4096 (16*247+j.val)+point split endpoint 4096 (16*247+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3952 ≤ upperValue ((point split endpoint 4096 3952+point split endpoint 4096 3953)/2)
    have hp : upperPayment 3952 = (23790676840:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3952+point split endpoint 4096 3953)/2 = (675556927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675556927:ℝ)/168755200)*ClassicalSixthBranch.v ((675556927:ℝ)/168755200)/ClassicalSixthBranch.r = (75944677247505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3952
  · change upperPayment 3953 ≤ upperValue ((point split endpoint 4096 3953+point split endpoint 4096 3954)/2)
    have hp : upperPayment 3953 = (23627893469:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3953+point split endpoint 4096 3954)/2 = (675582077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675582077:ℝ)/168755200)*ClassicalSixthBranch.v ((675582077:ℝ)/168755200)/ClassicalSixthBranch.r = (75926661087257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3953
  · change upperPayment 3954 ≤ upperValue ((point split endpoint 4096 3954+point split endpoint 4096 3955)/2)
    have hp : upperPayment 3954 = (23465068469:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3954+point split endpoint 4096 3955)/2 = (675607227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675607227:ℝ)/168755200)*ClassicalSixthBranch.v ((675607227:ℝ)/168755200)/ClassicalSixthBranch.r = (75908646951081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3954
  · change upperPayment 3955 ≤ upperValue ((point split endpoint 4096 3955+point split endpoint 4096 3956)/2)
    have hp : upperPayment 3955 = (23302201829:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3955+point split endpoint 4096 3956)/2 = (675632377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675632377:ℝ)/168755200)*ClassicalSixthBranch.v ((675632377:ℝ)/168755200)/ClassicalSixthBranch.r = (75890634838977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3955
  · change upperPayment 3956 ≤ upperValue ((point split endpoint 4096 3956+point split endpoint 4096 3957)/2)
    have hp : upperPayment 3956 = (23139293538:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3956+point split endpoint 4096 3957)/2 = (675657527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675657527:ℝ)/168755200)*ClassicalSixthBranch.v ((675657527:ℝ)/168755200)/ClassicalSixthBranch.r = (75872624750945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3956
  · change upperPayment 3957 ≤ upperValue ((point split endpoint 4096 3957+point split endpoint 4096 3958)/2)
    have hp : upperPayment 3957 = (22976343584:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3957+point split endpoint 4096 3958)/2 = (675682677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675682677:ℝ)/168755200)*ClassicalSixthBranch.v ((675682677:ℝ)/168755200)/ClassicalSixthBranch.r = (75854616686985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3957
  · change upperPayment 3958 ≤ upperValue ((point split endpoint 4096 3958+point split endpoint 4096 3959)/2)
    have hp : upperPayment 3958 = (22813351955:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3958+point split endpoint 4096 3959)/2 = (675707827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675707827:ℝ)/168755200)*ClassicalSixthBranch.v ((675707827:ℝ)/168755200)/ClassicalSixthBranch.r = (75836610647097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3958
  · change upperPayment 3959 ≤ upperValue ((point split endpoint 4096 3959+point split endpoint 4096 3960)/2)
    have hp : upperPayment 3959 = (22650318641:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3959+point split endpoint 4096 3960)/2 = (675732977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675732977:ℝ)/168755200)*ClassicalSixthBranch.v ((675732977:ℝ)/168755200)/ClassicalSixthBranch.r = (75818606631281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3959
  · change upperPayment 3960 ≤ upperValue ((point split endpoint 4096 3960+point split endpoint 4096 3961)/2)
    have hp : upperPayment 3960 = (22487243629:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3960+point split endpoint 4096 3961)/2 = (675758127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675758127:ℝ)/168755200)*ClassicalSixthBranch.v ((675758127:ℝ)/168755200)/ClassicalSixthBranch.r = (75800604639537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3960
  · change upperPayment 3961 ≤ upperValue ((point split endpoint 4096 3961+point split endpoint 4096 3962)/2)
    have hp : upperPayment 3961 = (22324126907:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3961+point split endpoint 4096 3962)/2 = (675783277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675783277:ℝ)/168755200)*ClassicalSixthBranch.v ((675783277:ℝ)/168755200)/ClassicalSixthBranch.r = (75782604671865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3961
  · change upperPayment 3962 ≤ upperValue ((point split endpoint 4096 3962+point split endpoint 4096 3963)/2)
    have hp : upperPayment 3962 = (22160968465:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3962+point split endpoint 4096 3963)/2 = (675808427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675808427:ℝ)/168755200)*ClassicalSixthBranch.v ((675808427:ℝ)/168755200)/ClassicalSixthBranch.r = (75764606728265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3962
  · change upperPayment 3963 ≤ upperValue ((point split endpoint 4096 3963+point split endpoint 4096 3964)/2)
    have hp : upperPayment 3963 = (21997768291:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3963+point split endpoint 4096 3964)/2 = (675833577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675833577:ℝ)/168755200)*ClassicalSixthBranch.v ((675833577:ℝ)/168755200)/ClassicalSixthBranch.r = (75746610808737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3963
  · change upperPayment 3964 ≤ upperValue ((point split endpoint 4096 3964+point split endpoint 4096 3965)/2)
    have hp : upperPayment 3964 = (21834526373:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3964+point split endpoint 4096 3965)/2 = (675858727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675858727:ℝ)/168755200)*ClassicalSixthBranch.v ((675858727:ℝ)/168755200)/ClassicalSixthBranch.r = (75728616913281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3964
  · change upperPayment 3965 ≤ upperValue ((point split endpoint 4096 3965+point split endpoint 4096 3966)/2)
    have hp : upperPayment 3965 = (21671242699:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3965+point split endpoint 4096 3966)/2 = (675883877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675883877:ℝ)/168755200)*ClassicalSixthBranch.v ((675883877:ℝ)/168755200)/ClassicalSixthBranch.r = (75710625041897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3965
  · change upperPayment 3966 ≤ upperValue ((point split endpoint 4096 3966+point split endpoint 4096 3967)/2)
    have hp : upperPayment 3966 = (21507917259:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3966+point split endpoint 4096 3967)/2 = (675909027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675909027:ℝ)/168755200)*ClassicalSixthBranch.v ((675909027:ℝ)/168755200)/ClassicalSixthBranch.r = (75692635194585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3966
  · change upperPayment 3967 ≤ upperValue ((point split endpoint 4096 3967+point split endpoint 4096 3968)/2)
    have hp : upperPayment 3967 = (21344550040:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3967+point split endpoint 4096 3968)/2 = (675934177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675934177:ℝ)/168755200)*ClassicalSixthBranch.v ((675934177:ℝ)/168755200)/ClassicalSixthBranch.r = (75674647371345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3967
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_247
