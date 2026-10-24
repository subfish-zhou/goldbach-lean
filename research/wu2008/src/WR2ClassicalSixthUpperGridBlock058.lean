import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints058
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_058 (j : Fin 16) : upperPayment (16*58+j.val) ≤
    upperValue ((point split endpoint 4096 (16*58+j.val)+point split endpoint 4096 (16*58+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 928 ≤ upperValue ((point split endpoint 4096 928+point split endpoint 4096 929)/2)
    have hp : upperPayment 928 = (365492423097:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 928+point split endpoint 4096 929)/2 = (599503327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599503327:ℝ)/168755200)*ClassicalSixthBranch.v ((599503327:ℝ)/168755200)/ClassicalSixthBranch.r = (139683246351057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_928
  · change upperPayment 929 ≤ upperValue ((point split endpoint 4096 929+point split endpoint 4096 930)/2)
    have hp : upperPayment 929 = (365419408322:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 929+point split endpoint 4096 930)/2 = (599528477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599528477:ℝ)/168755200)*ClassicalSixthBranch.v ((599528477:ℝ)/168755200)/ClassicalSixthBranch.r = (139659109397081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_929
  · change upperPayment 930 ≤ upperValue ((point split endpoint 4096 930+point split endpoint 4096 931)/2)
    have hp : upperPayment 930 = (365346371809:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 930+point split endpoint 4096 931)/2 = (5820909:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((5820909:ℝ)/1638400)*ClassicalSixthBranch.v ((5820909:ℝ)/1638400)/ClassicalSixthBranch.r = (1355679363759:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_930
  · change upperPayment 931 ≤ upperValue ((point split endpoint 4096 931+point split endpoint 4096 932)/2)
    have hp : upperPayment 931 = (365273313554:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 931+point split endpoint 4096 932)/2 = (599578777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599578777:ℝ)/168755200)*ClassicalSixthBranch.v ((599578777:ℝ)/168755200)/ClassicalSixthBranch.r = (139610841561345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_931
  · change upperPayment 932 ≤ upperValue ((point split endpoint 4096 932+point split endpoint 4096 933)/2)
    have hp : upperPayment 932 = (365200233554:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 932+point split endpoint 4096 933)/2 = (599603927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599603927:ℝ)/168755200)*ClassicalSixthBranch.v ((599603927:ℝ)/168755200)/ClassicalSixthBranch.r = (139586710679585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_932
  · change upperPayment 933 ≤ upperValue ((point split endpoint 4096 933+point split endpoint 4096 934)/2)
    have hp : upperPayment 933 = (365127131806:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 933+point split endpoint 4096 934)/2 = (599629077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599629077:ℝ)/168755200)*ClassicalSixthBranch.v ((599629077:ℝ)/168755200)/ClassicalSixthBranch.r = (139562581821897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_933
  · change upperPayment 934 ≤ upperValue ((point split endpoint 4096 934+point split endpoint 4096 935)/2)
    have hp : upperPayment 934 = (365054008307:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 934+point split endpoint 4096 935)/2 = (599654227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599654227:ℝ)/168755200)*ClassicalSixthBranch.v ((599654227:ℝ)/168755200)/ClassicalSixthBranch.r = (139538454988281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_934
  · change upperPayment 935 ≤ upperValue ((point split endpoint 4096 935+point split endpoint 4096 936)/2)
    have hp : upperPayment 935 = (364980863053:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 935+point split endpoint 4096 936)/2 = (599679377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599679377:ℝ)/168755200)*ClassicalSixthBranch.v ((599679377:ℝ)/168755200)/ClassicalSixthBranch.r = (139514330178737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_935
  · change upperPayment 936 ≤ upperValue ((point split endpoint 4096 936+point split endpoint 4096 937)/2)
    have hp : upperPayment 936 = (364907696040:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 936+point split endpoint 4096 937)/2 = (599704527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599704527:ℝ)/168755200)*ClassicalSixthBranch.v ((599704527:ℝ)/168755200)/ClassicalSixthBranch.r = (139490207393265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_936
  · change upperPayment 937 ≤ upperValue ((point split endpoint 4096 937+point split endpoint 4096 938)/2)
    have hp : upperPayment 937 = (364834507267:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 937+point split endpoint 4096 938)/2 = (599729677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599729677:ℝ)/168755200)*ClassicalSixthBranch.v ((599729677:ℝ)/168755200)/ClassicalSixthBranch.r = (139466086631865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_937
  · change upperPayment 938 ≤ upperValue ((point split endpoint 4096 938+point split endpoint 4096 939)/2)
    have hp : upperPayment 938 = (364761296728:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 938+point split endpoint 4096 939)/2 = (599754827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599754827:ℝ)/168755200)*ClassicalSixthBranch.v ((599754827:ℝ)/168755200)/ClassicalSixthBranch.r = (139441967894537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_938
  · change upperPayment 939 ≤ upperValue ((point split endpoint 4096 939+point split endpoint 4096 940)/2)
    have hp : upperPayment 939 = (364688064422:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 939+point split endpoint 4096 940)/2 = (599779977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599779977:ℝ)/168755200)*ClassicalSixthBranch.v ((599779977:ℝ)/168755200)/ClassicalSixthBranch.r = (139417851181281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_939
  · change upperPayment 940 ≤ upperValue ((point split endpoint 4096 940+point split endpoint 4096 941)/2)
    have hp : upperPayment 940 = (364614810344:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 940+point split endpoint 4096 941)/2 = (599805127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599805127:ℝ)/168755200)*ClassicalSixthBranch.v ((599805127:ℝ)/168755200)/ClassicalSixthBranch.r = (139393736492097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_940
  · change upperPayment 941 ≤ upperValue ((point split endpoint 4096 941+point split endpoint 4096 942)/2)
    have hp : upperPayment 941 = (364541534492:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 941+point split endpoint 4096 942)/2 = (599830277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599830277:ℝ)/168755200)*ClassicalSixthBranch.v ((599830277:ℝ)/168755200)/ClassicalSixthBranch.r = (139369623826985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_941
  · change upperPayment 942 ≤ upperValue ((point split endpoint 4096 942+point split endpoint 4096 943)/2)
    have hp : upperPayment 942 = (364468236862:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 942+point split endpoint 4096 943)/2 = (599855427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599855427:ℝ)/168755200)*ClassicalSixthBranch.v ((599855427:ℝ)/168755200)/ClassicalSixthBranch.r = (139345513185945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_942
  · change upperPayment 943 ≤ upperValue ((point split endpoint 4096 943+point split endpoint 4096 944)/2)
    have hp : upperPayment 943 = (364394917450:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 943+point split endpoint 4096 944)/2 = (599880577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599880577:ℝ)/168755200)*ClassicalSixthBranch.v ((599880577:ℝ)/168755200)/ClassicalSixthBranch.r = (139321404568977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_943
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_058
