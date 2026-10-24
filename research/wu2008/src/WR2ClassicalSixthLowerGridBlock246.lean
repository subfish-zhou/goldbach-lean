import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints246
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_246 (j : Fin 16) : lowerPayment (16*246+j.val) ≤
    lowerValue ((point 2 split 4096 (16*246+j.val)+point 2 split 4096 (16*246+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3936 ≤ lowerValue ((point 2 split 4096 3936+point 2 split 4096 3937)/2)
    have hp : lowerPayment 3936 = (408186611124:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3936+point 2 split 4096 3937)/2 = (566858763:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((566858763:ℝ)/168755200)/ClassicalSixthBranch.v ((566858763:ℝ)/168755200) = (509669899003:ℝ)/231595408536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3936
  · change lowerPayment 3937 ≤ lowerValue ((point 2 split 4096 3937+point 2 split 4096 3938)/2)
    have hp : lowerPayment 3937 = (408286060218:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3937+point 2 split 4096 3938)/2 = (22676681:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((22676681:ℝ)/6750208)/ClassicalSixthBranch.v ((22676681:ℝ)/6750208) = (509592585329:ℝ)/231547400648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3937
  · change lowerPayment 3938 ≤ lowerValue ((point 2 split 4096 3938+point 2 split 4096 3939)/2)
    have hp : lowerPayment 3938 = (408385528646:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3938+point 2 split 4096 3939)/2 = (566975287:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((566975287:ℝ)/168755200)/ClassicalSixthBranch.v ((566975287:ℝ)/168755200) = (101903054331:ℝ)/46299878552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3938
  · change lowerPayment 3939 ≤ lowerValue ((point 2 split 4096 3939+point 2 split 4096 3940)/2)
    have hp : lowerPayment 3939 = (408485016427:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3939+point 2 split 4096 3940)/2 = (567033549:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((567033549:ℝ)/168755200)/ClassicalSixthBranch.v ((567033549:ℝ)/168755200) = (509437957981:ℝ)/231451384872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3939
  · change lowerPayment 3940 ≤ lowerValue ((point 2 split 4096 3940+point 2 split 4096 3941)/2)
    have hp : lowerPayment 3940 = (408584523579:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3940+point 2 split 4096 3941)/2 = (567091811:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((567091811:ℝ)/168755200)/ClassicalSixthBranch.v ((567091811:ℝ)/168755200) = (509360644307:ℝ)/231403376984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3940
  · change lowerPayment 3941 ≤ lowerValue ((point 2 split 4096 3941+point 2 split 4096 3942)/2)
    have hp : lowerPayment 3941 = (408684050121:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3941+point 2 split 4096 3942)/2 = (567150073:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((567150073:ℝ)/168755200)/ClassicalSixthBranch.v ((567150073:ℝ)/168755200) = (1012491711:ℝ)/459951032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3941
  · change lowerPayment 3942 ≤ lowerValue ((point 2 split 4096 3942+point 2 split 4096 3943)/2)
    have hp : lowerPayment 3942 = (408783596071:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3942+point 2 split 4096 3943)/2 = (113441667:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((113441667:ℝ)/33751040)/ClassicalSixthBranch.v ((113441667:ℝ)/33751040) = (509206016959:ℝ)/231307361208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3942
  · change lowerPayment 3943 ≤ lowerValue ((point 2 split 4096 3943+point 2 split 4096 3944)/2)
    have hp : lowerPayment 3943 = (408883161447:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3943+point 2 split 4096 3944)/2 = (567266597:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((567266597:ℝ)/168755200)/ClassicalSixthBranch.v ((567266597:ℝ)/168755200) = (101825740657:ℝ)/46251870664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3943
  · change lowerPayment 3944 ≤ lowerValue ((point 2 split 4096 3944+point 2 split 4096 3945)/2)
    have hp : lowerPayment 3944 = (408982746267:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3944+point 2 split 4096 3945)/2 = (567324859:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((567324859:ℝ)/168755200)/ClassicalSixthBranch.v ((567324859:ℝ)/168755200) = (509051389611:ℝ)/231211345432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3944
  · change lowerPayment 3945 ≤ lowerValue ((point 2 split 4096 3945+point 2 split 4096 3946)/2)
    have hp : lowerPayment 3945 = (409082350551:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3945+point 2 split 4096 3946)/2 = (567383121:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((567383121:ℝ)/168755200)/ClassicalSixthBranch.v ((567383121:ℝ)/168755200) = (508974075937:ℝ)/231163337544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3945
  · change lowerPayment 3946 ≤ lowerValue ((point 2 split 4096 3946+point 2 split 4096 3947)/2)
    have hp : lowerPayment 3946 = (409181974316:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3946+point 2 split 4096 3947)/2 = (567441383:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((567441383:ℝ)/168755200)/ClassicalSixthBranch.v ((567441383:ℝ)/168755200) = (508896762263:ℝ)/231115329656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3946
  · change lowerPayment 3947 ≤ lowerValue ((point 2 split 4096 3947+point 2 split 4096 3948)/2)
    have hp : lowerPayment 3947 = (409281617582:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3947+point 2 split 4096 3948)/2 = (113499929:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((113499929:ℝ)/33751040)/ClassicalSixthBranch.v ((113499929:ℝ)/33751040) = (508819448589:ℝ)/231067321768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3947
  · change lowerPayment 3948 ≤ lowerValue ((point 2 split 4096 3948+point 2 split 4096 3949)/2)
    have hp : lowerPayment 3948 = (409381280365:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3948+point 2 split 4096 3949)/2 = (567557907:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((567557907:ℝ)/168755200)/ClassicalSixthBranch.v ((567557907:ℝ)/168755200) = (101748426983:ℝ)/46203862776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3948
  · change lowerPayment 3949 ≤ lowerValue ((point 2 split 4096 3949+point 2 split 4096 3950)/2)
    have hp : lowerPayment 3949 = (409480962685:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3949+point 2 split 4096 3950)/2 = (567616169:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((567616169:ℝ)/168755200)/ClassicalSixthBranch.v ((567616169:ℝ)/168755200) = (508664821241:ℝ)/230971305992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3949
  · change lowerPayment 3950 ≤ lowerValue ((point 2 split 4096 3950+point 2 split 4096 3951)/2)
    have hp : lowerPayment 3950 = (409580664561:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3950+point 2 split 4096 3951)/2 = (567674431:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((567674431:ℝ)/168755200)/ClassicalSixthBranch.v ((567674431:ℝ)/168755200) = (508587507567:ℝ)/230923298104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3950
  · change lowerPayment 3951 ≤ lowerValue ((point 2 split 4096 3951+point 2 split 4096 3952)/2)
    have hp : lowerPayment 3951 = (409680386010:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3951+point 2 split 4096 3952)/2 = (567732693:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((567732693:ℝ)/168755200)/ClassicalSixthBranch.v ((567732693:ℝ)/168755200) = (508510193893:ℝ)/230875290216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3951
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_246
