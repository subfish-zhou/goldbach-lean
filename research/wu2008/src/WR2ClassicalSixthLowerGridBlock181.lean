import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints181
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_181 (j : Fin 16) : lowerPayment (16*181+j.val) ≤
    lowerValue ((point 2 split 4096 (16*181+j.val)+point 2 split 4096 (16*181+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2896 ≤ lowerValue ((point 2 split 4096 2896+point 2 split 4096 2897)/2)
    have hp : lowerPayment 2896 = (312100363419:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2896+point 2 split 4096 2897)/2 = (506266283:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((506266283:ℝ)/168755200)/ClassicalSixthBranch.v ((506266283:ℝ)/168755200) = (590076119963:ℝ)/281523612056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2896
  · change lowerPayment 2897 ≤ lowerValue ((point 2 split 4096 2897+point 2 split 4096 2898)/2)
    have hp : lowerPayment 2897 = (312188477442:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2897+point 2 split 4096 2898)/2 = (101264909:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((101264909:ℝ)/33751040)/ClassicalSixthBranch.v ((101264909:ℝ)/33751040) = (589998806289:ℝ)/281475604168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2897
  · change lowerPayment 2898 ≤ lowerValue ((point 2 split 4096 2898+point 2 split 4096 2899)/2)
    have hp : lowerPayment 2898 = (312276594665:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2898+point 2 split 4096 2899)/2 = (506382807:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((506382807:ℝ)/168755200)/ClassicalSixthBranch.v ((506382807:ℝ)/168755200) = (117984298523:ℝ)/56285519256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2898
  · change lowerPayment 2899 ≤ lowerValue ((point 2 split 4096 2899+point 2 split 4096 2900)/2)
    have hp : lowerPayment 2899 = (312364715101:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2899+point 2 split 4096 2900)/2 = (506441069:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((506441069:ℝ)/168755200)/ClassicalSixthBranch.v ((506441069:ℝ)/168755200) = (589844178941:ℝ)/281379588392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2899
  · change lowerPayment 2900 ≤ lowerValue ((point 2 split 4096 2900+point 2 split 4096 2901)/2)
    have hp : lowerPayment 2900 = (312452838766:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2900+point 2 split 4096 2901)/2 = (506499331:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((506499331:ℝ)/168755200)/ClassicalSixthBranch.v ((506499331:ℝ)/168755200) = (589766865267:ℝ)/281331580504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2900
  · change lowerPayment 2901 ≤ lowerValue ((point 2 split 4096 2901+point 2 split 4096 2902)/2)
    have hp : lowerPayment 2901 = (312540965672:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2901+point 2 split 4096 2902)/2 = (506557593:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((506557593:ℝ)/168755200)/ClassicalSixthBranch.v ((506557593:ℝ)/168755200) = (589689551593:ℝ)/281283572616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2901
  · change lowerPayment 2902 ≤ lowerValue ((point 2 split 4096 2902+point 2 split 4096 2903)/2)
    have hp : lowerPayment 2902 = (312629095834:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2902+point 2 split 4096 2903)/2 = (101323171:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((101323171:ℝ)/33751040)/ClassicalSixthBranch.v ((101323171:ℝ)/33751040) = (589612237919:ℝ)/281235564728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2902
  · change lowerPayment 2903 ≤ lowerValue ((point 2 split 4096 2903+point 2 split 4096 2904)/2)
    have hp : lowerPayment 2903 = (312717229266:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2903+point 2 split 4096 2904)/2 = (506674117:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((506674117:ℝ)/168755200)/ClassicalSixthBranch.v ((506674117:ℝ)/168755200) = (117906984849:ℝ)/56237511368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2903
  · change lowerPayment 2904 ≤ lowerValue ((point 2 split 4096 2904+point 2 split 4096 2905)/2)
    have hp : lowerPayment 2904 = (312805365982:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2904+point 2 split 4096 2905)/2 = (506732379:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((506732379:ℝ)/168755200)/ClassicalSixthBranch.v ((506732379:ℝ)/168755200) = (589457610571:ℝ)/281139548952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2904
  · change lowerPayment 2905 ≤ lowerValue ((point 2 split 4096 2905+point 2 split 4096 2906)/2)
    have hp : lowerPayment 2905 = (312893505997:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2905+point 2 split 4096 2906)/2 = (506790641:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((506790641:ℝ)/168755200)/ClassicalSixthBranch.v ((506790641:ℝ)/168755200) = (589380296897:ℝ)/281091541064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2905
  · change lowerPayment 2906 ≤ lowerValue ((point 2 split 4096 2906+point 2 split 4096 2907)/2)
    have hp : lowerPayment 2906 = (312981649324:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2906+point 2 split 4096 2907)/2 = (506848903:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((506848903:ℝ)/168755200)/ClassicalSixthBranch.v ((506848903:ℝ)/168755200) = (589302983223:ℝ)/281043533176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2906
  · change lowerPayment 2907 ≤ lowerValue ((point 2 split 4096 2907+point 2 split 4096 2908)/2)
    have hp : lowerPayment 2907 = (313069795977:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2907+point 2 split 4096 2908)/2 = (101381433:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((101381433:ℝ)/33751040)/ClassicalSixthBranch.v ((101381433:ℝ)/33751040) = (589225669549:ℝ)/280995525288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2907
  · change lowerPayment 2908 ≤ lowerValue ((point 2 split 4096 2908+point 2 split 4096 2909)/2)
    have hp : lowerPayment 2908 = (313157945971:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2908+point 2 split 4096 2909)/2 = (506965427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((506965427:ℝ)/168755200)/ClassicalSixthBranch.v ((506965427:ℝ)/168755200) = (23565934235:ℝ)/11237900696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2908
  · change lowerPayment 2909 ≤ lowerValue ((point 2 split 4096 2909+point 2 split 4096 2910)/2)
    have hp : lowerPayment 2909 = (313246099320:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2909+point 2 split 4096 2910)/2 = (507023689:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((507023689:ℝ)/168755200)/ClassicalSixthBranch.v ((507023689:ℝ)/168755200) = (589071042201:ℝ)/280899509512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2909
  · change lowerPayment 2910 ≤ lowerValue ((point 2 split 4096 2910+point 2 split 4096 2911)/2)
    have hp : lowerPayment 2910 = (313334256038:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2910+point 2 split 4096 2911)/2 = (507081951:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((507081951:ℝ)/168755200)/ClassicalSixthBranch.v ((507081951:ℝ)/168755200) = (588993728527:ℝ)/280851501624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2910
  · change lowerPayment 2911 ≤ lowerValue ((point 2 split 4096 2911+point 2 split 4096 2912)/2)
    have hp : lowerPayment 2911 = (313422416139:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2911+point 2 split 4096 2912)/2 = (507140213:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((507140213:ℝ)/168755200)/ClassicalSixthBranch.v ((507140213:ℝ)/168755200) = (588916414853:ℝ)/280803493736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2911
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_181
