import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints116
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_116 (j : Fin 16) : upperPayment (16*116+j.val) ≤
    upperValue ((point split endpoint 4096 (16*116+j.val)+point split endpoint 4096 (16*116+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1856 ≤ upperValue ((point split endpoint 4096 1856+point split endpoint 4096 1857)/2)
    have hp : upperPayment 1856 = (287897815544:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1856+point split endpoint 4096 1857)/2 = (622842527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622842527:ℝ)/168755200)*ClassicalSixthBranch.v ((622842527:ℝ)/168755200)/ClassicalSixthBranch.r = (118154763102545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1856
  · change upperPayment 1857 ≤ upperValue ((point split endpoint 4096 1857+point split endpoint 4096 1858)/2)
    have hp : upperPayment 1857 = (287802996256:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1857+point split endpoint 4096 1858)/2 = (6047259:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6047259:ℝ)/1638400)*ClassicalSixthBranch.v ((6047259:ℝ)/1638400)/ClassicalSixthBranch.r = (1146917519295:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1857
  · change upperPayment 1858 ≤ upperValue ((point split endpoint 4096 1858+point split endpoint 4096 1859)/2)
    have hp : upperPayment 1858 = (287708151467:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1858+point split endpoint 4096 1859)/2 = (622892827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622892827:ℝ)/168755200)*ClassicalSixthBranch.v ((622892827:ℝ)/168755200)/ClassicalSixthBranch.r = (118110247896297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1858
  · change upperPayment 1859 ≤ upperValue ((point split endpoint 4096 1859+point split endpoint 4096 1860)/2)
    have hp : upperPayment 1859 = (287613281170:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1859+point split endpoint 4096 1860)/2 = (622917977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622917977:ℝ)/168755200)*ClassicalSixthBranch.v ((622917977:ℝ)/168755200)/ClassicalSixthBranch.r = (118087993329281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1859
  · change upperPayment 1860 ≤ upperValue ((point split endpoint 4096 1860+point split endpoint 4096 1861)/2)
    have hp : upperPayment 1860 = (287518385363:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1860+point split endpoint 4096 1861)/2 = (622943127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622943127:ℝ)/168755200)*ClassicalSixthBranch.v ((622943127:ℝ)/168755200)/ClassicalSixthBranch.r = (118065740786337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1860
  · change upperPayment 1861 ≤ upperValue ((point split endpoint 4096 1861+point split endpoint 4096 1862)/2)
    have hp : upperPayment 1861 = (287423464039:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1861+point split endpoint 4096 1862)/2 = (622968277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622968277:ℝ)/168755200)*ClassicalSixthBranch.v ((622968277:ℝ)/168755200)/ClassicalSixthBranch.r = (118043490267465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1861
  · change upperPayment 1862 ≤ upperValue ((point split endpoint 4096 1862+point split endpoint 4096 1863)/2)
    have hp : upperPayment 1862 = (287328517193:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1862+point split endpoint 4096 1863)/2 = (622993427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622993427:ℝ)/168755200)*ClassicalSixthBranch.v ((622993427:ℝ)/168755200)/ClassicalSixthBranch.r = (118021241772665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1862
  · change upperPayment 1863 ≤ upperValue ((point split endpoint 4096 1863+point split endpoint 4096 1864)/2)
    have hp : upperPayment 1863 = (287233544822:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1863+point split endpoint 4096 1864)/2 = (623018577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623018577:ℝ)/168755200)*ClassicalSixthBranch.v ((623018577:ℝ)/168755200)/ClassicalSixthBranch.r = (117998995301937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1863
  · change upperPayment 1864 ≤ upperValue ((point split endpoint 4096 1864+point split endpoint 4096 1865)/2)
    have hp : upperPayment 1864 = (287138546920:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1864+point split endpoint 4096 1865)/2 = (623043727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623043727:ℝ)/168755200)*ClassicalSixthBranch.v ((623043727:ℝ)/168755200)/ClassicalSixthBranch.r = (117976750855281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1864
  · change upperPayment 1865 ≤ upperValue ((point split endpoint 4096 1865+point split endpoint 4096 1866)/2)
    have hp : upperPayment 1865 = (287043523482:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1865+point split endpoint 4096 1866)/2 = (623068877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623068877:ℝ)/168755200)*ClassicalSixthBranch.v ((623068877:ℝ)/168755200)/ClassicalSixthBranch.r = (117954508432697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1865
  · change upperPayment 1866 ≤ upperValue ((point split endpoint 4096 1866+point split endpoint 4096 1867)/2)
    have hp : upperPayment 1866 = (286948474503:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1866+point split endpoint 4096 1867)/2 = (623094027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623094027:ℝ)/168755200)*ClassicalSixthBranch.v ((623094027:ℝ)/168755200)/ClassicalSixthBranch.r = (117932268034185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1866
  · change upperPayment 1867 ≤ upperValue ((point split endpoint 4096 1867+point split endpoint 4096 1868)/2)
    have hp : upperPayment 1867 = (286853399978:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1867+point split endpoint 4096 1868)/2 = (623119177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623119177:ℝ)/168755200)*ClassicalSixthBranch.v ((623119177:ℝ)/168755200)/ClassicalSixthBranch.r = (117910029659745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1867
  · change upperPayment 1868 ≤ upperValue ((point split endpoint 4096 1868+point split endpoint 4096 1869)/2)
    have hp : upperPayment 1868 = (286758299903:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1868+point split endpoint 4096 1869)/2 = (623144327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623144327:ℝ)/168755200)*ClassicalSixthBranch.v ((623144327:ℝ)/168755200)/ClassicalSixthBranch.r = (117887793309377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1868
  · change upperPayment 1869 ≤ upperValue ((point split endpoint 4096 1869+point split endpoint 4096 1870)/2)
    have hp : upperPayment 1869 = (286663174272:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1869+point split endpoint 4096 1870)/2 = (623169477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623169477:ℝ)/168755200)*ClassicalSixthBranch.v ((623169477:ℝ)/168755200)/ClassicalSixthBranch.r = (117865558983081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1869
  · change upperPayment 1870 ≤ upperValue ((point split endpoint 4096 1870+point split endpoint 4096 1871)/2)
    have hp : upperPayment 1870 = (286568023081:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1870+point split endpoint 4096 1871)/2 = (623194627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623194627:ℝ)/168755200)*ClassicalSixthBranch.v ((623194627:ℝ)/168755200)/ClassicalSixthBranch.r = (117843326680857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1870
  · change upperPayment 1871 ≤ upperValue ((point split endpoint 4096 1871+point split endpoint 4096 1872)/2)
    have hp : upperPayment 1871 = (286472846324:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1871+point split endpoint 4096 1872)/2 = (623219777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623219777:ℝ)/168755200)*ClassicalSixthBranch.v ((623219777:ℝ)/168755200)/ClassicalSixthBranch.r = (117821096402705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1871
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_116
