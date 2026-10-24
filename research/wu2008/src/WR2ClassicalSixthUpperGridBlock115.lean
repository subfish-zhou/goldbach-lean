import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints115
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_115 (j : Fin 16) : upperPayment (16*115+j.val) ≤
    upperValue ((point split endpoint 4096 (16*115+j.val)+point split endpoint 4096 (16*115+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1840 ≤ upperValue ((point split endpoint 4096 1840+point split endpoint 4096 1841)/2)
    have hp : upperPayment 1840 = (289411459907:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1840+point split endpoint 4096 1841)/2 = (622440127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622440127:ℝ)/168755200)*ClassicalSixthBranch.v ((622440127:ℝ)/168755200)/ClassicalSixthBranch.r = (118511176218897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1840
  · change upperPayment 1841 ≤ upperValue ((point split endpoint 4096 1841+point split endpoint 4096 1842)/2)
    have hp : upperPayment 1841 = (289317047982:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1841+point split endpoint 4096 1842)/2 = (622465277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622465277:ℝ)/168755200)*ClassicalSixthBranch.v ((622465277:ℝ)/168755200)/ClassicalSixthBranch.r = (118488885218585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1841
  · change upperPayment 1842 ≤ upperValue ((point split endpoint 4096 1842+point split endpoint 4096 1843)/2)
    have hp : upperPayment 1842 = (289222610634:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1842+point split endpoint 4096 1843)/2 = (622490427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622490427:ℝ)/168755200)*ClassicalSixthBranch.v ((622490427:ℝ)/168755200)/ClassicalSixthBranch.r = (118466596242345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1842
  · change upperPayment 1843 ≤ upperValue ((point split endpoint 4096 1843+point split endpoint 4096 1844)/2)
    have hp : upperPayment 1843 = (289128147858:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1843+point split endpoint 4096 1844)/2 = (622515577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622515577:ℝ)/168755200)*ClassicalSixthBranch.v ((622515577:ℝ)/168755200)/ClassicalSixthBranch.r = (118444309290177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1843
  · change upperPayment 1844 ≤ upperValue ((point split endpoint 4096 1844+point split endpoint 4096 1845)/2)
    have hp : upperPayment 1844 = (289033659647:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1844+point split endpoint 4096 1845)/2 = (622540727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622540727:ℝ)/168755200)*ClassicalSixthBranch.v ((622540727:ℝ)/168755200)/ClassicalSixthBranch.r = (118422024362081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1844
  · change upperPayment 1845 ≤ upperValue ((point split endpoint 4096 1845+point split endpoint 4096 1846)/2)
    have hp : upperPayment 1845 = (288939145999:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1845+point split endpoint 4096 1846)/2 = (622565877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622565877:ℝ)/168755200)*ClassicalSixthBranch.v ((622565877:ℝ)/168755200)/ClassicalSixthBranch.r = (118399741458057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1845
  · change upperPayment 1846 ≤ upperValue ((point split endpoint 4096 1846+point split endpoint 4096 1847)/2)
    have hp : upperPayment 1846 = (288844606907:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1846+point split endpoint 4096 1847)/2 = (622591027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622591027:ℝ)/168755200)*ClassicalSixthBranch.v ((622591027:ℝ)/168755200)/ClassicalSixthBranch.r = (118377460578105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1846
  · change upperPayment 1847 ≤ upperValue ((point split endpoint 4096 1847+point split endpoint 4096 1848)/2)
    have hp : upperPayment 1847 = (288750042367:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1847+point split endpoint 4096 1848)/2 = (622616177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622616177:ℝ)/168755200)*ClassicalSixthBranch.v ((622616177:ℝ)/168755200)/ClassicalSixthBranch.r = (118355181722225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1847
  · change upperPayment 1848 ≤ upperValue ((point split endpoint 4096 1848+point split endpoint 4096 1849)/2)
    have hp : upperPayment 1848 = (288655452375:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1848+point split endpoint 4096 1849)/2 = (622641327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622641327:ℝ)/168755200)*ClassicalSixthBranch.v ((622641327:ℝ)/168755200)/ClassicalSixthBranch.r = (118332904890417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1848
  · change upperPayment 1849 ≤ upperValue ((point split endpoint 4096 1849+point split endpoint 4096 1850)/2)
    have hp : upperPayment 1849 = (288560836924:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1849+point split endpoint 4096 1850)/2 = (622666477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622666477:ℝ)/168755200)*ClassicalSixthBranch.v ((622666477:ℝ)/168755200)/ClassicalSixthBranch.r = (118310630082681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1849
  · change upperPayment 1850 ≤ upperValue ((point split endpoint 4096 1850+point split endpoint 4096 1851)/2)
    have hp : upperPayment 1850 = (288466196011:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1850+point split endpoint 4096 1851)/2 = (622691627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622691627:ℝ)/168755200)*ClassicalSixthBranch.v ((622691627:ℝ)/168755200)/ClassicalSixthBranch.r = (118288357299017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1850
  · change upperPayment 1851 ≤ upperValue ((point split endpoint 4096 1851+point split endpoint 4096 1852)/2)
    have hp : upperPayment 1851 = (288371529631:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1851+point split endpoint 4096 1852)/2 = (622716777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622716777:ℝ)/168755200)*ClassicalSixthBranch.v ((622716777:ℝ)/168755200)/ClassicalSixthBranch.r = (118266086539425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1851
  · change upperPayment 1852 ≤ upperValue ((point split endpoint 4096 1852+point split endpoint 4096 1853)/2)
    have hp : upperPayment 1852 = (288276837778:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1852+point split endpoint 4096 1853)/2 = (622741927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622741927:ℝ)/168755200)*ClassicalSixthBranch.v ((622741927:ℝ)/168755200)/ClassicalSixthBranch.r = (118243817803905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1852
  · change upperPayment 1853 ≤ upperValue ((point split endpoint 4096 1853+point split endpoint 4096 1854)/2)
    have hp : upperPayment 1853 = (288182120447:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1853+point split endpoint 4096 1854)/2 = (622767077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622767077:ℝ)/168755200)*ClassicalSixthBranch.v ((622767077:ℝ)/168755200)/ClassicalSixthBranch.r = (118221551092457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1853
  · change upperPayment 1854 ≤ upperValue ((point split endpoint 4096 1854+point split endpoint 4096 1855)/2)
    have hp : upperPayment 1854 = (288087377635:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1854+point split endpoint 4096 1855)/2 = (622792227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622792227:ℝ)/168755200)*ClassicalSixthBranch.v ((622792227:ℝ)/168755200)/ClassicalSixthBranch.r = (118199286405081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1854
  · change upperPayment 1855 ≤ upperValue ((point split endpoint 4096 1855+point split endpoint 4096 1856)/2)
    have hp : upperPayment 1855 = (287992609336:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1855+point split endpoint 4096 1856)/2 = (622817377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622817377:ℝ)/168755200)*ClassicalSixthBranch.v ((622817377:ℝ)/168755200)/ClassicalSixthBranch.r = (118177023741777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1855
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_115
