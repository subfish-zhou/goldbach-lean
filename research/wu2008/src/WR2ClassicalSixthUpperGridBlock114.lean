import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints114
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_114 (j : Fin 16) : upperPayment (16*114+j.val) ≤
    upperValue ((point split endpoint 4096 (16*114+j.val)+point split endpoint 4096 (16*114+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1824 ≤ upperValue ((point split endpoint 4096 1824+point split endpoint 4096 1825)/2)
    have hp : upperPayment 1824 = (290918597017:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1824+point split endpoint 4096 1825)/2 = (622037727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622037727:ℝ)/168755200)*ClassicalSixthBranch.v ((622037727:ℝ)/168755200)/ClassicalSixthBranch.r = (118868107497681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1824
  · change upperPayment 1825 ≤ upperValue ((point split endpoint 4096 1825+point split endpoint 4096 1826)/2)
    have hp : upperPayment 1825 = (290824591214:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1825+point split endpoint 4096 1826)/2 = (622062877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622062877:ℝ)/168755200)*ClassicalSixthBranch.v ((622062877:ℝ)/168755200)/ClassicalSixthBranch.r = (118845784112217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1825
  · change upperPayment 1826 ≤ upperValue ((point split endpoint 4096 1826+point split endpoint 4096 1827)/2)
    have hp : upperPayment 1826 = (290730560065:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1826+point split endpoint 4096 1827)/2 = (622088027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622088027:ℝ)/168755200)*ClassicalSixthBranch.v ((622088027:ℝ)/168755200)/ClassicalSixthBranch.r = (118823462750825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1826
  · change upperPayment 1827 ≤ upperValue ((point split endpoint 4096 1827+point split endpoint 4096 1828)/2)
    have hp : upperPayment 1827 = (290636503565:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1827+point split endpoint 4096 1828)/2 = (622113177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622113177:ℝ)/168755200)*ClassicalSixthBranch.v ((622113177:ℝ)/168755200)/ClassicalSixthBranch.r = (118801143413505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1827
  · change upperPayment 1828 ≤ upperValue ((point split endpoint 4096 1828+point split endpoint 4096 1829)/2)
    have hp : upperPayment 1828 = (290542421709:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1828+point split endpoint 4096 1829)/2 = (622138327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622138327:ℝ)/168755200)*ClassicalSixthBranch.v ((622138327:ℝ)/168755200)/ClassicalSixthBranch.r = (118778826100257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1828
  · change upperPayment 1829 ≤ upperValue ((point split endpoint 4096 1829+point split endpoint 4096 1830)/2)
    have hp : upperPayment 1829 = (290448314492:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1829+point split endpoint 4096 1830)/2 = (622163477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622163477:ℝ)/168755200)*ClassicalSixthBranch.v ((622163477:ℝ)/168755200)/ClassicalSixthBranch.r = (118756510811081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1829
  · change upperPayment 1830 ≤ upperValue ((point split endpoint 4096 1830+point split endpoint 4096 1831)/2)
    have hp : upperPayment 1830 = (290354181909:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1830+point split endpoint 4096 1831)/2 = (622188627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622188627:ℝ)/168755200)*ClassicalSixthBranch.v ((622188627:ℝ)/168755200)/ClassicalSixthBranch.r = (118734197545977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1830
  · change upperPayment 1831 ≤ upperValue ((point split endpoint 4096 1831+point split endpoint 4096 1832)/2)
    have hp : upperPayment 1831 = (290260023956:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1831+point split endpoint 4096 1832)/2 = (622213777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622213777:ℝ)/168755200)*ClassicalSixthBranch.v ((622213777:ℝ)/168755200)/ClassicalSixthBranch.r = (118711886304945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1831
  · change upperPayment 1832 ≤ upperValue ((point split endpoint 4096 1832+point split endpoint 4096 1833)/2)
    have hp : upperPayment 1832 = (290165840627:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1832+point split endpoint 4096 1833)/2 = (622238927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622238927:ℝ)/168755200)*ClassicalSixthBranch.v ((622238927:ℝ)/168755200)/ClassicalSixthBranch.r = (118689577087985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1832
  · change upperPayment 1833 ≤ upperValue ((point split endpoint 4096 1833+point split endpoint 4096 1834)/2)
    have hp : upperPayment 1833 = (290071631919:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1833+point split endpoint 4096 1834)/2 = (622264077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622264077:ℝ)/168755200)*ClassicalSixthBranch.v ((622264077:ℝ)/168755200)/ClassicalSixthBranch.r = (118667269895097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1833
  · change upperPayment 1834 ≤ upperValue ((point split endpoint 4096 1834+point split endpoint 4096 1835)/2)
    have hp : upperPayment 1834 = (289977397825:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1834+point split endpoint 4096 1835)/2 = (622289227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622289227:ℝ)/168755200)*ClassicalSixthBranch.v ((622289227:ℝ)/168755200)/ClassicalSixthBranch.r = (118644964726281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1834
  · change upperPayment 1835 ≤ upperValue ((point split endpoint 4096 1835+point split endpoint 4096 1836)/2)
    have hp : upperPayment 1835 = (289883138342:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1835+point split endpoint 4096 1836)/2 = (622314377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622314377:ℝ)/168755200)*ClassicalSixthBranch.v ((622314377:ℝ)/168755200)/ClassicalSixthBranch.r = (118622661581537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1835
  · change upperPayment 1836 ≤ upperValue ((point split endpoint 4096 1836+point split endpoint 4096 1837)/2)
    have hp : upperPayment 1836 = (289788853463:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1836+point split endpoint 4096 1837)/2 = (622339527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622339527:ℝ)/168755200)*ClassicalSixthBranch.v ((622339527:ℝ)/168755200)/ClassicalSixthBranch.r = (118600360460865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1836
  · change upperPayment 1837 ≤ upperValue ((point split endpoint 4096 1837+point split endpoint 4096 1838)/2)
    have hp : upperPayment 1837 = (289694543186:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1837+point split endpoint 4096 1838)/2 = (622364677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622364677:ℝ)/168755200)*ClassicalSixthBranch.v ((622364677:ℝ)/168755200)/ClassicalSixthBranch.r = (118578061364265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1837
  · change upperPayment 1838 ≤ upperValue ((point split endpoint 4096 1838+point split endpoint 4096 1839)/2)
    have hp : upperPayment 1838 = (289600207503:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1838+point split endpoint 4096 1839)/2 = (622389827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622389827:ℝ)/168755200)*ClassicalSixthBranch.v ((622389827:ℝ)/168755200)/ClassicalSixthBranch.r = (118555764291737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1838
  · change upperPayment 1839 ≤ upperValue ((point split endpoint 4096 1839+point split endpoint 4096 1840)/2)
    have hp : upperPayment 1839 = (289505846412:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1839+point split endpoint 4096 1840)/2 = (622414977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622414977:ℝ)/168755200)*ClassicalSixthBranch.v ((622414977:ℝ)/168755200)/ClassicalSixthBranch.r = (118533469243281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1839
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_114
