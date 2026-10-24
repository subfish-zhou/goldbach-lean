import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints113
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_113 (j : Fin 16) : upperPayment (16*113+j.val) ≤
    upperValue ((point split endpoint 4096 (16*113+j.val)+point split endpoint 4096 (16*113+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1808 ≤ upperValue ((point split endpoint 4096 1808+point split endpoint 4096 1809)/2)
    have hp : upperPayment 1808 = (292419246679:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1808+point split endpoint 4096 1809)/2 = (621635327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621635327:ℝ)/168755200)*ClassicalSixthBranch.v ((621635327:ℝ)/168755200)/ClassicalSixthBranch.r = (119225556938897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1808
  · change upperPayment 1809 ≤ upperValue ((point split endpoint 4096 1809+point split endpoint 4096 1810)/2)
    have hp : upperPayment 1809 = (292325645764:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1809+point split endpoint 4096 1810)/2 = (621660477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621660477:ℝ)/168755200)*ClassicalSixthBranch.v ((621660477:ℝ)/168755200)/ClassicalSixthBranch.r = (119203201168281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1809
  · change upperPayment 1810 ≤ upperValue ((point split endpoint 4096 1810+point split endpoint 4096 1811)/2)
    have hp : upperPayment 1810 = (292232019579:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1810+point split endpoint 4096 1811)/2 = (621685627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621685627:ℝ)/168755200)*ClassicalSixthBranch.v ((621685627:ℝ)/168755200)/ClassicalSixthBranch.r = (119180847421737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1810
  · change upperPayment 1811 ≤ upperValue ((point split endpoint 4096 1811+point split endpoint 4096 1812)/2)
    have hp : upperPayment 1811 = (292138368121:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1811+point split endpoint 4096 1812)/2 = (621710777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621710777:ℝ)/168755200)*ClassicalSixthBranch.v ((621710777:ℝ)/168755200)/ClassicalSixthBranch.r = (119158495699265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1811
  · change upperPayment 1812 ≤ upperValue ((point split endpoint 4096 1812+point split endpoint 4096 1813)/2)
    have hp : upperPayment 1812 = (292044691383:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1812+point split endpoint 4096 1813)/2 = (621735927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621735927:ℝ)/168755200)*ClassicalSixthBranch.v ((621735927:ℝ)/168755200)/ClassicalSixthBranch.r = (119136146000865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1812
  · change upperPayment 1813 ≤ upperValue ((point split endpoint 4096 1813+point split endpoint 4096 1814)/2)
    have hp : upperPayment 1813 = (291950989362:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1813+point split endpoint 4096 1814)/2 = (621761077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621761077:ℝ)/168755200)*ClassicalSixthBranch.v ((621761077:ℝ)/168755200)/ClassicalSixthBranch.r = (119113798326537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1813
  · change upperPayment 1814 ≤ upperValue ((point split endpoint 4096 1814+point split endpoint 4096 1815)/2)
    have hp : upperPayment 1814 = (291857262052:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1814+point split endpoint 4096 1815)/2 = (621786227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621786227:ℝ)/168755200)*ClassicalSixthBranch.v ((621786227:ℝ)/168755200)/ClassicalSixthBranch.r = (119091452676281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1814
  · change upperPayment 1815 ≤ upperValue ((point split endpoint 4096 1815+point split endpoint 4096 1816)/2)
    have hp : upperPayment 1815 = (291763509448:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1815+point split endpoint 4096 1816)/2 = (621811377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621811377:ℝ)/168755200)*ClassicalSixthBranch.v ((621811377:ℝ)/168755200)/ClassicalSixthBranch.r = (119069109050097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1815
  · change upperPayment 1816 ≤ upperValue ((point split endpoint 4096 1816+point split endpoint 4096 1817)/2)
    have hp : upperPayment 1816 = (291669731546:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1816+point split endpoint 4096 1817)/2 = (621836527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621836527:ℝ)/168755200)*ClassicalSixthBranch.v ((621836527:ℝ)/168755200)/ClassicalSixthBranch.r = (119046767447985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1816
  · change upperPayment 1817 ≤ upperValue ((point split endpoint 4096 1817+point split endpoint 4096 1818)/2)
    have hp : upperPayment 1817 = (291575928341:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1817+point split endpoint 4096 1818)/2 = (621861677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621861677:ℝ)/168755200)*ClassicalSixthBranch.v ((621861677:ℝ)/168755200)/ClassicalSixthBranch.r = (119024427869945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1817
  · change upperPayment 1818 ≤ upperValue ((point split endpoint 4096 1818+point split endpoint 4096 1819)/2)
    have hp : upperPayment 1818 = (291482099828:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1818+point split endpoint 4096 1819)/2 = (621886827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621886827:ℝ)/168755200)*ClassicalSixthBranch.v ((621886827:ℝ)/168755200)/ClassicalSixthBranch.r = (119002090315977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1818
  · change upperPayment 1819 ≤ upperValue ((point split endpoint 4096 1819+point split endpoint 4096 1820)/2)
    have hp : upperPayment 1819 = (291388246003:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1819+point split endpoint 4096 1820)/2 = (621911977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621911977:ℝ)/168755200)*ClassicalSixthBranch.v ((621911977:ℝ)/168755200)/ClassicalSixthBranch.r = (118979754786081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1819
  · change upperPayment 1820 ≤ upperValue ((point split endpoint 4096 1820+point split endpoint 4096 1821)/2)
    have hp : upperPayment 1820 = (291294366860:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1820+point split endpoint 4096 1821)/2 = (621937127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621937127:ℝ)/168755200)*ClassicalSixthBranch.v ((621937127:ℝ)/168755200)/ClassicalSixthBranch.r = (118957421280257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1820
  · change upperPayment 1821 ≤ upperValue ((point split endpoint 4096 1821+point split endpoint 4096 1822)/2)
    have hp : upperPayment 1821 = (291200462394:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1821+point split endpoint 4096 1822)/2 = (621962277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621962277:ℝ)/168755200)*ClassicalSixthBranch.v ((621962277:ℝ)/168755200)/ClassicalSixthBranch.r = (118935089798505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1821
  · change upperPayment 1822 ≤ upperValue ((point split endpoint 4096 1822+point split endpoint 4096 1823)/2)
    have hp : upperPayment 1822 = (291106532602:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1822+point split endpoint 4096 1823)/2 = (621987427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621987427:ℝ)/168755200)*ClassicalSixthBranch.v ((621987427:ℝ)/168755200)/ClassicalSixthBranch.r = (118912760340825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1822
  · change upperPayment 1823 ≤ upperValue ((point split endpoint 4096 1823+point split endpoint 4096 1824)/2)
    have hp : upperPayment 1823 = (291012577478:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1823+point split endpoint 4096 1824)/2 = (622012577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((622012577:ℝ)/168755200)*ClassicalSixthBranch.v ((622012577:ℝ)/168755200)/ClassicalSixthBranch.r = (118890432907217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1823
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_113
