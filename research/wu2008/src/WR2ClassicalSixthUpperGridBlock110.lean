import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints110
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_110 (j : Fin 16) : upperPayment (16*110+j.val) ≤
    upperValue ((point split endpoint 4096 (16*110+j.val)+point split endpoint 4096 (16*110+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1760 ≤ upperValue ((point split endpoint 4096 1760+point split endpoint 4096 1761)/2)
    have hp : upperPayment 1760 = (296882467089:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1760+point split endpoint 4096 1761)/2 = (620428127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620428127:ℝ)/168755200)*ClassicalSixthBranch.v ((620428127:ℝ)/168755200)/ClassicalSixthBranch.r = (120301014237137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1760
  · change upperPayment 1761 ≤ upperValue ((point split endpoint 4096 1761+point split endpoint 4096 1762)/2)
    have hp : upperPayment 1761 = (296790073513:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1761+point split endpoint 4096 1762)/2 = (620453277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620453277:ℝ)/168755200)*ClassicalSixthBranch.v ((620453277:ℝ)/168755200)/ClassicalSixthBranch.r = (120278561311065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1761
  · change upperPayment 1762 ≤ upperValue ((point split endpoint 4096 1762+point split endpoint 4096 1763)/2)
    have hp : upperPayment 1762 = (296697654896:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1762+point split endpoint 4096 1763)/2 = (620478427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620478427:ℝ)/168755200)*ClassicalSixthBranch.v ((620478427:ℝ)/168755200)/ClassicalSixthBranch.r = (120256110409065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1762
  · change upperPayment 1763 ≤ upperValue ((point split endpoint 4096 1763+point split endpoint 4096 1764)/2)
    have hp : upperPayment 1763 = (296605211232:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1763+point split endpoint 4096 1764)/2 = (620503577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620503577:ℝ)/168755200)*ClassicalSixthBranch.v ((620503577:ℝ)/168755200)/ClassicalSixthBranch.r = (120233661531137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1763
  · change upperPayment 1764 ≤ upperValue ((point split endpoint 4096 1764+point split endpoint 4096 1765)/2)
    have hp : upperPayment 1764 = (296512742517:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1764+point split endpoint 4096 1765)/2 = (620528727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620528727:ℝ)/168755200)*ClassicalSixthBranch.v ((620528727:ℝ)/168755200)/ClassicalSixthBranch.r = (120211214677281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1764
  · change upperPayment 1765 ≤ upperValue ((point split endpoint 4096 1765+point split endpoint 4096 1766)/2)
    have hp : upperPayment 1765 = (296420248746:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1765+point split endpoint 4096 1766)/2 = (620553877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620553877:ℝ)/168755200)*ClassicalSixthBranch.v ((620553877:ℝ)/168755200)/ClassicalSixthBranch.r = (120188769847497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1765
  · change upperPayment 1766 ≤ upperValue ((point split endpoint 4096 1766+point split endpoint 4096 1767)/2)
    have hp : upperPayment 1766 = (296327729915:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1766+point split endpoint 4096 1767)/2 = (620579027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620579027:ℝ)/168755200)*ClassicalSixthBranch.v ((620579027:ℝ)/168755200)/ClassicalSixthBranch.r = (120166327041785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1766
  · change upperPayment 1767 ≤ upperValue ((point split endpoint 4096 1767+point split endpoint 4096 1768)/2)
    have hp : upperPayment 1767 = (296235186018:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1767+point split endpoint 4096 1768)/2 = (620604177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620604177:ℝ)/168755200)*ClassicalSixthBranch.v ((620604177:ℝ)/168755200)/ClassicalSixthBranch.r = (120143886260145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1767
  · change upperPayment 1768 ≤ upperValue ((point split endpoint 4096 1768+point split endpoint 4096 1769)/2)
    have hp : upperPayment 1768 = (296142617051:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1768+point split endpoint 4096 1769)/2 = (620629327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620629327:ℝ)/168755200)*ClassicalSixthBranch.v ((620629327:ℝ)/168755200)/ClassicalSixthBranch.r = (120121447502577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1768
  · change upperPayment 1769 ≤ upperValue ((point split endpoint 4096 1769+point split endpoint 4096 1770)/2)
    have hp : upperPayment 1769 = (296050023010:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1769+point split endpoint 4096 1770)/2 = (620654477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620654477:ℝ)/168755200)*ClassicalSixthBranch.v ((620654477:ℝ)/168755200)/ClassicalSixthBranch.r = (120099010769081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1769
  · change upperPayment 1770 ≤ upperValue ((point split endpoint 4096 1770+point split endpoint 4096 1771)/2)
    have hp : upperPayment 1770 = (295957403889:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1770+point split endpoint 4096 1771)/2 = (620679627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620679627:ℝ)/168755200)*ClassicalSixthBranch.v ((620679627:ℝ)/168755200)/ClassicalSixthBranch.r = (120076576059657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1770
  · change upperPayment 1771 ≤ upperValue ((point split endpoint 4096 1771+point split endpoint 4096 1772)/2)
    have hp : upperPayment 1771 = (295864759684:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1771+point split endpoint 4096 1772)/2 = (620704777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620704777:ℝ)/168755200)*ClassicalSixthBranch.v ((620704777:ℝ)/168755200)/ClassicalSixthBranch.r = (120054143374305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1771
  · change upperPayment 1772 ≤ upperValue ((point split endpoint 4096 1772+point split endpoint 4096 1773)/2)
    have hp : upperPayment 1772 = (295772090390:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1772+point split endpoint 4096 1773)/2 = (620729927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620729927:ℝ)/168755200)*ClassicalSixthBranch.v ((620729927:ℝ)/168755200)/ClassicalSixthBranch.r = (120031712713025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1772
  · change upperPayment 1773 ≤ upperValue ((point split endpoint 4096 1773+point split endpoint 4096 1774)/2)
    have hp : upperPayment 1773 = (295679396002:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1773+point split endpoint 4096 1774)/2 = (620755077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620755077:ℝ)/168755200)*ClassicalSixthBranch.v ((620755077:ℝ)/168755200)/ClassicalSixthBranch.r = (120009284075817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1773
  · change upperPayment 1774 ≤ upperValue ((point split endpoint 4096 1774+point split endpoint 4096 1775)/2)
    have hp : upperPayment 1774 = (295586676516:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1774+point split endpoint 4096 1775)/2 = (620780227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620780227:ℝ)/168755200)*ClassicalSixthBranch.v ((620780227:ℝ)/168755200)/ClassicalSixthBranch.r = (119986857462681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1774
  · change upperPayment 1775 ≤ upperValue ((point split endpoint 4096 1775+point split endpoint 4096 1776)/2)
    have hp : upperPayment 1775 = (295493931927:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1775+point split endpoint 4096 1776)/2 = (620805377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620805377:ℝ)/168755200)*ClassicalSixthBranch.v ((620805377:ℝ)/168755200)/ClassicalSixthBranch.r = (119964432873617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1775
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_110
