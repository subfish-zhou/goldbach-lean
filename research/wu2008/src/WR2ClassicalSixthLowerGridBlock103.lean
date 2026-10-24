import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints103
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_103 (j : Fin 16) : lowerPayment (16*103+j.val) ≤
    lowerValue ((point 2 split 4096 (16*103+j.val)+point 2 split 4096 (16*103+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1648 ≤ lowerValue ((point 2 split 4096 1648+point 2 split 4096 1649)/2)
    have hp : lowerPayment 1648 = (199898062790:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1648+point 2 split 4096 1649)/2 = (433555307:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((433555307:ℝ)/168755200)/ClassicalSixthBranch.v ((433555307:ℝ)/168755200) = (137312717023:ℝ)/68287491256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1648
  · change lowerPayment 1649 ≤ lowerValue ((point 2 split 4096 1649+point 2 split 4096 1650)/2)
    have hp : lowerPayment 1649 = (199993801108:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1649+point 2 split 4096 1650)/2 = (433613569:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((433613569:ℝ)/168755200)/ClassicalSixthBranch.v ((433613569:ℝ)/168755200) = (686486271441:ℝ)/341389448392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1649
  · change lowerPayment 1650 ≤ lowerValue ((point 2 split 4096 1650+point 2 split 4096 1651)/2)
    have hp : lowerPayment 1650 = (200089522909:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1650+point 2 split 4096 1651)/2 = (433671831:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((433671831:ℝ)/168755200)/ClassicalSixthBranch.v ((433671831:ℝ)/168755200) = (686408957767:ℝ)/341341440504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1650
  · change lowerPayment 1651 ≤ lowerValue ((point 2 split 4096 1651+point 2 split 4096 1652)/2)
    have hp : lowerPayment 1651 = (200185228212:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1651+point 2 split 4096 1652)/2 = (433730093:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((433730093:ℝ)/168755200)/ClassicalSixthBranch.v ((433730093:ℝ)/168755200) = (686331644093:ℝ)/341293432616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1651
  · change lowerPayment 1652 ≤ lowerValue ((point 2 split 4096 1652+point 2 split 4096 1653)/2)
    have hp : lowerPayment 1652 = (200280917038:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1652+point 2 split 4096 1653)/2 = (86757671:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((86757671:ℝ)/33751040)/ClassicalSixthBranch.v ((86757671:ℝ)/33751040) = (686254330419:ℝ)/341245424728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1652
  · change lowerPayment 1653 ≤ lowerValue ((point 2 split 4096 1653+point 2 split 4096 1654)/2)
    have hp : lowerPayment 1653 = (200376589405:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1653+point 2 split 4096 1654)/2 = (433846617:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((433846617:ℝ)/168755200)/ClassicalSixthBranch.v ((433846617:ℝ)/168755200) = (137235403349:ℝ)/68239483368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1653
  · change lowerPayment 1654 ≤ lowerValue ((point 2 split 4096 1654+point 2 split 4096 1655)/2)
    have hp : lowerPayment 1654 = (200472245333:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1654+point 2 split 4096 1655)/2 = (433904879:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((433904879:ℝ)/168755200)/ClassicalSixthBranch.v ((433904879:ℝ)/168755200) = (686099703071:ℝ)/341149408952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1654
  · change lowerPayment 1655 ≤ lowerValue ((point 2 split 4096 1655+point 2 split 4096 1656)/2)
    have hp : lowerPayment 1655 = (200567884843:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1655+point 2 split 4096 1656)/2 = (433963141:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((433963141:ℝ)/168755200)/ClassicalSixthBranch.v ((433963141:ℝ)/168755200) = (686022389397:ℝ)/341101401064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1655
  · change lowerPayment 1656 ≤ lowerValue ((point 2 split 4096 1656+point 2 split 4096 1657)/2)
    have hp : lowerPayment 1656 = (200663507953:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1656+point 2 split 4096 1657)/2 = (434021403:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((434021403:ℝ)/168755200)/ClassicalSixthBranch.v ((434021403:ℝ)/168755200) = (685945075723:ℝ)/341053393176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1656
  · change lowerPayment 1657 ≤ lowerValue ((point 2 split 4096 1657+point 2 split 4096 1658)/2)
    have hp : lowerPayment 1657 = (200759114682:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1657+point 2 split 4096 1658)/2 = (86815933:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((86815933:ℝ)/33751040)/ClassicalSixthBranch.v ((86815933:ℝ)/33751040) = (685867762049:ℝ)/341005385288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1657
  · change lowerPayment 1658 ≤ lowerValue ((point 2 split 4096 1658+point 2 split 4096 1659)/2)
    have hp : lowerPayment 1658 = (200854705052:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1658+point 2 split 4096 1659)/2 = (434137927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((434137927:ℝ)/168755200)/ClassicalSixthBranch.v ((434137927:ℝ)/168755200) = (27431617935:ℝ)/13638295096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1658
  · change lowerPayment 1659 ≤ lowerValue ((point 2 split 4096 1659+point 2 split 4096 1660)/2)
    have hp : lowerPayment 1659 = (200950279080:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1659+point 2 split 4096 1660)/2 = (434196189:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((434196189:ℝ)/168755200)/ClassicalSixthBranch.v ((434196189:ℝ)/168755200) = (685713134701:ℝ)/340909369512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1659
  · change lowerPayment 1660 ≤ lowerValue ((point 2 split 4096 1660+point 2 split 4096 1661)/2)
    have hp : lowerPayment 1660 = (201045836787:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1660+point 2 split 4096 1661)/2 = (434254451:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((434254451:ℝ)/168755200)/ClassicalSixthBranch.v ((434254451:ℝ)/168755200) = (685635821027:ℝ)/340861361624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1660
  · change lowerPayment 1661 ≤ lowerValue ((point 2 split 4096 1661+point 2 split 4096 1662)/2)
    have hp : lowerPayment 1661 = (201141378192:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1661+point 2 split 4096 1662)/2 = (434312713:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((434312713:ℝ)/168755200)/ClassicalSixthBranch.v ((434312713:ℝ)/168755200) = (685558507353:ℝ)/340813353736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1661
  · change lowerPayment 1662 ≤ lowerValue ((point 2 split 4096 1662+point 2 split 4096 1663)/2)
    have hp : lowerPayment 1662 = (201236903315:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1662+point 2 split 4096 1663)/2 = (17374839:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((17374839:ℝ)/6750208)/ClassicalSixthBranch.v ((17374839:ℝ)/6750208) = (685481193679:ℝ)/340765345848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1662
  · change lowerPayment 1663 ≤ lowerValue ((point 2 split 4096 1663+point 2 split 4096 1664)/2)
    have hp : lowerPayment 1663 = (201332412174:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1663+point 2 split 4096 1664)/2 = (434429237:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((434429237:ℝ)/168755200)/ClassicalSixthBranch.v ((434429237:ℝ)/168755200) = (137080776001:ℝ)/68143467592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1663
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_103
