import F1BFullLogNormalize

noncomputable section
open Real Set FirstCRationalPayment F1JointFTC F1ActualSecondFTC
namespace F1BFullFTC

def rationalOne : ℝ := oneD*(1/(2+1727/600)-1/(927/200+1727/600))+
  (oneE/2)*(1/(2+1727/600)^2-1/(927/200+1727/600)^2)

def collectedOne : ℝ := oneA*log refOne+oneB*log refTwo+
  (oneC+oneF/21)*log bRefOne+bOneMinus*log bCrossOneMinus-
    bOnePlus*log bCrossOnePlus+rationalOne

theorem collectedOne_exact : massOne = collectedOne := by
  have hq := quadratic_difference_normalized (oneF/21) (oneG/(1127/200)-oneF/21-oneF/(1127/200)) (22) (21*3/(1127/200)+1) bRefOne
    (by norm_num) (by norm_num) (by norm_num [bRefOne])
  have hquad : quadPrimitiveOne oneF oneG (927/200)-quadPrimitiveOne oneF oneG 2 =
      (oneF/21)*log bRefOne+bOneMinus*log bCrossOneMinus-bOnePlus*log bCrossOnePlus := by
    unfold quadPrimitiveOne bOneMinus bOnePlus bCrossOneMinus bCrossOnePlus
    convert hq using 1 <;> norm_num
    ring
  have hA : log refOne=log (927/200+2)-log ((2:ℝ)+2) := by
    rw [← log_div (by norm_num : (927:ℝ)/200+2 ≠ 0) (by norm_num : (2:ℝ)+2 ≠ 0)]
    norm_num [refOne]
  have hB : log refTwo=log (927/200-2/3)-log ((2:ℝ)-2/3) := by
    rw [← log_div (by norm_num : (927:ℝ)/200-2/3 ≠ 0) (by norm_num : (2:ℝ)-2/3 ≠ 0)]
    norm_num [refTwo]
  have hC : log bRefOne=log (927/200+1727/600)-log ((2:ℝ)+1727/600) := by
    rw [← log_div (by norm_num : (927:ℝ)/200+1727/600 ≠ 0) (by norm_num : (2:ℝ)+1727/600 ≠ 0)]
    norm_num [bRefOne]
  unfold massOne primitiveOne collectedOne rationalOne
  rw [hA,hB,hC]
  rw [hC] at hquad
  unfold polePrimitive
  simp only [sub_neg_eq_add,zero_div,sub_zero]
  linear_combination hquad

def rationalTwo : ℝ := twoD*(1/(2+3581/200)-1/(927/200+3581/200))+
  (twoE/2)*(1/(2+3581/200)^2-1/(927/200+3581/200)^2)

def collectedTwo : ℝ := twoA*log refOne+twoB*log refTwo+
  (twoC+twoF)*log bRefTwo+bTwoMinus*log bCrossTwoMinus-
    bTwoPlus*log bCrossTwoPlus+rationalTwo

theorem collectedTwo_exact : massTwo = collectedTwo := by
  have hq := quadratic_difference_normalized (twoF) (twoG/(1127/200)-twoF-twoF/(1127/200)) (2) (3/(1127/200)+1) bRefTwo
    (by norm_num) (by norm_num) (by norm_num [bRefTwo])
  have hquad : quadPrimitiveTwo twoF twoG (927/200)-quadPrimitiveTwo twoF twoG 2 =
      (twoF)*log bRefTwo+bTwoMinus*log bCrossTwoMinus-bTwoPlus*log bCrossTwoPlus := by
    unfold quadPrimitiveTwo bTwoMinus bTwoPlus bCrossTwoMinus bCrossTwoPlus
    convert hq using 1 <;> norm_num
    ring
  have hA : log refOne=log (927/200+2)-log ((2:ℝ)+2) := by
    rw [← log_div (by norm_num : (927:ℝ)/200+2 ≠ 0) (by norm_num : (2:ℝ)+2 ≠ 0)]
    norm_num [refOne]
  have hB : log refTwo=log (927/200-2/3)-log ((2:ℝ)-2/3) := by
    rw [← log_div (by norm_num : (927:ℝ)/200-2/3 ≠ 0) (by norm_num : (2:ℝ)-2/3 ≠ 0)]
    norm_num [refTwo]
  have hC : log bRefTwo=log (927/200+3581/200)-log ((2:ℝ)+3581/200) := by
    rw [← log_div (by norm_num : (927:ℝ)/200+3581/200 ≠ 0) (by norm_num : (2:ℝ)+3581/200 ≠ 0)]
    norm_num [bRefTwo]
  unfold massTwo primitiveTwo collectedTwo rationalTwo
  rw [hA,hB,hC]
  rw [hC] at hquad
  unfold polePrimitive
  simp only [sub_neg_eq_add,zero_div,sub_zero]
  linear_combination hquad

end F1BFullFTC
