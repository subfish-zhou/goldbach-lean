import F1BFullConsumption

noncomputable section
open Real Set FirstCRationalPayment F1JointFTC
namespace F1BFullFTC

theorem quadratic_difference_normalized (f g x y t : ℝ)
    (hx : 0 < x) (hy : 0 < y) (ht : 0 < t) :
    quadraticPrimitive f g x-quadraticPrimitive f g y =
      f*log t+(f/2+(g-8*f)/(2*root))*log ((x+8-root)/((y+8-root)*t))-
        (f/2-(g-8*f)/(2*root))*log (t*(y+8+root)/(x+8+root)) := by
  have hxm : 0 < x+8-root := by linarith only [hx,root_lt_eight]
  have hxp : 0 < x+8+root := by linarith only [hx,root_pos]
  have hym : 0 < y+8-root := by linarith only [hy,root_lt_eight]
  have hyp : 0 < y+8+root := by linarith only [hy,root_pos]
  obtain ⟨hq,hr⟩ := F1ActualSecondFTC.normalized_logs hxm hxp hym hyp ht
  have hxq : (x+8-root)*(x+8+root)=x^2+16*x+4 := by nlinarith only [root_sq]
  have hyq : (y+8-root)*(y+8+root)=y^2+16*y+4 := by nlinarith only [root_sq]
  rw [hxq,hyq,log_div (by positivity : x^2+16*x+4 ≠ 0)
    (by positivity : y^2+16*y+4 ≠ 0)] at hq
  rw [log_div hxm.ne' hym.ne',log_div hxp.ne' hyp.ne'] at hr
  unfold quadraticPrimitive
  linear_combination (f/2)*hq+((g-8*f)/(2*root))*hr

theorem normalized_cross_ge_one (x y t d : ℝ) (hy : 0 < y) (hxy : y ≤ x)
    (hd : 0 < y+d) (he : t=(x+d)/(y+d)) (hm : 8-root ≤ d) (hp : d ≤ 8+root) :
    1 ≤ (x+8-root)/((y+8-root)*t) ∧ 1 ≤ t*(y+8+root)/(x+8+root) := by
  have hx : 0 < x := lt_of_lt_of_le hy hxy
  have hym : 0 < y+8-root := by linarith only [hy,root_lt_eight]
  have hxp : 0 < x+8+root := by linarith only [hx,root_pos]
  have ht : 0 < t := by rw [he]; exact div_pos (by linarith) hd
  constructor
  · apply (le_div_iff₀ (mul_pos hym ht)).mpr
    rw [he]
    apply (le_of_sub_nonneg ?_)
    field_simp
    have hmul := mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hm)
    nlinarith only [hmul]
  · apply (le_div_iff₀ hxp).mpr
    rw [he]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).mpr
    have hmul := mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hp)
    nlinarith only [hmul]

def bRefOne : ℝ := 4508/2927
def bRefTwo : ℝ := 4508/3981

def bOneMinus : ℝ := oneF/42+(oneG/(1127/200)-oneF/(1127/200)-9*oneF/21)/(2*root)
def bOnePlus : ℝ := oneF/42-(oneG/(1127/200)-oneF/(1127/200)-9*oneF/21)/(2*root)
def bTwoMinus : ℝ := twoF/2+(twoG/(1127/200)-twoF/(1127/200)-9*twoF)/(2*root)
def bTwoPlus : ℝ := twoF/2-(twoG/(1127/200)-twoF/(1127/200)-9*twoF)/(2*root)

def bCrossOneMinus : ℝ := (30-root)/((21*3/(1127/200)+9-root)*bRefOne)
def bCrossOnePlus : ℝ := bRefOne*(21*3/(1127/200)+9+root)/(30+root)
def bCrossTwoMinus : ℝ := (10-root)/((3/(1127/200)+9-root)*bRefTwo)
def bCrossTwoPlus : ℝ := bRefTwo*(3/(1127/200)+9+root)/(10+root)

theorem b_cross_arguments : 1 ≤ bCrossOneMinus ∧ 1 ≤ bCrossOnePlus ∧
    1 ≤ bCrossTwoMinus ∧ 1 ≤ bCrossTwoPlus := by
  have hr : 6 < root := by nlinarith only [root_sq,root_pos]
  have h1 := normalized_cross_ge_one 22 (21*3/(1127/200)+1) bRefOne 6
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [bRefOne])
    (by linarith only [hr]) (by linarith only [root_pos])
  have h2 := normalized_cross_ge_one 2 (3/(1127/200)+1) bRefTwo 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [bRefTwo])
    (by linarith only [hr]) (by linarith only [root_pos])
  convert And.intro h1.1 (And.intro h1.2 h2) using 1 <;>
    norm_num [bCrossOneMinus,bCrossOnePlus,bCrossTwoMinus,bCrossTwoPlus]

end F1BFullFTC
