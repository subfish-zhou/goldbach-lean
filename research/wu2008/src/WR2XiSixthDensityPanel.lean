import WR2XiSixthSliceMonotone
import WR2XiSixthContinuousDensity
import WR2SourceLogLower

noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
open Real Set QuarterTrim WuSource.SrcSixthGain

def sliceRatio (z : ℝ) : ℝ :=
  upperX z*(z-lowerX z)/(lowerX z*(z-upperX z))

def panelRatio (a b : ℝ) : ℝ :=
  let za := 1/2-alpha*a
  let zb := 1/2-alpha*b
  upperX zb*(zb-lowerX zb)/(lowerX za*(za-upperX za))

def densityLower (a b : ℝ) : ℝ :=
  SourceLogRational.lower (max 1 (panelRatio a b))/(b*(1-2*alpha*a))

theorem sliceRatio_one_le {z : ℝ} (hz : z ∈ Icc (alpha+beta) (1/2-2*alpha)) :
    1 ≤ sliceRatio z := by
  have hg := slice_bounds hz
  apply (one_le_div (mul_pos hg.1 hg.2.2.1)).mpr
  nlinarith [mul_nonneg hg.2.2.2.1.le (sub_nonneg.mpr hg.2.1)]

theorem panelRatio_le {a b s : ℝ} (ha : 2 ≤ a) (hb : b ≤ endpoint)
    (hs : s ∈ Icc a b) : panelRatio a b ≤ sliceRatio (1/2-alpha*s) := by
  let za := 1/2-alpha*a
  let zb := 1/2-alpha*b
  let z := 1/2-alpha*s
  have hza := slice_bounds (scalar_bounds (show a ∈ Icc 2 endpoint from ⟨ha,le_trans hs.1 (le_trans hs.2 hb)⟩))
  have hzb := slice_bounds (scalar_bounds (show b ∈ Icc 2 endpoint from ⟨le_trans ha (le_trans hs.1 hs.2),hb⟩))
  have hz := slice_bounds (scalar_bounds (show s ∈ Icc 2 endpoint from ⟨le_trans ha hs.1,le_trans hs.2 hb⟩))
  change 0 < lowerX za ∧ lowerX za ≤ upperX za ∧ 0 < za-upperX za ∧ 0 < za ∧ 0 < 1/2-za at hza
  change 0 < lowerX zb ∧ lowerX zb ≤ upperX zb ∧ 0 < zb-upperX zb ∧ 0 < zb ∧ 0 < 1/2-zb at hzb
  change 0 < lowerX z ∧ lowerX z ≤ upperX z ∧ 0 < z-upperX z ∧ 0 < z ∧ 0 < 1/2-z at hz
  have hbs : zb ≤ z := by dsimp [zb,z]; nlinarith [alpha_pos,hs.2]
  have hsa : z ≤ za := by dsimp [z,za]; nlinarith [alpha_pos,hs.1]
  have hm := slice_factors_mono hbs
  have hn := slice_factors_mono hsa
  have hnum : upperX zb*(zb-lowerX zb) ≤ upperX z*(z-lowerX z) :=
    mul_le_mul hm.1 hm.2.1 (by linarith [hzb.2.1,hzb.2.2.1]) (hz.1.trans_le hz.2.1).le
  have hden : lowerX z*(z-upperX z) ≤ lowerX za*(za-upperX za) :=
    mul_le_mul hn.2.2.1 hn.2.2.2 hz.2.2.1.le hza.1.le
  have hnon : 0 ≤ upperX zb*(zb-lowerX zb) :=
    mul_nonneg (hzb.1.trans_le hzb.2.1).le (by linarith [hzb.2.1,hzb.2.2.1])
  exact div_le_div₀ (hnon.trans hnum) hnum (mul_pos hz.1 hz.2.2.1) hden

theorem densityLower_nonneg {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hb : b ≤ endpoint) : 0 ≤ densityLower a b := by
  have hg := slice_bounds (scalar_bounds (show a ∈ Icc 2 endpoint from ⟨ha,hab.trans hb⟩))
  exact div_nonneg (SourceLogRational.lower_nonneg (le_max_left _ _))
    (mul_nonneg (by linarith) (by linarith [hg.2.2.2.1]))

theorem densityLower_le {a b s : ℝ} (ha : 2 ≤ a) (hb : b ≤ endpoint)
    (hs : s ∈ Icc a b) : densityLower a b ≤ density s := by
  have hsi : s ∈ Icc 2 endpoint := ⟨ha.trans hs.1,hs.2.trans hb⟩
  have hg := slice_bounds (scalar_bounds hsi)
  have hr : max 1 (panelRatio a b) ≤ sliceRatio (1/2-alpha*s) :=
    max_le (sliceRatio_one_le (scalar_bounds hsi)) (panelRatio_le ha hb hs)
  have hlog := (SourceLogRational.lower_le_log (le_max_left 1 (panelRatio a b))).trans
    (Real.log_le_log (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)) hr)
  have hden : s*(1-2*alpha*s) ≤ b*(1-2*alpha*a) := by
    apply mul_le_mul hs.2
    · nlinarith [alpha_pos,hs.1]
    · linarith [hg.2.2.2.1]
    · linarith [hsi.1,hs.2]
  exact div_le_div₀ ((SourceLogRational.lower_nonneg (le_max_left _ _)).trans hlog) hlog
    (mul_pos (by linarith [hsi.1]) (by linarith [hg.2.2.2.1])) hden

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.densityLower_le
