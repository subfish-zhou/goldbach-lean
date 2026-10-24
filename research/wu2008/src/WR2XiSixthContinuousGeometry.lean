import WSrcSixthGainReduction
import W01ContinuousIntegral

noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
open Real Set MeasureTheory QuarterTrim WuTarget.W01Continuous
open WuSource.SrcSixthGain WuTarget.Wu08FifthSource
open scoped Classical

def lowerX (z : ℝ) : ℝ := max alpha (z-1/4)

theorem sum_region_iff (z x : ℝ) :
    (x,z-x) ∈ StaircaseShrink.domain 0 ↔
      z ∈ Icc (alpha+beta) (1/2-2*alpha) ∧ x ∈ Icc (lowerX z) (upperX z) := by
  rw [StaircaseShrink.domain_iff]
  simp only [lowerX, upperX, mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨ha,hb,hc,hd,he⟩
    constructor <;> constructor <;> first | constructor <;> linarith | linarith
  · rintro ⟨⟨hz0,hz1⟩,⟨⟨hx,hxq⟩,hxb,hxz⟩⟩
    refine ⟨hx,hxb,?_,?_,?_⟩ <;> linarith

theorem slice_bounds {z : ℝ} (hz : z ∈ Icc (alpha+beta) (1/2-2*alpha)) :
    0 < lowerX z ∧ lowerX z ≤ upperX z ∧ 0 < z-upperX z ∧
      0 < z ∧ 0 < 1/2-z := by
  have hb : 0 < beta := StaircaseShrink.fixed_bounds.1
  have hab : alpha ≤ beta := StaircaseShrink.fixed_bounds.2.1.le
  have hbq : beta ≤ (1/4:ℝ) := by norm_num [beta]
  have hzq : z-1/4 ≤ beta := by
    have hnum : (1/2:ℝ)-2*alpha-1/4 ≤ beta := by norm_num [alpha,beta]
    linarith [hz.2]
  have hlow : lowerX z ≤ upperX z := by
    unfold lowerX upperX
    exact max_le (le_min hab (by linarith [hz.1]))
      (le_min hzq (by linarith))
  have hu : upperX z ≤ z-beta := min_le_right _ _
  exact ⟨alpha_pos.trans_le (le_max_left _ _),hlow,by linarith,
    by linarith [hz.1,alpha_pos],by linarith [hz.2,alpha_pos]⟩

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.sum_region_iff
#print axioms WuPaper.R2Xi.SixthContinuous.slice_bounds
