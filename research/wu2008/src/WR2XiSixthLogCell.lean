import WR2XiSixthContinuousReduction
import WR2SourceLogLower

noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
open Real Set MeasureTheory NodeExtension
open scoped Classical Interval

/-- Exact logarithmic mass of a clipped original profile cell. -/
theorem indicator_reciprocal_integral {a b c R q : ℝ}
    (ha : 0 < a) (hb : b ≤ R) (hc : c ≤ R) :
    (∫ t in c..R, (Ioc a b).indicator (fun t => q/t) t) =
      if max a c ≤ b then q*log (b/max a c) else 0 := by
  have hs : Ioc a b ∩ Ioc c R = Ioc (max a c) b := by
    ext t
    simp only [mem_inter_iff,mem_Ioc,max_lt_iff]
    constructor
    · rintro ⟨⟨ht1,ht2⟩,ht3,ht4⟩
      exact ⟨⟨ht1,ht3⟩,ht2⟩
    · rintro ⟨⟨ht1,ht2⟩,ht3⟩
      exact ⟨⟨ht1,ht3⟩,ht2,ht3.trans hb⟩
  rw [intervalIntegral.integral_of_le hc,MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,hs]
  split_ifs with hab
  · rw [← intervalIntegral.integral_of_le hab]
    have hm : 0 < max a c := ha.trans_le (le_max_left _ _)
    have he : (fun t : ℝ => q/t) = fun t => q*(1/t) := by funext t; ring
    rw [he,intervalIntegral.integral_const_mul, integral_one_div_of_pos hm (hm.trans_le hab)]
  · rw [Ioc_eq_empty_of_le (le_of_not_ge hab)]
    simp

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.indicator_reciprocal_integral
