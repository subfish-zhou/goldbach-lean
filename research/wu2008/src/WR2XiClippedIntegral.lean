import WR2XiRectangleLower

/-! Exact clipping of the original closed indicator intervals to a node cell. -/
noncomputable section
namespace WuPaper.R2Xi
open Set MeasureTheory Filter
open scoped Interval

def clippedIntegral (f : ℝ → ℝ) (a b l r : ℝ) : ℝ :=
  if max a l ≤ min b r then ∫ t in max a l..min b r, f t else 0

/-- Endpoint atoms vanish; disjoint pieces contribute zero instead of a reversed integral. -/
theorem indicator_integral_eq_clipped (f : ℝ → ℝ) {a b l r : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, (Icc l r).indicator f t) = clippedIntegral f a b l r := by
  rw [intervalIntegral.integral_of_le hab, setIntegral_indicator measurableSet_Icc]
  have he : (Ioc a b ∩ Icc l r : Set ℝ) =ᵐ[volume] (Ioc a b ∩ Ioc l r : Set ℝ) :=
    (ae_eq_refl (Ioc a b)).inter Ioc_ae_eq_Icc.symm
  rw [setIntegral_congr_set he]
  have hset : Ioc a b ∩ Ioc l r = Ioc (max a l) (min b r) := by
    ext t
    simp only [mem_inter_iff, mem_Ioc, max_lt_iff, le_min_iff]
    tauto
  rw [hset]
  unfold clippedIntegral
  split_ifs with h
  · exact (intervalIntegral.integral_of_le h).symm
  · rw [Ioc_eq_empty (not_lt_of_ge (le_of_not_ge h)), setIntegral_empty]

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.indicator_integral_eq_clipped
