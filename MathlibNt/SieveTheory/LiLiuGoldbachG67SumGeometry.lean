import MathlibNt.SieveTheory.LiLiuGoldbachG67ElementaryIntegralBridge

open Set MeasureTheory
open scoped Interval
noncomputable section
namespace G67SumCoordinate

/-- Lower endpoint of the sum-coordinate fiber. -/
def lower (a d s : ℝ) : ℝ := max a (s-d)
/-- Upper endpoint of the sum-coordinate fiber. -/
def upper (b c s : ℝ) : ℝ := min b (s-c)

/-- The fiber is a nonempty positive interval throughout the sum range. -/
theorem fiber_bounds {a b c d s : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hab : a ≤ b) (hcd : c ≤ d) (hs : s ∈ Icc (a+c) (b+d)) :
    0 < lower a d s ∧ lower a d s ≤ upper b c s ∧ 0 < s-upper b c s := by
  dsimp [lower, upper]
  refine ⟨lt_of_lt_of_le ha (le_max_left _ _), ?_, ?_⟩
  · apply max_le
    · exact le_min hab (by linarith [hs.1])
    · exact le_min (by linarith [hs.2]) (by linarith)
  · have := min_le_right b (s-c)
    linarith

/-- Exact closed-domain equivalence; no coordinate substitution is assumed. -/
theorem fiber_mem {a b c d s u : ℝ} :
    u ∈ Icc (lower a d s) (upper b c s) ↔
      u ∈ Icc a b ∧ s-u ∈ Icc c d := by
  simp only [mem_Icc, lower, upper, max_le_iff, le_min_iff]
  constructor <;> rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩ <;> constructor <;> constructor <;> linarith

end G67SumCoordinate
