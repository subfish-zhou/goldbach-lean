import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9LongRectangle

noncomputable section
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- A positive rectangular majorant for the entire actual labelled mother set.
No subtraction of a principal term or signed-error inequality is asserted. -/
theorem fouvryG9_positive_rectangle_cover (N : ℕ) (e : ℝ) {ρ : ℝ}
    (hρ : 1 < ρ) (F : ℕ → ℕ → ℝ) (hF : ∀ n m, 0 ≤ F n m) :
    (∑ a ∈ goldbachB9LowPositivePrefixAtoms N e, F a.1.1 (a.1.2*a.2)) ≤
      ∑ k ∈ fouvryG9GridUsed N e ρ, ∑ n ∈ fouvryG9LongShortLabels N ρ k,
        ∑ m ∈ fouvryG9LongProducts N ρ k, fouvryG9LongAlpha N ρ k m * F n m := by
  rw [fouvryG9_sum_reindex, ← fouvryG9GridCell_sum N e ρ]
  exact sum_le_sum (fun k _ => fouvryG9Long_cell_le_weighted_rectangle hρ k F hF)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
