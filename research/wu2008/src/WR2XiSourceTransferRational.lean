import WR2XiCandidateGrid
import WR2SourceLogLower

noncomputable section
namespace WuPaper.R2Xi.SourceRational
open Real NodeExtension Finset
open scoped Classical

/-- Rational logarithm weights preserve the original finite transfer formula. -/
def transferLower (q : ℕ → ℝ) (j : ℕ) : ℝ :=
  RationalCandidate.lowerH 0*SourceLogRational.lower
    (rNode (max 2 (j-10))/(rNode j-1))+
    ∑ i ∈ Icc (max 3 (j-9)) 29,
      q i*SourceLogRational.lower (rNode i/rNode (i-1))

theorem transferLower_le_original {q : ℕ → ℝ}
    (hq0 : ∀ i, 0 ≤ q i)
    (hq : ∀ i, 2 ≤ i → i ≤ 29 → q i ≤ extendedNode RationalCandidate.lowerH i)
    {j : ℕ} (hj : j ≤ 29) :
    transferLower q j ≤ originalTransfer RationalCandidate.lowerH j := by
  have hs := WuSource.SrcGrid.start_bounds_all hj
  have hr : 1 ≤ rNode (max 2 (j-10))/(rNode j-1) := by
    apply (one_le_div (by linarith [hs.2.2.1])).mpr
    exact hs.2.2.2
  unfold transferLower originalTransfer
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (SourceLogRational.lower_le_log hr)
      (RationalCandidate.lowerH_nonneg 0)
  · apply sum_le_sum
    intro i hi
    have hib := mem_Icc.mp hi
    have hi2 : 2 ≤ i := by have := le_max_left 3 (j-9); omega
    have hratio : 1 ≤ rNode i/rNode (i-1) :=
      (one_le_div (rNode_pos _)).mpr (rNode_mono (by omega))
    exact mul_le_mul (hq i hi2 hib.2) (SourceLogRational.lower_le_log hratio)
      (SourceLogRational.lower_nonneg hratio) ((hq0 i).trans (hq i hi2 hib.2))

theorem transferLower_nonneg {q : ℕ → ℝ} (hq0 : ∀ i, 0 ≤ q i)
    {j : ℕ} (hj : j ≤ 29) : 0 ≤ transferLower q j := by
  have hs := WuSource.SrcGrid.start_bounds_all hj
  have hr : 1 ≤ rNode (max 2 (j-10))/(rNode j-1) :=
    (one_le_div (by linarith [hs.2.2.1])).mpr hs.2.2.2
  apply add_nonneg
  · exact mul_nonneg (RationalCandidate.lowerH_nonneg 0) (SourceLogRational.lower_nonneg hr)
  · apply sum_nonneg
    intro i _
    exact mul_nonneg (hq0 i) (SourceLogRational.lower_nonneg
      ((one_le_div (rNode_pos _)).mpr (rNode_mono (by omega))))

end WuPaper.R2Xi.SourceRational
#print axioms WuPaper.R2Xi.SourceRational.transferLower_le_original
