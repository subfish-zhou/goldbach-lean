import WR2XiSourceLowerCertificate
import WR2XiSourceSingleRational

noncomputable section
namespace WuPaper.R2Xi.SourceRational.SingleCertificate
open Real NodeExtension Finset Wu2008DoubleSieve WuSource.SrcSingle
open scoped Classical

def weightTerm : ℕ → ℝ
  | 0 => 182588049/1000000000000
  | 1 => 184875998/1000000000000
  | 2 => 153569471/1000000000000
  | 3 => 126682767/1000000000000
  | 4 => 103632329/1000000000000
  | 5 => 83935971/1000000000000
  | 6 => 67194473/1000000000000
  | 7 => 53077372/1000000000000
  | 8 => 41311988/1000000000000
  | 9 => 31644719/1000000000000
  | 10 => 23805412/1000000000000
  | 11 => 17508586/1000000000000
  | 12 => 12478158/1000000000000
  | 13 => 8447540/1000000000000
  | 14 => 5154763/1000000000000
  | 15 => 2380156/1000000000000
  | _ => 0

theorem weightTerm_paid {k : ℕ} (hk : k ∈ range 16) :
    weightTerm k ≤ SourceLogRational.lower (weightArgument k)*upperLower (14+k) := by
  have hk16 := mem_range.mp hk
  interval_cases k <;> norm_num [weightTerm, upperLower, upperNumerator, weightArgument,
    fourthGrid, truncatedSixthLowerAlpha, SourceLogRational.lower]

theorem transfer22_lower : (638785617/1000000000000 : ℝ) ≤ transferLower upperLower 22 := by
  exact lowerLower_le_transfer (j := 22) (by omega) (by omega)

theorem fourth_lower : (1098287752/1000000000000 : ℝ) ≤
    ∑ k ∈ range 16, SourceLogRational.lower (weightArgument k)*upperLower (14+k) := by
  have h := sum_le_sum (s := range 16) (fun k hk => weightTerm_paid hk)
  have he : (∑ k ∈ range 16, weightTerm k) = (1098287752/1000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, weightTerm]
  rw [he] at h
  exact h

theorem single_gain_lower : (23732/1000000 : ℝ) ≤ SourceSingle.amount := by
  have hm : (131197825/1000000000000 : ℝ) ≤
      upperLower 12*SourceLogRational.lower (40/39) := by
    norm_num [upperLower, upperNumerator, SourceLogRational.lower]
  have hs := singleLower_le_amount upperLower_nonneg
    (fun i hi hi29 => upperLower_le_extended hi hi29)
  unfold singleLower at hs
  linarith only [hs, transfer22_lower, fourth_lower, hm]

end WuPaper.R2Xi.SourceRational.SingleCertificate
#print axioms WuPaper.R2Xi.SourceRational.SingleCertificate.single_gain_lower
