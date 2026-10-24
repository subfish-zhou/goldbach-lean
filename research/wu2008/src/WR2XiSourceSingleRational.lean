import WR2XiSourceTransferRational
import WR2XiSourceSingle

noncomputable section
namespace WuPaper.R2Xi.SourceRational
open Real NodeExtension Finset Wu2008DoubleSieve WuSource.SrcSingle
open scoped Classical

def weightArgument (k : ℕ) : ℝ :=
  fourthGrid (k+1)*(1-2*truncatedSixthLowerAlpha*fourthGrid k)/
    (fourthGrid k*(1-2*truncatedSixthLowerAlpha*fourthGrid (k+1)))

theorem weightArgument_ge_one {k : ℕ} (hk : k < 16) : 1 ≤ weightArgument k := by
  interval_cases k <;> norm_num [weightArgument, fourthGrid, truncatedSixthLowerAlpha]

def singleLower (q : ℕ → ℝ) : ℝ :=
  8*(transferLower q 22+q 12*SourceLogRational.lower (40/39))+
    16*∑ k ∈ range 16, SourceLogRational.lower (weightArgument k)*q (14+k)

theorem singleLower_le_amount {q : ℕ → ℝ} (hq0 : ∀ i, 0 ≤ q i)
    (hq : ∀ i, 2 ≤ i → i ≤ 29 → q i ≤ extendedNode RationalCandidate.lowerH i) :
    singleLower q ≤ SourceSingle.amount := by
  have ht := transferLower_le_original hq0 hq (j := 22) (by omega)
  have hl := mul_le_mul (hq 12 (by omega) (by omega))
    (SourceLogRational.lower_le_log (by norm_num : (1:ℝ) ≤ 40/39))
    (SourceLogRational.lower_nonneg (by norm_num : (1:ℝ) ≤ 40/39))
    ((hq0 12).trans (hq 12 (by omega) (by omega)))
  have hs : (∑ k ∈ range 16, SourceLogRational.lower (weightArgument k)*q (14+k)) ≤
      ∑ k ∈ range 16, sourceWeight (fourthGrid k) (fourthGrid (k+1))*
        extendedNode RationalCandidate.lowerH (14+k) := by
    apply sum_le_sum
    intro k hk
    have hk16 := mem_range.mp hk
    have harg := weightArgument_ge_one hk16
    have hw := SourceLogRational.lower_le_log harg
    have hw0 := SourceLogRational.lower_nonneg harg
    exact mul_le_mul hw (hq (14+k) (by omega) (by omega)) (hq0 (14+k)) (hw0.trans hw)
  unfold singleLower SourceSingle.amount secondNodeGain fourthNodeSum CandidateGrid.upper CandidateGrid.lower
  linarith only [ht,hl,hs]

end WuPaper.R2Xi.SourceRational
#print axioms WuPaper.R2Xi.SourceRational.singleLower_le_amount
