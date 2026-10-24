import WR2XiSourceNode11
import WR2XiSourceNode12
import WR2XiSourceNode13
import WR2XiSourceNode14
import WR2XiSourceNode15
import WR2XiSourceNode16
import WR2XiSourceNode17
import WR2XiSourceNode18
import WR2XiSourceNode19
import WR2XiSourceNode20
import WR2XiSourceNode21
import WR2XiSourceNode22
import WR2XiSourceNode23
import WR2XiSourceNode24
import WR2XiSourceNode25
import WR2XiSourceNode26
import WR2XiSourceNode27
import WR2XiSourceNode28
import WR2XiSourceNode29

noncomputable section
namespace WuPaper.R2Xi.SourceRational
open NodeExtension

/-- Rounded rational bounds for every extended upper node used by the source ledger. -/
def upperNumerator : ℕ → ℕ
  | 11 => 61150104
  | 12 => 51820373
  | 13 => 43726568
  | 14 => 36703695
  | 15 => 30615051
  | 16 => 25346254
  | 17 => 20800762
  | 18 => 16896457
  | 19 => 13563001
  | 20 => 10739764
  | 21 => 8374182
  | 22 => 6420445
  | 23 => 4833811
  | 24 => 3565810
  | 25 => 2565457
  | 26 => 1783875
  | 27 => 1174988
  | 28 => 695497
  | 29 => 310497
  | _ => 0

def upperLower (i : ℕ) : ℝ :=
  if h : 2 ≤ i ∧ i ≤ 10 then RationalCandidate.lowerH ⟨i-2, by omega⟩
  else (upperNumerator i:ℝ)/10000000000

theorem upperLower_nonneg (i : ℕ) : 0 ≤ upperLower i := by
  unfold upperLower
  split_ifs
  · exact RationalCandidate.lowerH_nonneg _
  · positivity

theorem upperLower_le_extended {i : ℕ} (hi : 2 ≤ i) (hi29 : i ≤ 29) :
    upperLower i ≤ extendedNode RationalCandidate.lowerH i := by
  by_cases h10 : i ≤ 10
  · simp [upperLower, extendedNode, hi, h10]
  · have h11 : 11 ≤ i := by omega
    interval_cases i
    · exact Node11.upper_lower
    · exact Node12.upper_lower
    · exact Node13.upper_lower
    · exact Node14.upper_lower
    · exact Node15.upper_lower
    · exact Node16.upper_lower
    · exact Node17.upper_lower
    · exact Node18.upper_lower
    · exact Node19.upper_lower
    · exact Node20.upper_lower
    · exact Node21.upper_lower
    · exact Node22.upper_lower
    · exact Node23.upper_lower
    · exact Node24.upper_lower
    · exact Node25.upper_lower
    · exact Node26.upper_lower
    · exact Node27.upper_lower
    · exact Node28.upper_lower
    · exact Node29.upper_lower

end WuPaper.R2Xi.SourceRational
#print axioms WuPaper.R2Xi.SourceRational.upperLower_le_extended
