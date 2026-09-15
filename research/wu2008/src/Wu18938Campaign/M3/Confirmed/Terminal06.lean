import Wu18938Campaign.M3.Confirmed.Ledger
import Wu18938Campaign.M3.Confirmed.Refinement
import WSrcFourEnclosureFine

noncomputable section

namespace Wu18938Campaign.M3.Confirmed

open Wu2008DoubleSieve Wu08TerminalAlignment Wu08OriginalFourWeights
open MathlibNt.Wu2008DoubleSieve

def conservativeLedger : ℝ :=
  originalNumericLedger + (3 / 50 - 60469 / 1000000) / 4

theorem conservativeLedger_exact :
    conservativeLedger = (179816383 / 200000000 : ℝ) := by
  rw [conservativeLedger, originalNumericLedger_exact]
  norm_num

theorem conservativeLedger_margin :
    conservativeLedger - (899 / 1000 : ℝ) = 16383 / 200000000 := by
  rw [conservativeLedger_exact]
  norm_num

theorem conservative_sixth_scalar :
    (3819092 / 1000000 : ℝ) + 3 / 50 = 3879092 / 1000000 := by norm_num

theorem original_functions_sixth06 {δ G3 G4 G5 G6 : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hh42 : (6440 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (21 / 5))
    (hH32 : (52233 / 10000000 : ℝ) ≤ wuImprovementLimit true δ (16 / 5))
    (hC1 : (14900897 / 1000000 : ℝ) ≤ firstMain)
    (hC2 : (9103015 / 1000000 : ℝ) ≤ secondMain)
    (hC3 : thirdMain ≤ (23652925 / 1000000 : ℝ))
    (hC4 : fourthMain ≤ (19643510 / 1000000 : ℝ))
    (hC5 : (1654808 / 1000000 : ℝ) ≤ fifthMain)
    (hC6 : (3819092 / 1000000 : ℝ) ≤ sixthMain)
    (hC7 : seventhMain ≤ (585179 / 1000000 : ℝ))
    (hC8 : eighthMain ≤ (5279581 / 1000000 : ℝ))
    (hC9 : ninthMain ≤ (5372410 / 1000000 : ℝ))
    (hG3 : (39890 / 1000000 : ℝ) ≤ G3)
    (hG4 : (8860 / 1000000 : ℝ) ≤ G4)
    (hG5 : (1359 / 1000000 : ℝ) ≤ G5)
    (hG6 : (3 / 50 : ℝ) ≤ G6) :
    conservativeLedger < signedOriginalFunctions δ G3 G4 G5 G6 := by
  have h := (signed_original_functions_lower hd hh hh42 hH32
    WuSource.SrcFourEnclosure.original_pair_upper hC1 hC2 hC3 hC4 hC5 hC6
    hC7 hC8 hC9 hG3 hG4 hG5
    (show (60469 / 1000000 : ℝ) ≤ G6 + 469 / 1000000 by linarith)).1
  unfold conservativeLedger signedOriginalFunctions at *
  linarith only [h]

theorem refined_1894_from_conservative_count
    (hcount : ∀ ε : ℝ, 0 < ε →
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (conservativeLedger - ε) * truncatedSixthMassScale N ≤
          ((wuPrimeComplements N).card : ℝ)) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      truncatedSixthMassScale N / 400 <
        ((Wu2004MeanValue.refinedGood N (947 / 500)).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ (447 / 500 : ℝ) := by
  apply refined_1894_from_ordinary_count
  intro ε heps
  obtain ⟨T, hT, hc⟩ := hcount ε heps
  refine ⟨T, hT, fun N hN he => ?_⟩
  have hcoef : (899 / 1000 : ℝ) ≤ conservativeLedger := by
    rw [conservativeLedger_exact]
    norm_num
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hcoef ε)
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (hc N hN he)

end Wu18938Campaign.M3.Confirmed
