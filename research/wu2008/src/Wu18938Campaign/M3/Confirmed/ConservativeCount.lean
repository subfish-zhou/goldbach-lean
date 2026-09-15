import Wu18938Campaign.M3.Confirmed.Refinement
import Wu18938Campaign.M3.Confirmed.Numerics

noncomputable section

namespace Wu18938Campaign.M3.Confirmed

open Wu2008DoubleSieve Wu2004MeanValue MathlibNt.Wu2008DoubleSieve

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

theorem refined_1894_from_conservative_count
    (hcount : ∀ ε : ℝ, 0 < ε →
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (conservativeLedger - ε) * truncatedSixthMassScale N ≤
          ((wuPrimeComplements N).card : ℝ)) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      truncatedSixthMassScale N / 400 <
        ((refinedGood N (947 / 500)).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ (447 / 500 : ℝ) := by
  apply refined_1894_from_ordinary_count
  intro ε heps
  obtain ⟨T, hT, hc⟩ := hcount ε heps
  refine ⟨T, hT, fun N hN he => ?_⟩
  have hcoef : (899 / 1000 : ℝ) ≤ conservativeLedger := by
    rw [conservativeLedger_exact]
    norm_num
  have hscale : 0 ≤ truncatedSixthMassScale N := by
    have hpos := wuSingularSeries_pos N (by omega)
    unfold truncatedSixthMassScale
    positivity
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hcoef ε) hscale).trans (hc N hN he)

end Wu18938Campaign.M3.Confirmed
