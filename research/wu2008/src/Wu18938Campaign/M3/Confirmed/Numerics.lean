import Mathlib.Tactic

/-!
Exact arithmetic in the parent-accepted original numerical ledger.

These lemmas certify arithmetic, not the analytic inequalities supplying the
paper's coefficients. In particular, they do not assert the sixth-term count
bound or an unconditional Goldbach theorem.
-/

noncomputable section

namespace Wu18938Campaign.M3.Confirmed

/-- Rational lower expression obtained from the two cited table entries and
`log (40 / 39) > 1 / 40`. The analytic premise is established separately. -/
def correctedG2 : ℝ :=
  8 * (6440 / 10000000 + 52233 / (40 * 10000000))

theorem correctedG2_exact : correctedG2 = (309833 : ℝ) / 50000000 := by
  norm_num [correctedG2]

/-- The original signed scalar ledger, with the same-domain fourfold upper
bound and the corrected second-term lower expression. -/
def originalNumericLedger : ℝ :=
  (3 * (14900897 / 1000000) + 9103015 / 1000000 -
    23652925 / 1000000 - 19643510 / 1000000 +
    1654808 / 1000000 + 3819092 / 1000000 -
    2 * (585179 / 1000000) - 5279581 / 1000000 -
    5372410 / 1000000 - 851 / 1250 + correctedG2 +
    39890 / 1000000 + 8860 / 1000000 +
    1359 / 1000000 + 60469 / 1000000) / 4

theorem originalNumericLedger_exact :
    originalNumericLedger = (179839833 : ℝ) / 200000000 := by
  norm_num [originalNumericLedger, correctedG2]

theorem originalNumericLedger_margin :
    originalNumericLedger - (899 : ℝ) / 1000 = 39833 / 200000000 := by
  rw [originalNumericLedger_exact]
  norm_num

theorem originalNumericLedger_gt :
    (899 : ℝ) / 1000 < originalNumericLedger := by
  rw [originalNumericLedger_exact]
  norm_num

/-- The required sixth-slot numerical contribution, not a count estimate. -/
theorem sixth_scalar_sum :
    (3819092 : ℝ) / 1000000 + 60469 / 1000000 = 3879561 / 1000000 := by
  norm_num

end Wu18938Campaign.M3.Confirmed

#check @Wu18938Campaign.M3.Confirmed.originalNumericLedger_gt
#print axioms Wu18938Campaign.M3.Confirmed.correctedG2_exact
#print axioms Wu18938Campaign.M3.Confirmed.originalNumericLedger_exact
#print axioms Wu18938Campaign.M3.Confirmed.originalNumericLedger_margin
#print axioms Wu18938Campaign.M3.Confirmed.originalNumericLedger_gt
#print axioms Wu18938Campaign.M3.Confirmed.sixth_scalar_sum
