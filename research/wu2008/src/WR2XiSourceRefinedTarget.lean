import WR2XiSourceContinuousFormula
import WRefinedCountBridge
import MathlibNt.Wu2004MeanValue.RefinedCounting

/-! The remaining numerical count threshold implies the exact 1+1.894 statement. -/
noncomputable section
namespace WuPaper.R2Xi.SourceContinuousCount

/-- The sole premise here is quantitative; the final integral enclosure remains to be supplied. -/
theorem one894_of_coefficient (hc : (4491/5000 : ℝ) ≤ coefficient) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∃ p r q : ℕ, p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p + r*q ∧ r^500 ≤ q^447 := by
  obtain ⟨T, hT, hcount⟩ := WuTarget.RefinedExit.from_actual_count hc
    (fun _ hε => ordinary_count hε)
  refine ⟨T, hT, ?_⟩
  intro N hN hEven
  have hM : 0 < U8CanonicalMother.M N :=
    Wu2008DoubleSieve.HighSixPhase6.original_scale_positive (hT.trans hN)
  have hpos : 0 < ((Wu2004MeanValue.refinedGood N (9469/5000)).card : ℝ) :=
    (mul_pos (half_pos WuTarget.RefinedExit.margin_pos) hM).trans_le (hcount N hN hEven).1
  exact Wu2004MeanValue.exists_one894_of_source_count_pos (by exact_mod_cast hpos)

end WuPaper.R2Xi.SourceContinuousCount
#print axioms WuPaper.R2Xi.SourceContinuousCount.one894_of_coefficient
