import WR2XiSourceContinuousFormula
import WRefinedCountBridge
import MathlibNt.Wu2004MeanValue.RefinedCounting

/-! The certified count threshold implies exact 1+1.8938 and 1+1.894 statements. -/
noncomputable section
namespace WuPaper.R2Xi.SourceContinuousCount

/-- The certified source exponent, without rounding it up to 1.894. -/
theorem one8938_of_coefficient (hc : (4491/5000 : ℝ) ≤ coefficient) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∃ p r q : ℕ, p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p + r*q ∧ r^5000 ≤ q^4469 := by
  obtain ⟨T, hT, hcount⟩ := WuTarget.RefinedExit.from_actual_count hc
    (fun _ hε => ordinary_count hε)
  refine ⟨T, hT, ?_⟩
  intro N hN hEven
  obtain ⟨p, r, q, hp, hr, hq, heq, hpow⟩ := (hcount N hN hEven).2
  exact ⟨p, r, q, hp, hr, hq, heq,
    (MathlibNt.nat_pow_le_iff_le_rpow r q 4469 5000 (by decide)).mpr hpow⟩

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

#print axioms WuPaper.R2Xi.SourceContinuousCount.one8938_of_coefficient
