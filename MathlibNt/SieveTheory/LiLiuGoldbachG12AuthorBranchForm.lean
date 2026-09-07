import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorLowHigh

noncomputable section
open Classical Finset
open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The author's rational low branch on every literal low-mother atom. -/
theorem goldbachG12AuthorPrimeWeight_eq_low_mother {N : ℕ} (hN : 4 ≤ N)
    {ε : ℝ} {p : ℕ × ℕ} (hp : p ∈ G12FlexibleRectangle.mother N ε) :
    goldbachG12AuthorPrimeWeight N p.2 = 36/(5*(1-Real.log (p.2 : ℝ)/Real.log N)) := by
  obtain ⟨_,hr,_,_,hcut⟩ := (G12LowRectangle.mother_linked_iff N p.1 p.2 ε).mp hp
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrp : (0 : ℝ) < p.2 := by exact_mod_cast (mem_filter.mp hr).2.1.pos
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  apply goldbachG11AuthorWeight_eq_low
  apply (div_le_iff₀ hl).mpr
  have h := Real.log_le_log hrp hcut.le
  rw [Real.log_rpow hNp] at h
  exact h

/-- Expanded finite mother mass; no output-primality predicate was inserted. -/
theorem goldbachG12AuthorLowMotherMass_eq_rational {N : ℕ} (hN : 4 ≤ N) (ε : ℝ) :
    goldbachG12AuthorLowMotherMass N ε =
      ∑ p ∈ G12FlexibleRectangle.mother N ε, goldbachG12NormalizedCoefficient N p.1*
        (36/(5*(1-Real.log (p.2 : ℝ)/Real.log N))) := by
  apply sum_congr rfl
  intro p hp
  rw [goldbachG12AuthorPrimeWeight_eq_low_mother hN hp]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
