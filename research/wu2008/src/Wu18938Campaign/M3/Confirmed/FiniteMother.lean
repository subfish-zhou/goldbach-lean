import MathlibNt.Wu2008DoubleSieve.TruncatedSixth
import WR2MotherTerms

noncomputable section

namespace Wu18938Campaign.M3.Confirmed

open Finset Wu2008DoubleSieve WuPaper.R2Mother
open scoped Classical

def sixthAtoms (N : ℕ) (z w u V : ℝ) : Finset ((ℕ × ℕ) × ℕ) :=
  (truncatedSixthKept N z w u V ×ˢ range N).filter
    (fun t => t.2.Prime ∧ t.1.1 * t.1.2 ∣ N - t.2 ∧
      Sifted N ((N - t.2) / (t.1.1 * t.1.2)) z)

theorem sixthAtoms_card {N : ℕ} (he : Even N) (hN : 4 ≤ N) (z w u V : ℝ) :
    ((sixthAtoms N z w u V).card : ℤ) = truncatedSixthMass N z w u V := by
  have hnprime : ¬N.Prime := by
    intro hp
    have hzero := Nat.even_iff.mp he
    have htwo := hp.eq_two_or_odd
    omega
  have hcar (d : ℕ) :
      ((range N).filter (fun p => p.Prime ∧ d ∣ N - p ∧
        Sifted N ((N - p) / d) z)) = sieveCarrier N d N z := by
    ext p
    simp only [mem_filter, mem_range, sieveCarrier]
    constructor
    · rintro ⟨hpN, hp⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hpN, hp⟩
      refine ⟨?_, hp⟩
      by_contra h
      have : p = N := by omega
      exact hnprime (this ▸ hp.1)
  simp only [sixthAtoms, card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, truncatedSixthMass, sieveCount]
  rw [Finset.sum_product]
  apply sum_congr rfl
  intro t _
  rw [← hcar]
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

def paperMother (N : ℕ) (z w u v V : ℝ) : ℤ :=
  3 * upsilon1 N z + upsilon2 N w - upsilon3 N z v - upsilon4 N z u +
    upsilon5 N z w + truncatedSixthMass N z w u V - 2 * upsilon7 N w u -
    upsilon8 N z v - upsilon9 N w u - upsilon10 N z w - upsilon11 N z w V

theorem paperMother_eq_truncated (N : ℕ) (z w u v V : ℝ) :
    paperMother N z w u v V = truncatedSixthExpression N z w u v V := by
  have he : fourModulusQuotientEleven N z w u v V = eleven N z w u v V := rfl
  have hfull : truncatedSixthFullMass N z w u = upsilon6 N z w u :=
    truncatedSixth_full_eq_original N z w u
  rw [truncatedSixthExpression, he, hfull]
  unfold paperMother eleven
  ring

def fixedPaperMother (N : ℕ) : ℤ :=
  paperMother N ((N : ℝ) ^ (100 / 1327 : ℝ)) ((N : ℝ) ^ (25 / 206 : ℝ))
    ((N : ℝ) ^ (1 / 2 - 3 * (100 / 1327 : ℝ))) ((N : ℝ) ^ (1 / 3 : ℝ))
    ((N : ℝ) ^ (1 / 2 - 2 * (100 / 1327 : ℝ)))

theorem fixedPaperMother_eq (N : ℕ) :
    fixedPaperMother N = truncatedSixthFixedExpression N := by
  exact paperMother_eq_truncated N _ _ _ _ _

theorem fixedPaperMother_actual_count {N : ℕ}
    (hN : 4 ≤ N) (he : Even N) (hz : 2 ≤ (N : ℝ) ^ (100 / 1327 : ℝ)) :
    (fixedPaperMother N : ℝ) -
        truncatedSixthErrorConstant * (N : ℝ) ^ (1 - (100 / 1327 : ℝ)) ≤
      4 * (((range (N + 1)).filter (fun p =>
        p.Prime ∧ 0 < N - p ∧ ArithmeticFunction.cardFactors (N - p) ≤ 2)).card : ℝ) := by
  have h := truncatedSixth_fixed_le_count hN he hz
  rw [← fixedPaperMother_eq] at h
  change _ ≤ 4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)
  linarith

end Wu18938Campaign.M3.Confirmed
