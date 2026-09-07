import MathlibNt.SieveTheory.LiLiuGoldbachG11RoughSandwich

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11_audit_canonical (N : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    (∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)),
        goldbachG11RoughCount N ε v) ≤
      goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)) ∧
    goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)) ≤
      (∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)),
        goldbachG11RoughCount N ε v) +
      (∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)),
        goldbachG11RSquareCount (goldbachDifferenceCarrier N ε) v) +
      (∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)),
        goldbachG11NCount (goldbachDifferenceCarrier N ε) N v) :=
  goldbachWeightG11_roughQuotient_sandwich N ε _ _ hε

theorem goldbachG11_audit_epsilon_zero (N : ℕ) (z b : ℝ) :
    (∑ v ∈ goldbachG11Labels N z b, goldbachG11RoughCount N 0 v) ≤
        goldbachWeightG11 (goldbachDifferenceCarrier N 0) N z b ∧
      goldbachWeightG11 (goldbachDifferenceCarrier N 0) N z b ≤
        (∑ v ∈ goldbachG11Labels N z b, goldbachG11RoughCount N 0 v) +
          (∑ v ∈ goldbachG11Labels N z b,
            goldbachG11RSquareCount (goldbachDifferenceCarrier N 0) v) +
          (∑ v ∈ goldbachG11Labels N z b,
            goldbachG11NCount (goldbachDifferenceCarrier N 0) N v) :=
  goldbachWeightG11_roughQuotient_sandwich N 0 z b le_rfl

theorem goldbachG11_audit_difference_ne_zero {N n : ℕ}
    (hn : n ∈ goldbachDifferenceCarrier N 0) : n ≠ 0 := by
  have h := (goldbachG11_difference_data le_rfl hn).1
  omega

theorem goldbachG11_audit_cofactor_one {N p : ℕ} {ε : ℝ} {v : GoldbachG11Label} :
    (p, 1) ∈ goldbachG11RoughPairs N ε v ↔
      p.Prime ∧ (p : ℝ) < (1 - ε) * N ∧ p + goldbachG11LabelProd v = N := by
  rw [mem_goldbachG11RoughPairs_iff]
  constructor
  · rintro ⟨_, _, _, hp, hcut, heq, _⟩
    exact ⟨hp, hcut, by simpa using heq⟩
  · rintro ⟨hp, hcut, heq⟩
    refine ⟨by omega, le_rfl, ?_, hp, hcut, by simpa using heq, ?_⟩
    · have := hp.two_le
      omega
    · exact (goldbachG11_survives_one_iff _ _).mp (goldbachG11_survives_one _)

theorem goldbachG11_audit_first_diagonal (N r s t : ℕ) (z b : ℝ) :
    (⟨t, s, r, r⟩ : GoldbachG11Label) ∈ goldbachG11Labels N z b ↔
      r.Prime ∧ s.Prime ∧ t.Prime ∧ Nat.Coprime (r * r * s * t) N ∧
        z ≤ (r : ℝ) ∧ r ≤ s ∧ s ≤ t ∧ (t : ℝ) ≤ b := by
  simp [mem_goldbachG11Labels_iff]

theorem goldbachG11_audit_middle_diagonal (N r s t : ℕ) (z b : ℝ) :
    (⟨t, s, r, s⟩ : GoldbachG11Label) ∈ goldbachG11Labels N z b ↔
      r.Prime ∧ s.Prime ∧ t.Prime ∧ Nat.Coprime (r * s * s * t) N ∧
        z ≤ (r : ℝ) ∧ r ≤ s ∧ s ≤ t ∧ (t : ℝ) ≤ b := by
  simp [mem_goldbachG11Labels_iff]

theorem goldbachG11_audit_last_diagonal (N r q s : ℕ) (z b : ℝ) :
    (⟨s, s, r, q⟩ : GoldbachG11Label) ∈ goldbachG11Labels N z b ↔
      r.Prime ∧ q.Prime ∧ s.Prime ∧ Nat.Coprime (r * q * s * s) N ∧
        z ≤ (r : ℝ) ∧ r ≤ q ∧ q ≤ s ∧ (s : ℝ) ≤ b := by
  simp [mem_goldbachG11Labels_iff]

theorem goldbachG11_audit_first_diagonal_exception (A : Finset ℕ) (r s t : ℕ) :
    goldbachG11RSquareException A ⟨t, s, r, r⟩ = ∅ := by
  classical
  simp [goldbachG11RSquareException]

#print goldbachWeightG11
#print goldbachDifferenceCarrier
#print goldbachPrimeCarrier
#print literalH
#print literalHPoint
#print SurvivesSieve
#print goldbachG11Labels
#print goldbachG11LabelProd
#print goldbachG11QuotientPairs
#print goldbachG11RoughPairs
#print goldbachG11RoughCount
#print goldbachG11RSquareException
#print goldbachG11NException
#print goldbachG11RSquareCount
#print goldbachG11NCount
#print goldbachG11QuotientEquiv

#check GoldbachG11Label
#print axioms GoldbachG11Label
#check goldbachG11Labels
#print axioms goldbachG11Labels
#check goldbachG11LabelProd
#print axioms goldbachG11LabelProd
#check goldbachG11Labels_sum
#print axioms goldbachG11Labels_sum
#check goldbachWeightG11_eq_label_sum
#print axioms goldbachWeightG11_eq_label_sum
#check mem_goldbachG11Labels_iff
#print axioms mem_goldbachG11Labels_iff
#check goldbachG11LabelProd_pos
#print axioms goldbachG11LabelProd_pos
#check goldbachG11_survives_one_iff
#print axioms goldbachG11_survives_one_iff
#check goldbachG11_survives_one
#print axioms goldbachG11_survives_one
#check goldbachG11QuotientPairs
#print axioms goldbachG11QuotientPairs
#check goldbachG11RoughPairs
#print axioms goldbachG11RoughPairs
#check goldbachG11RoughCount
#print axioms goldbachG11RoughCount
#check mem_goldbachG11QuotientPairs_iff
#print axioms mem_goldbachG11QuotientPairs_iff
#check mem_goldbachG11RoughPairs_iff
#print axioms mem_goldbachG11RoughPairs_iff
#check goldbachG11_difference_data
#print axioms goldbachG11_difference_data
#check goldbachG11_quotient_forward
#print axioms goldbachG11_quotient_forward
#check goldbachG11_quotient_backward
#print axioms goldbachG11_quotient_backward
#check goldbachG11_quotient_cast
#print axioms goldbachG11_quotient_cast
#check goldbachG11QuotientEquiv
#print axioms goldbachG11QuotientEquiv
#check goldbachG11RoughCount_eq_filter
#print axioms goldbachG11RoughCount_eq_filter
#check goldbachG11RSquareException
#print axioms goldbachG11RSquareException
#check goldbachG11NException
#print axioms goldbachG11NException
#check goldbachG11RSquareCount
#print axioms goldbachG11RSquareCount
#check goldbachG11NCount
#print axioms goldbachG11NCount
#check goldbachG11_rough_mul_survives
#print axioms goldbachG11_rough_mul_survives
#check goldbachG11_survives_or_exceptions
#print axioms goldbachG11_survives_or_exceptions
#check goldbachG11_cell_sandwich
#print axioms goldbachG11_cell_sandwich
#check goldbachWeightG11_roughQuotient_sandwich
#print axioms goldbachWeightG11_roughQuotient_sandwich
#check goldbachG11_audit_canonical
#print axioms goldbachG11_audit_canonical
#check goldbachG11_audit_epsilon_zero
#print axioms goldbachG11_audit_epsilon_zero
#check goldbachG11_audit_difference_ne_zero
#print axioms goldbachG11_audit_difference_ne_zero
#check goldbachG11_audit_cofactor_one
#print axioms goldbachG11_audit_cofactor_one
#check goldbachG11_audit_first_diagonal
#print axioms goldbachG11_audit_first_diagonal
#check goldbachG11_audit_middle_diagonal
#print axioms goldbachG11_audit_middle_diagonal
#check goldbachG11_audit_last_diagonal
#print axioms goldbachG11_audit_last_diagonal
#check goldbachG11_audit_first_diagonal_exception
#print axioms goldbachG11_audit_first_diagonal_exception

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig