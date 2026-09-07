import MathlibNt.SieveTheory.LiLiuGoldbachB9LowPositivePrefixTransport

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

attribute [local instance] instDecidableGoldbachB9LowPositivePrefix

theorem goldbachB9LowPositivePrefixAudit_actualLow {N : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachS5LowFirstActualAtoms N eps ↔
      x.1 ∈ goldbachC10Pairs N ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)) ∧
      x.2 ∈ goldbachDifferenceCarrier N eps ∧
      literalHPoint (N * x.1.1) (x.1.1 * x.1.2) x.1.2 x.2 ∧
      (x.1.1 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ) := by
  simp only [goldbachS5LowFirstActualAtoms, mem_filter,
    mem_goldbachS5ActualAtoms_iff, goldbachC9Pairs_eq_C10Pairs,
    goldbachC9Prod, goldbachC8Prod]
  tauto

theorem goldbachB9LowPositivePrefixAudit_rightMother {N : ℕ} {eps Z : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachB9LowPositivePrefixSiftedAtoms N eps Z ↔
      x.1.1.Prime ∧ x.1.2.Prime ∧ Nat.Coprime (x.1.1 * x.1.2) N ∧
      (N : ℝ) ^ (4 / 53 : ℝ) ≤ (x.1.1 : ℝ) ∧
      (x.1.1 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) ∧
      (N : ℝ) ^ (1 / 3 : ℝ) ≤ (x.1.2 : ℝ) ∧ x.1.1 * x.1.2 ^ 2 ≤ N ∧
      x.2 ∈ range (N + 1) ∧ x.2.Prime ∧
      eps * (N : ℝ) / (x.1.1 * x.1.2 : ℕ) < (x.2 : ℝ) ∧
      (x.2 : ℝ) < (N : ℝ) / (x.1.1 * x.1.2 : ℕ) ∧
      literalHPoint N 1 Z (N - (x.1.1 * x.1.2) * x.2) ∧
      (x.1.1 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ) := by
  simp only [mem_goldbachB9LowPositivePrefixSiftedAtoms_iff,
    mem_goldbachB10SiftedAtoms_iff, mem_goldbachC10Pairs_iff,
    goldbachB10Point, goldbachC10Prod, goldbachPi10Output]
  tauto

theorem goldbachB9LowPositivePrefixAudit_retainedEpsilon {N : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} (heps : 0 < eps)
    (hx : x ∈ goldbachS5LowFirstActualAtoms N eps) :
    x.2 = (goldbachS5Switch x).1.1 * (goldbachS5Switch x).1.2 *
      (goldbachS5Switch x).2 ∧
    eps * (N : ℝ) <
      ((goldbachS5Switch x).1.1 * (goldbachS5Switch x).1.2 *
        (goldbachS5Switch x).2 : ℕ) ∧
    eps * (N : ℝ) /
      ((goldbachS5Switch x).1.1 * (goldbachS5Switch x).1.2 : ℕ) <
        ((goldbachS5Switch x).2 : ℝ) := by
  have ha := (mem_filter.mp hx).1
  exact ⟨goldbachS5ActualAtom_factorization ha,
    goldbachS5ActualAtom_retained_epsilon heps ha⟩

theorem goldbachB9LowPositivePrefixAudit_terminal
    (delta : ℝ) (hdelta : 0 < delta) (eps : ℝ)
    (heps : 0 < eps ∧ eps < (2 : ℝ) / 15) :
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ Z : ℝ,
      1 ≤ Z → Z ≤ Real.sqrt (N : ℝ) →
      (goldbachS5ClosedBelow (goldbachDifferenceCarrier N eps) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
        ((N : ℝ) ^ (1 / 10 : ℝ)) : ℝ) ≤
        ((goldbachB9LowPositivePrefixSiftedAtoms N eps Z).card : ℝ) +
        delta * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  simpa only [goldbachB9LowPositivePrefixSiftedCount, Int.cast_natCast] using
    goldbachS5ClosedBelow_le_positivePrefix_sifted_normalized delta hdelta eps heps

#check instDecidableGoldbachB9LowPositivePrefix
#print axioms instDecidableGoldbachB9LowPositivePrefix
#check goldbachS5LowFirstActualAtoms
#print axioms goldbachS5LowFirstActualAtoms
#check goldbachS5ClosedBelow_eq_card_lowActualAtoms
#print axioms goldbachS5ClosedBelow_eq_card_lowActualAtoms
#check goldbachB9LowPositivePrefixAtoms
#print axioms goldbachB9LowPositivePrefixAtoms
#check goldbachB9LowPositivePrefixSiftedAtoms
#print axioms goldbachB9LowPositivePrefixSiftedAtoms
#check goldbachB9LowPositivePrefixSiftedCount
#print axioms goldbachB9LowPositivePrefixSiftedCount
#check goldbachB9LowPositivePrefixPrimeAtoms
#print axioms goldbachB9LowPositivePrefixPrimeAtoms
#check mem_goldbachB9LowPositivePrefixAtoms_iff
#print axioms mem_goldbachB9LowPositivePrefixAtoms_iff
#check mem_goldbachB9LowPositivePrefixSiftedAtoms_iff
#print axioms mem_goldbachB9LowPositivePrefixSiftedAtoms_iff
#check goldbachB9LowPositivePrefixSiftedAtoms_eq_filter
#print axioms goldbachB9LowPositivePrefixSiftedAtoms_eq_filter
#check goldbachB9LowPositivePrefixPrimeAtoms_eq_Pi10_filter
#print axioms goldbachB9LowPositivePrefixPrimeAtoms_eq_Pi10_filter
#check goldbachB9LowPositivePrefixAtoms_product_window
#print axioms goldbachB9LowPositivePrefixAtoms_product_window
#check goldbachB9LowPositivePrefixSiftedAtoms_product_window
#print axioms goldbachB9LowPositivePrefixSiftedAtoms_product_window
#check goldbachB9LowPositivePrefixAtoms_subset_B9Plus
#print axioms goldbachB9LowPositivePrefixAtoms_subset_B9Plus
#check goldbachS5ActualAtom_retained_epsilon
#print axioms goldbachS5ActualAtom_retained_epsilon
#check goldbachS5LowFirstSwitch_preserves_pair
#print axioms goldbachS5LowFirstSwitch_preserves_pair
#check goldbachS5LowFirstSwitch_mem_positivePrimeAtoms
#print axioms goldbachS5LowFirstSwitch_mem_positivePrimeAtoms
#check goldbachS5ClosedBelow_le_positivePrefix_sifted
#print axioms goldbachS5ClosedBelow_le_positivePrefix_sifted
#check goldbachS5ClosedBelow_le_positivePrefix_sifted_normalized_of_pos
#print axioms goldbachS5ClosedBelow_le_positivePrefix_sifted_normalized_of_pos
#check goldbachS5ClosedBelow_le_positivePrefix_sifted_normalized
#print axioms goldbachS5ClosedBelow_le_positivePrefix_sifted_normalized
#check goldbachB9LowPositivePrefixAudit_actualLow
#print axioms goldbachB9LowPositivePrefixAudit_actualLow
#check goldbachB9LowPositivePrefixAudit_rightMother
#print axioms goldbachB9LowPositivePrefixAudit_rightMother
#check goldbachB9LowPositivePrefixAudit_retainedEpsilon
#print axioms goldbachB9LowPositivePrefixAudit_retainedEpsilon
#check goldbachB9LowPositivePrefixAudit_terminal
#print axioms goldbachB9LowPositivePrefixAudit_terminal

#print goldbachS5ClosedBelow
#print goldbachS5ActualAtoms
#print goldbachS5LowFirstActualAtoms
#print goldbachDifferenceCarrier
#print literalHPoint
#print SurvivesSieve
#print goldbachC10Pairs
#print goldbachB10Point
#print goldbachB10Atoms
#print goldbachB10SiftedAtoms
#print goldbachB10SiftedFiber
#print goldbachPi10Output
#print goldbachB9LowPositivePrefixAtoms
#print goldbachB9LowPositivePrefixSiftedAtoms
#print goldbachB9LowPositivePrefixSiftedCount
#print goldbachB9LowPositivePrefixPrimeAtoms
#print goldbachS5ActualAtom_retained_epsilon

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig