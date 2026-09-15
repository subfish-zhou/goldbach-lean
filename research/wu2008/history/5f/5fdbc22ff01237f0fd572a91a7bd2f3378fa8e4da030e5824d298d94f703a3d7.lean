import MathlibNt.Wu2008DoubleSieve.SourceCarriers
import MathlibNt.Wu2008DoubleSieve.ConvolutionWuBoxes
import MathlibNt.SieveTheory.LinearSieve.UpperRosserDensity

/-!
# Actual signed Rosser sieve remainders on Wu's convolution sequences

The sequence is the unscaled divisible subsequence of `{N-p : p<=N}`.
Its further divisible count is identified with the literal prime-AP count.
The weights below are the frozen upper/lower Rosser coefficients, not
supplied functions satisfying an assumed remainder estimate.

This realizes the finite ordinary-AP consumer in Wu04 (3.11)--(3.13) for
canonical Rosser weights. It does not construct the source's well-factorable
decomposition into `lambda_l`, nor any switched distribution estimate.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.LinearSieve

noncomputable def goldbachDivisible (N d : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun p => p.Prime ∧ d ∣ N - p)

noncomputable def sourceSequenceCount (N d q : ℕ) : ℕ :=
  ((goldbachDivisible N d).filter (fun p => q ∣ N - p)).card

theorem goldbachDivisible_card_eq_AP (N d : ℕ) :
    (goldbachDivisible N d).card =
      MathlibNt.SieveTheory.BombieriVinogradov.primesInAP N d N := by
  unfold goldbachDivisible MathlibNt.SieveTheory.BombieriVinogradov.primesInAP
  congr 1
  apply filter_congr
  intro p hp
  rw [Nat.modEq_iff_dvd' (by have := mem_range.mp hp; omega)]

theorem sourceSequenceCount_eq_AP (N : ℕ) {d q : ℕ} (hcop : d.Coprime q) :
    sourceSequenceCount N d q =
      MathlibNt.SieveTheory.BombieriVinogradov.primesInAP N (d * q) N := by
  rw [← goldbachDivisible_card_eq_AP]
  unfold sourceSequenceCount
  congr 1
  ext p
  simp only [goldbachDivisible, mem_filter]
  constructor
  · rintro ⟨⟨hp, hprime, hd⟩, hq⟩
    exact ⟨hp, hprime, hcop.mul_dvd_of_dvd_of_dvd hd hq⟩
  · rintro ⟨hp, hprime, hdq⟩
    exact ⟨⟨hp, hprime, (dvd_mul_right d q).trans hdq⟩,
      (dvd_mul_left q d).trans hdq⟩

noncomputable def sourceSequenceRemainder (N d q : ℕ) : ℝ :=
  (sourceSequenceCount N d q : ℝ) -
    logarithmicIntegral N / (Nat.totient (d * q) : ℝ)

theorem sourceSequenceRemainder_eq_AP (N : ℕ) {d q : ℕ} (hcop : d.Coprime q) :
    sourceSequenceRemainder N d q = primeAPError N (d * q) N := by
  simp only [sourceSequenceRemainder, sourceSequenceCount_eq_AP N hcop, primeAPError]

/-- The actual finite strict prime product for `P(M)`. -/
noncomputable def ordinarySievePrimeProduct (M : ℕ) (z : ℝ) : ℕ :=
  ∏ p ∈ primeWindow M 0 z, p

theorem ordinarySievePrimeProduct_pos (M : ℕ) (z : ℝ) :
    0 < ordinarySievePrimeProduct M z :=
  prod_pos (fun _p hp => (mem_primeWindow.mp hp).1.pos)

theorem ordinarySievePrimeProduct_coprime (M : ℕ) (z : ℝ) :
    (ordinarySievePrimeProduct M z).Coprime M :=
  Nat.Coprime.prod_left (fun _p hp => (mem_primeWindow.mp hp).2.1)

/-- Either actual frozen Rosser coefficient, with its natural strict level. -/
noncomputable def ordinaryRosserWeight (upper : Bool) (N d D : ℕ) (z : ℝ)
    (q : ℕ) : ℝ :=
  if upper then upperRosserWeight (ordinarySievePrimeProduct (d * N) z) D q
  else lowerRosserWeight (ordinarySievePrimeProduct (d * N) z) D q

theorem ordinaryRosserWeight_abs_le_one (upper : Bool) (N d D q : ℕ) (z : ℝ) :
    |ordinaryRosserWeight upper N d D z q| ≤ 1 := by
  cases upper
  · exact abs_lowerRosserWeight_le_one _ _ _
  · exact abs_upperRosserWeight_le_one _ _ _

/-- Both the coprimality mask and full combined-modulus bound follow from
the concrete coefficients. Neither is an assumed sieve-weight property. -/
theorem ordinaryRosserWeight_support {upper : Bool} {N d D Q q : ℕ} {z : ℝ}
    (hD : D ≤ Q / d + 1) (hq : ordinaryRosserWeight upper N d D z q ≠ 0) :
    q ∈ (Icc 1 (Q / d)).filter (fun q => q.Coprime (d * N)) := by
  have hdiv : q ∣ ordinarySievePrimeProduct (d * N) z := by
    cases upper
    · exact lowerRosserWeight_dvd hq
    · exact upperRosserWeight_dvd hq
  have hlevel : q < D := by
    cases upper
    · exact lowerRosserWeight_lt_level hq
    · exact upperRosserWeight_lt_level hq
  exact mem_filter.mpr ⟨mem_Icc.mpr
    ⟨Nat.pos_of_dvd_of_pos hdiv (ordinarySievePrimeProduct_pos _ _), by omega⟩,
    (ordinarySievePrimeProduct_coprime _ _).of_dvd_left hdiv⟩

noncomputable def ordinaryRosserRemainder (upper : Bool) (N d D : ℕ)
    (z : ℝ) : ℝ :=
  ∑ q ∈ (ordinarySievePrimeProduct (d * N) z).divisors,
    ordinaryRosserWeight upper N d D z q * sourceSequenceRemainder N d q

theorem ordinaryRosserRemainder_le_AP {upper : Bool} {N d D Q : ℕ} (z : ℝ)
    (hD : D ≤ Q / d + 1) :
    |ordinaryRosserRemainder upper N d D z| ≤
      ∑ q ∈ (Icc 1 (Q / d)).filter (fun q => q.Coprime (d * N)),
        |primeAPError N (d * q) N| := by
  let P := ordinarySievePrimeProduct (d * N) z
  let T := (Icc 1 (Q / d)).filter (fun q => q.Coprime (d * N))
  let f := fun q => ordinaryRosserWeight upper N d D z q *
    sourceSequenceRemainder N d q
  have hsum : (∑ q ∈ P.divisors, f q) = ∑ q ∈ T, f q := by
    calc
      _ = ∑ q ∈ P.divisors ∪ T, f q := by
        apply sum_subset subset_union_left
        intro q _ hq
        have hz : ordinaryRosserWeight upper N d D z q = 0 := by
          by_contra hn
          have hd : q ∣ P := by
            cases upper
            · exact lowerRosserWeight_dvd hn
            · exact upperRosserWeight_dvd hn
          exact hq (Nat.mem_divisors.mpr ⟨hd, (ordinarySievePrimeProduct_pos _ _).ne'⟩)
        simp [f, hz]
      _ = ∑ q ∈ T, f q := by
        symm
        apply sum_subset subset_union_right
        intro q _ hq
        have hz : ordinaryRosserWeight upper N d D z q = 0 := by
          by_contra hn
          exact hq (ordinaryRosserWeight_support hD hn)
        simp [f, hz]
  change |∑ q ∈ P.divisors, f q| ≤ _
  rw [hsum]
  apply (abs_sum_le_sum_abs f T).trans
  apply sum_le_sum
  intro q hq
  have hc := (mem_filter.mp hq).2
  have hdc : d.Coprime q :=
    (hc.of_dvd_right (dvd_mul_right d N)).symm
  change |ordinaryRosserWeight upper N d D z q * sourceSequenceRemainder N d q| ≤ _
  rw [abs_mul, sourceSequenceRemainder_eq_AP N hdc]
  exact (mul_le_mul_of_nonneg_right (ordinaryRosserWeight_abs_le_one upper N d D q z)
    (abs_nonneg _)).trans_eq (one_mul _)

/-- The complete convolution support is retained, with the signed remainder
inside the sum, exactly as in the source's `R`. -/
noncomputable def convolutionRosserRemainder {i : ℕ} (N : ℕ)
    (W : Fin i → Finset ℕ) (upper : Bool) (D : ℕ → ℕ) (z : ℕ → ℝ) : ℝ :=
  ∑ d ∈ (Fintype.piFinset W).image (fun t => ∏ j, t j),
    (convolutionCoeff W d : ℝ) * ordinaryRosserRemainder upper N d (D d) (z d)

theorem convolutionRosserRemainder_le_AP {i N Q : ℕ} (W : Fin i → Finset ℕ)
    (upper : Bool) (D : ℕ → ℕ) (z : ℕ → ℝ)
    (hD : ∀ d ∈ (Fintype.piFinset W).image (fun t => ∏ j, t j),
      D d ≤ Q / d + 1) :
    |convolutionRosserRemainder N W upper D z| ≤ convolutionAPError N Q W := by
  rw [convolutionAPError_eq_support_sum]
  unfold convolutionRosserRemainder
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro d hd
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left (ordinaryRosserRemainder_le_AP (z d) (hD d hd))
    (Nat.cast_nonneg _)

/-- A finite family of actual Rosser terms costs its actual cardinality.
This is not a well-factorable-family existence assertion. -/
theorem finite_rosser_family_remainder_le_AP {i N Q L : ℕ}
    (W : Fin i → Finset ℕ) (upper : Fin L → Bool)
    (D : Fin L → ℕ → ℕ) (z : Fin L → ℕ → ℝ)
    (hD : ∀ l, ∀ d ∈ (Fintype.piFinset W).image (fun t => ∏ j, t j),
      D l d ≤ Q / d + 1) :
    |∑ l, convolutionRosserRemainder N W (upper l) (D l) (z l)| ≤
      (L : ℝ) * convolutionAPError N Q W := by
  calc
    _ ≤ ∑ l, |convolutionRosserRemainder N W (upper l) (D l) (z l)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin L, convolutionAPError N Q W :=
      sum_le_sum (fun l _ => convolutionRosserRemainder_le_AP W (upper l) (D l) (z l)
        (hD l))
    _ = _ := by simp

/-- Uniform ordinary-AP payment for the actual signed finite-family
consumer. Cutoffs, natural levels, signs, and all boxes follow `C,N0`. -/
theorem wu_signed_rosser_bombieri_vinogradov (k L : ℕ) {δ A : ℝ}
    (hδ : 0 < δ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
        1 + Real.log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * Real.log (N : ℝ) ^ (-4 : ℝ) →
        ∀ V : Fin i → ℝ, (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) →
        ∀ upper : Fin L → Bool, ∀ D : Fin L → ℕ → ℕ, ∀ z : Fin L → ℕ → ℝ,
        (∀ l, ∀ d ∈ (Fintype.piFinset (convolutionWuWindows N Δ V)).image
            (fun t => ∏ j, t j), D l d ≤ convolutionModulusCutoff N δ / d + 1) →
        |∑ l, convolutionRosserRemainder N (convolutionWuWindows N Δ V)
          (upper l) (D l) (z l)| ≤
            (L : ℝ) * (C * (N : ℝ) / Real.log N ^ A) := by
  obtain ⟨C, hC, N0, hBV⟩ := wu_convolution_bombieri_vinogradov k hδ hA
  refine ⟨C, hC, N0, ?_⟩
  intro N hN i hik Δ hlo hhi V hV upper D z hD
  exact (finite_rosser_family_remainder_le_AP _ upper D z hD).trans
    (mul_le_mul_of_nonneg_left (hBV N hN i hik Δ hlo hhi V hV) (Nat.cast_nonneg L))

end Wu2008DoubleSieve
