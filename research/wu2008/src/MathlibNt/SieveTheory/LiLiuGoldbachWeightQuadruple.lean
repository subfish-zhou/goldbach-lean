import MathlibNt.SieveTheory.LiLiuGoldbachWeightInitial

open scoped BigOperators

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachWeightQuadruple (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The weakly ordered closed triple sum
`Σ_{z≤r≤s≤t≤b} H(A,N*r,rst;s)`. -/
noncomputable def goldbachWeightT14 (A : Finset ℕ) (N : ℕ) (z b : ℝ) : ℤ :=
  ∑ t ∈ goldbachClosedPrimes N z b,
    ∑ s ∈ goldbachClosedPrimes N z (t : ℝ),
      ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
        literalH A (N * r) (r * s * t) s

/-- The closed cross triple sum
`Σ_{z≤r≤s≤b≤t≤c} H(A,N*r,rst;s)`. -/
noncomputable def goldbachWeightT15 (A : Finset ℕ) (N : ℕ) (z b c : ℝ) : ℤ :=
  ∑ t ∈ goldbachClosedPrimes N b c,
    ∑ s ∈ goldbachClosedPrimes N z b,
      ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
        literalH A (N * r) (r * s * t) s

/-- The weakly ordered closed quadruple sum
`Σ_{z≤r≤q≤s≤t≤b} H(A,N*r,rqst;q)`. -/
noncomputable def goldbachWeightG11 (A : Finset ℕ) (N : ℕ) (z b : ℝ) : ℤ :=
  ∑ t ∈ goldbachClosedPrimes N z b,
    ∑ s ∈ goldbachClosedPrimes N z (t : ℝ),
      ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
        ∑ q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ),
          literalH A (N * r) (r * q * s * t) q

/-- The closed cross quadruple sum
`Σ_{z≤r≤q≤s≤b≤t≤c} H(A,N*r,rqst;q)`. -/
noncomputable def goldbachWeightG12 (A : Finset ℕ) (N : ℕ) (z b c : ℝ) : ℤ :=
  ∑ t ∈ goldbachClosedPrimes N b c,
    ∑ s ∈ goldbachClosedPrimes N z b,
      ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
        ∑ q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ),
          literalH A (N * r) (r * q * s * t) q

theorem goldbachWeightT14_nonneg (A : Finset ℕ) (N : ℕ) (z b : ℝ) :
    0 ≤ goldbachWeightT14 A N z b := by
  unfold goldbachWeightT14
  refine Finset.sum_nonneg ?_
  intro t ht
  refine Finset.sum_nonneg ?_
  intro s hs
  refine Finset.sum_nonneg ?_
  intro r hr
  exact literalH_nonneg A (N * r) (r * s * t) s

theorem goldbachWeightT15_nonneg (A : Finset ℕ) (N : ℕ) (z b c : ℝ) :
    0 ≤ goldbachWeightT15 A N z b c := by
  unfold goldbachWeightT15
  refine Finset.sum_nonneg ?_
  intro t ht
  refine Finset.sum_nonneg ?_
  intro s hs
  refine Finset.sum_nonneg ?_
  intro r hr
  exact literalH_nonneg A (N * r) (r * s * t) s

theorem goldbachWeightG11_nonneg (A : Finset ℕ) (N : ℕ) (z b : ℝ) :
    0 ≤ goldbachWeightG11 A N z b := by
  unfold goldbachWeightG11
  refine Finset.sum_nonneg ?_
  intro t ht
  refine Finset.sum_nonneg ?_
  intro s hs
  refine Finset.sum_nonneg ?_
  intro r hr
  refine Finset.sum_nonneg ?_
  intro q hq
  exact literalH_nonneg A (N * r) (r * q * s * t) q

theorem goldbachWeightG12_nonneg (A : Finset ℕ) (N : ℕ) (z b c : ℝ) :
    0 ≤ goldbachWeightG12 A N z b c := by
  unfold goldbachWeightG12
  refine Finset.sum_nonneg ?_
  intro t ht
  refine Finset.sum_nonneg ?_
  intro s hs
  refine Finset.sum_nonneg ?_
  intro r hr
  refine Finset.sum_nonneg ?_
  intro q hq
  exact literalH_nonneg A (N * r) (r * q * s * t) q

private theorem goldbachWeightQuad_middleCarrier_eq
    (N r s : ℕ) (hrPrime : r.Prime) :
    (siftingPrimes (N * r) s).filter (fun q : ℕ => (r : ℝ) ≤ (q : ℝ)) =
      (goldbachClosedPrimes N (r : ℝ) (s : ℝ)).filter
        (fun q : ℕ => (q : ℝ) < s ∧ r < q) := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqSift, hrq⟩
    rcases mem_siftingPrimes.mp hqSift with ⟨hqPrime, hqs, hqNr⟩
    have hqN : ¬q ∣ N := by
      intro hqN
      exact hqNr (dvd_mul_of_dvd_left hqN r)
    have hqne : q ≠ r := by
      intro hEq
      subst q
      exact hqNr (dvd_mul_of_dvd_right (dvd_refl r) N)
    have hrqNat : r ≤ q := by
      exact_mod_cast hrq
    have hqr : r < q := lt_of_le_of_ne hrqNat hqne.symm
    exact Finset.mem_filter.mpr
      ⟨mem_goldbachClosedPrimes_iff.mpr
          ⟨hqPrime, hqN, by exact_mod_cast hrqNat, hqs.le⟩,
        ⟨hqs, hqr⟩⟩
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqClosed, hqStrict⟩
    rcases mem_goldbachClosedPrimes_iff.mp hqClosed with ⟨hqPrime, hqN, _, _⟩
    have hqNr : ¬q ∣ N * r := by
      intro hqNr
      rcases hqPrime.dvd_mul.mp hqNr with hqN' | hqr
      · exact hqN hqN'
      · have hEq : q = r := (Nat.prime_dvd_prime_iff_eq hqPrime hrPrime).mp hqr
        exact (ne_of_gt hqStrict.2) hEq
    exact Finset.mem_filter.mpr
      ⟨mem_siftingPrimes.mpr ⟨hqPrime, hqStrict.1, hqNr⟩,
        by exact_mod_cast (Nat.le_of_lt hqStrict.2)⟩

private theorem goldbachWeightQuad_fixedCell_eq
    (A : Finset ℕ) (N r s t : ℕ)
    (hrPrime : r.Prime) (hsPrime : s.Prime) (htPrime : t.Prime)
    (hrs : r ≤ s) (hst : s ≤ t) :
    literalH A N (r * s * t) r =
      literalH A (N * r) (r * s * t) s +
        ∑ q ∈ (goldbachClosedPrimes N (r : ℝ) (s : ℝ)).filter
            (fun q : ℕ => (q : ℝ) < s ∧ r < q),
          literalH A (N * r) (r * q * s * t) q := by
  have hbuch :=
    literalH_buchstab_interval A (N * r) (r * s * t)
      (show (r : ℝ) ≤ (s : ℝ) by exact_mod_cast hrs)
  rw [literalH_mul_right_cutoff_prime_eq A N (r * s * t) r hrPrime] at hbuch
  rw [goldbachWeightQuad_middleCarrier_eq N r s hrPrime] at hbuch
  have hsum :
      ∑ q ∈ (goldbachClosedPrimes N (r : ℝ) (s : ℝ)).filter
          (fun q : ℕ => (q : ℝ) < s ∧ r < q),
        literalH (A.filter fun n => r * s * t ∣ n) (N * r) q q =
      ∑ q ∈ (goldbachClosedPrimes N (r : ℝ) (s : ℝ)).filter
          (fun q : ℕ => (q : ℝ) < s ∧ r < q),
        literalH A (N * r) (r * q * s * t) q := by
    apply Finset.sum_congr rfl
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqClosed, hqStrict⟩
    rcases mem_goldbachClosedPrimes_iff.mp hqClosed with ⟨hqPrime, _, _, _⟩
    have hqrCoprime : Nat.Coprime q r :=
      (Nat.coprime_primes hqPrime hrPrime).mpr (ne_of_gt hqStrict.2)
    have hqsNat : q < s := by
      exact_mod_cast hqStrict.1
    have hqsCoprime : Nat.Coprime q s :=
      (Nat.coprime_primes hqPrime hsPrime).mpr (ne_of_lt hqsNat)
    have hqtNat : q < t := lt_of_lt_of_le hqsNat hst
    have hqtCoprime : Nat.Coprime q t :=
      (Nat.coprime_primes hqPrime htPrime).mpr (ne_of_lt hqtNat)
    have hqrs : Nat.Coprime (r * s) q := by
      rw [Nat.coprime_mul_iff_left]
      exact ⟨hqrCoprime.symm, hqsCoprime.symm⟩
    have hqrst : Nat.Coprime (r * s * t) q := by
      simpa [Nat.mul_assoc] using hqrs.mul_left hqtCoprime.symm
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      literalH_filter_mul_of_coprime A (N * r) (r * s * t) q q hqrst
  rw [hsum] at hbuch
  omega

private theorem goldbachWeightQuad_fixedCell_le
    (A : Finset ℕ) (N r s t : ℕ)
    (hrPrime : r.Prime) (hsPrime : s.Prime) (htPrime : t.Prime)
    (hrs : r ≤ s) (hst : s ≤ t) :
    literalH A N (r * s * t) r ≤
      literalH A (N * r) (r * s * t) s +
        ∑ q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ),
          literalH A (N * r) (r * q * s * t) q := by
  have hcell :=
    goldbachWeightQuad_fixedCell_eq A N r s t hrPrime hsPrime htPrime hrs hst
  have hsumle :
      ∑ q ∈ (goldbachClosedPrimes N (r : ℝ) (s : ℝ)).filter
          (fun q : ℕ => (q : ℝ) < s ∧ r < q),
        literalH A (N * r) (r * q * s * t) q ≤
      ∑ q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ),
        literalH A (N * r) (r * q * s * t) q := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro q hq
      exact (Finset.mem_filter.mp hq).1
    · intro q hq hqnot
      exact literalH_nonneg A (N * r) (r * q * s * t) q
  omega

theorem goldbachWeightG14_le_goldbachWeightT14_add_goldbachWeightG11
    (A : Finset ℕ) (N : ℕ) (z b : ℝ) :
    goldbachWeightG14 A N z b ≤ goldbachWeightT14 A N z b + goldbachWeightG11 A N z b := by
  unfold goldbachWeightG14 goldbachWeightT14 goldbachWeightG11
  calc
    ∑ t ∈ goldbachClosedPrimes N z b,
        ∑ s ∈ goldbachClosedPrimes N z (t : ℝ),
          ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
            literalH A N (r * s * t) r
      ≤
    ∑ t ∈ goldbachClosedPrimes N z b,
        ∑ s ∈ goldbachClosedPrimes N z (t : ℝ),
          ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
            (literalH A (N * r) (r * s * t) s +
              ∑ q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ),
                literalH A (N * r) (r * q * s * t) q) := by
          refine Finset.sum_le_sum ?_
          intro t ht
          refine Finset.sum_le_sum ?_
          intro s hs
          refine Finset.sum_le_sum ?_
          intro r hr
          rcases mem_goldbachClosedPrimes_iff.mp ht with ⟨htPrime, _, _, _⟩
          rcases mem_goldbachClosedPrimes_iff.mp hs with ⟨hsPrime, _, _, hst⟩
          rcases mem_goldbachClosedPrimes_iff.mp hr with ⟨hrPrime, _, _, hrs⟩
          have hrsNat : r ≤ s := by
            exact_mod_cast hrs
          have hstNat : s ≤ t := by
            exact_mod_cast hst
          exact goldbachWeightQuad_fixedCell_le A N r s t hrPrime hsPrime htPrime hrsNat hstNat
    _ =
      (∑ t ∈ goldbachClosedPrimes N z b,
          ∑ s ∈ goldbachClosedPrimes N z (t : ℝ),
            ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
              literalH A (N * r) (r * s * t) s) +
        ∑ t ∈ goldbachClosedPrimes N z b,
          ∑ s ∈ goldbachClosedPrimes N z (t : ℝ),
            ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
              ∑ q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ),
                literalH A (N * r) (r * q * s * t) q := by
          simp_rw [Finset.sum_add_distrib]
    _ = goldbachWeightT14 A N z b + goldbachWeightG11 A N z b := by
          rfl

theorem goldbachWeightG15_le_goldbachWeightT15_add_goldbachWeightG12
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ) :
    goldbachWeightG15 A N z b c ≤ goldbachWeightT15 A N z b c + goldbachWeightG12 A N z b c := by
  unfold goldbachWeightG15 goldbachWeightT15 goldbachWeightG12
  calc
    ∑ t ∈ goldbachClosedPrimes N b c,
        ∑ s ∈ goldbachClosedPrimes N z b,
          ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
            literalH A N (r * s * t) r
      ≤
    ∑ t ∈ goldbachClosedPrimes N b c,
        ∑ s ∈ goldbachClosedPrimes N z b,
          ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
            (literalH A (N * r) (r * s * t) s +
              ∑ q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ),
                literalH A (N * r) (r * q * s * t) q) := by
          refine Finset.sum_le_sum ?_
          intro t ht
          refine Finset.sum_le_sum ?_
          intro s hs
          refine Finset.sum_le_sum ?_
          intro r hr
          rcases mem_goldbachClosedPrimes_iff.mp ht with ⟨htPrime, _, hbt, _⟩
          rcases mem_goldbachClosedPrimes_iff.mp hs with ⟨hsPrime, _, _, hsb⟩
          rcases mem_goldbachClosedPrimes_iff.mp hr with ⟨hrPrime, _, _, hrs⟩
          have hrsNat : r ≤ s := by
            exact_mod_cast hrs
          have hstNat : s ≤ t := by
            exact_mod_cast (hsb.trans hbt)
          exact goldbachWeightQuad_fixedCell_le A N r s t hrPrime hsPrime htPrime hrsNat hstNat
    _ =
      (∑ t ∈ goldbachClosedPrimes N b c,
          ∑ s ∈ goldbachClosedPrimes N z b,
            ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
              literalH A (N * r) (r * s * t) s) +
        ∑ t ∈ goldbachClosedPrimes N b c,
          ∑ s ∈ goldbachClosedPrimes N z b,
            ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
              ∑ q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ),
                literalH A (N * r) (r * q * s * t) q := by
          simp_rw [Finset.sum_add_distrib]
    _ = goldbachWeightT15 A N z b c + goldbachWeightG12 A N z b c := by
          rfl

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig