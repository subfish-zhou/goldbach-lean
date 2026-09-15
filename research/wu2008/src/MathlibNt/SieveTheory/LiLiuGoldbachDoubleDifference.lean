import MathlibNt.SieveTheory.LiLiuGoldbachIntermediateSums

open scoped BigOperators

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachDoubleDifference (P : Prop) : Decidable P := Classical.propDecidable P

/-- At cutoff `r`, adjoining the prime factor `r` to the sieve modulus does
not change which smaller primes are sifted. -/
theorem survivesSieve_mul_right_cutoff_prime_iff
    (N r n : ℕ) (hrPrime : r.Prime) :
    SurvivesSieve (N * r) r n ↔ SurvivesSieve N r n := by
  constructor
  · intro h ℓ hℓPrime hℓn hℓN
    by_cases hℓr : ℓ ∣ r
    · have hEq : ℓ = r := (Nat.prime_dvd_prime_iff_eq hℓPrime hrPrime).mp hℓr
      exact_mod_cast hEq.symm.le
    · exact h ℓ hℓPrime hℓn (by
        intro hMul
        rcases hℓPrime.dvd_mul.mp hMul with hN | hR
        · exact hℓN hN
        · exact hℓr hR)
  · intro h ℓ hℓPrime hℓn hℓNr
    exact h ℓ hℓPrime hℓn (fun hℓN => hℓNr (dvd_mul_of_dvd_left hℓN r))

/-- The literal count `H` is unchanged when the sieve modulus is replaced by
`N*r`, provided the cutoff is exactly the prime `r`. -/
theorem literalH_mul_right_cutoff_prime_eq
    (A : Finset ℕ) (N d r : ℕ) (hrPrime : r.Prime) :
    literalH A (N * r) d r = literalH A N d r := by
  unfold literalH
  congr 1
  apply congrArg Finset.card
  ext n
  simp [literalHPoint, survivesSieve_mul_right_cutoff_prime_iff N r n hrPrime]

private theorem doubleDifference_middleCarrier_eq
    (N r s : ℕ) (hrPrime : r.Prime) :
    (siftingPrimes (N * r) s).filter (fun q : ℕ => (r : ℝ) ≤ (q : ℝ)) =
      (goldbachHalfOpenPrimes N (r : ℝ) (s : ℝ)).filter (fun q : ℕ => r < q) := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqSift, hrq⟩
    have hq' := mem_siftingPrimes.mp hqSift
    have hqN : ¬q ∣ N := by
      intro hqN
      exact hq'.2.2 (dvd_mul_of_dvd_left hqN r)
    have hqne : q ≠ r := by
      intro hEq
      exact hq'.2.2 (hEq ▸ dvd_mul_of_dvd_right (dvd_refl r) N)
    have hrqNat : r ≤ q := by exact_mod_cast hrq
    have hrqStrict : r < q := lt_of_le_of_ne hrqNat hqne.symm
    apply Finset.mem_filter.mpr
    refine ⟨?_, hrqStrict⟩
    apply Finset.mem_filter.mpr
    refine ⟨mem_siftingPrimes.mpr ?_, ?_⟩
    · exact ⟨hq'.1, hq'.2.1, hqN⟩
    · exact_mod_cast hrqNat
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqHalf, hrqStrict⟩
    rcases Finset.mem_filter.mp hqHalf with ⟨hqSift, hrq⟩
    have hq' := mem_siftingPrimes.mp hqSift
    have hqNr : ¬q ∣ N * r := by
      intro hqNr
      rcases hq'.1.dvd_mul.mp hqNr with hqN | hqr
      · exact hq'.2.2 hqN
      · have hqrEq : q = r := (Nat.prime_dvd_prime_iff_eq hq'.1 hrPrime).mp hqr
        have hqNe : q ≠ r := by omega
        exact hqNe hqrEq
    apply Finset.mem_filter.mpr
    refine ⟨mem_siftingPrimes.mpr ?_, ?_⟩
    · exact ⟨hq'.1, hq'.2.1, hqNr⟩
    · exact_mod_cast (Nat.le_of_lt hrqStrict)

/-- Fixed-pair double-difference identity `HD`, with the genuine middle prime
range `r < q < s` and the literal triple divisibility fibre. -/
theorem goldbachDoubleDifference_fixed_pair
    (A : Finset ℕ) (N r s : ℕ)
    (hrPrime : r.Prime) (hsPrime : s.Prime) (hrs : r < s) :
    literalH A N (r * s) r - literalH A (N * r) (r * s) s =
      ∑ q ∈ (goldbachHalfOpenPrimes N (r : ℝ) (s : ℝ)).filter (fun q : ℕ => r < q),
        literalH A (N * r) (r * q * s) q := by
  have hbuch :=
    literalH_buchstab_interval A (N * r) (r * s)
      (show (r : ℝ) ≤ (s : ℝ) by exact_mod_cast Nat.le_of_lt hrs)
  have hleft : literalH A (N * r) (r * s) r = literalH A N (r * s) r := by
    simpa using literalH_mul_right_cutoff_prime_eq A N (r * s) r hrPrime
  rw [hleft] at hbuch
  have hcarrier := doubleDifference_middleCarrier_eq N r s hrPrime
  rw [hcarrier] at hbuch
  have hsum :
      ∑ q ∈ (goldbachHalfOpenPrimes N (r : ℝ) (s : ℝ)).filter (fun q : ℕ => r < q),
        literalH (A.filter fun n => r * s ∣ n) (N * r) q q =
      ∑ q ∈ (goldbachHalfOpenPrimes N (r : ℝ) (s : ℝ)).filter (fun q : ℕ => r < q),
        literalH A (N * r) (r * q * s) q := by
    apply Finset.sum_congr rfl
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqHalf, hrqStrict⟩
    have hqSift : q ∈ siftingPrimes N s := (Finset.mem_filter.mp hqHalf).1
    have hq' := mem_siftingPrimes.mp hqSift
    have hqs : q < s := by exact_mod_cast hq'.2.1
    have hqrCoprime : Nat.Coprime q r := by
      exact (Nat.coprime_primes hq'.1 hrPrime).mpr (ne_of_gt hrqStrict)
    have hqsCoprime : Nat.Coprime q s := by
      exact (Nat.coprime_primes hq'.1 hsPrime).mpr (ne_of_lt hqs)
    have hqrs : Nat.Coprime (r * s) q := by
      rw [Nat.coprime_mul_iff_left]
      exact ⟨hqrCoprime.symm, hqsCoprime.symm⟩
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      literalH_filter_mul_of_coprime A (N * r) (r * s) q q hqrs
  rw [hsum] at hbuch
  exact hbuch

/-- The strict part of `V`, with the diagonal removed but the same `r<s`
carrier as `U`. -/
noncomputable def goldbachVStrict (A : Finset ℕ) (N : ℕ) (z y : ℝ) : ℤ :=
  ∑ s ∈ goldbachHalfOpenPrimes N z y,
    ∑ r ∈ (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)),
      literalH A (N * r) (r * s) s

private theorem halfOpen_filter_lt_eq_inner
    (N : ℕ) (z y : ℝ) {s : ℕ}
    (hs : s ∈ goldbachHalfOpenPrimes N z y) :
    (goldbachHalfOpenPrimes N z y).filter (fun r : ℕ => r < s) =
      (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)) := by
  have hsSift : s ∈ siftingPrimes N y := (Finset.mem_filter.mp hs).1
  have hsy : (s : ℝ) < y := (mem_siftingPrimes.mp hsSift).2.1
  ext r
  constructor
  · intro hr
    rcases Finset.mem_filter.mp hr with ⟨hrHalf, hrs⟩
    rcases Finset.mem_filter.mp hrHalf with ⟨hrSift, hzr⟩
    have hr' := mem_siftingPrimes.mp hrSift
    apply Finset.mem_filter.mpr
    refine ⟨mem_siftingPrimes.mpr ?_, hzr⟩
    exact ⟨hr'.1, by exact_mod_cast hrs, hr'.2.2⟩
  · intro hr
    rcases Finset.mem_filter.mp hr with ⟨hrSift, hzr⟩
    have hr' := mem_siftingPrimes.mp hrSift
    apply Finset.mem_filter.mpr
    refine ⟨?_, by exact_mod_cast hr'.2.1⟩
    apply Finset.mem_filter.mpr
    refine ⟨mem_siftingPrimes.mpr ?_, hzr⟩
    exact ⟨hr'.1, hr'.2.1.trans hsy, hr'.2.2⟩

private theorem halfOpen_filter_not_lt_eq_singleton
    (N : ℕ) (z y : ℝ) {s : ℕ}
    (hs : s ∈ goldbachHalfOpenPrimes N z y) :
    ((goldbachHalfOpenPrimes N z y).filter (fun r : ℕ => r ≤ s)).filter
        (fun r : ℕ => ¬r < s) = {s} := by
  ext r
  constructor
  · intro hr
    simp only [Finset.mem_filter, Finset.mem_singleton] at hr ⊢
    rcases hr with ⟨⟨_, hrsLe⟩, hrsGe⟩
    exact le_antisymm hrsLe (not_lt.mp hrsGe)
  · intro hr
    rcases Finset.mem_singleton.mp hr with rfl
    simp [hs]

/-- The weakly ordered double sum splits into its strict part plus the actual
diagonal `Q`. -/
theorem goldbachV_eq_goldbachVStrict_add_goldbachQ
    (A : Finset ℕ) (N : ℕ) (z y : ℝ) :
    goldbachV A N z y = goldbachVStrict A N z y + goldbachQ A N z y := by
  unfold goldbachV goldbachVStrict goldbachQ
  calc
    ∑ s ∈ goldbachHalfOpenPrimes N z y,
        ∑ r ∈ (goldbachHalfOpenPrimes N z y).filter (fun r => r ≤ s),
          literalH A (N * r) (r * s) s =
      ∑ s ∈ goldbachHalfOpenPrimes N z y,
        ((∑ r ∈ (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)),
            literalH A (N * r) (r * s) s) +
          literalH A N (s ^ 2) s) := by
            apply Finset.sum_congr rfl
            intro s hs
            have hsPrime : s.Prime := (mem_siftingPrimes.mp (Finset.mem_filter.mp hs).1).1
            have hsplit :=
              Finset.sum_filter_add_sum_filter_not
                ((goldbachHalfOpenPrimes N z y).filter (fun r : ℕ => r ≤ s))
                (fun r : ℕ => r < s)
                (fun r => literalH A (N * r) (r * s) s)
            rw [← hsplit]
            have hstrict :
                ((goldbachHalfOpenPrimes N z y).filter (fun r : ℕ => r ≤ s)).filter
                    (fun r : ℕ => r < s) =
                  (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)) := by
              ext r
              constructor
              · intro hr
                rcases Finset.mem_filter.mp hr with ⟨hrLe, hrs⟩
                rcases Finset.mem_filter.mp hrLe with ⟨hrHalf, hrsLe⟩
                have hr' : r ∈ (goldbachHalfOpenPrimes N z y).filter (fun r : ℕ => r < s) := by
                  exact Finset.mem_filter.mpr ⟨hrHalf, hrs⟩
                rw [halfOpen_filter_lt_eq_inner N z y hs] at hr'
                exact hr'
              · intro hr
                have hr' : r ∈ (goldbachHalfOpenPrimes N z y).filter (fun r : ℕ => r < s) := by
                  rw [halfOpen_filter_lt_eq_inner N z y hs]
                  exact hr
                rcases Finset.mem_filter.mp hr' with ⟨hrHalf, hrs⟩
                exact Finset.mem_filter.mpr
                  ⟨Finset.mem_filter.mpr ⟨hrHalf, Nat.le_of_lt hrs⟩, hrs⟩
            have hdiag :
                ((goldbachHalfOpenPrimes N z y).filter (fun r : ℕ => r ≤ s)).filter
                    (fun r : ℕ => ¬r < s) = {s} :=
              halfOpen_filter_not_lt_eq_singleton N z y hs
            rw [hstrict, hdiag, Finset.sum_singleton]
            simpa [pow_two] using literalH_mul_right_cutoff_prime_eq A N (s * s) s hsPrime
    _ = (∑ s ∈ goldbachHalfOpenPrimes N z y,
          ∑ r ∈ (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)),
            literalH A (N * r) (r * s) s) +
        ∑ s ∈ goldbachHalfOpenPrimes N z y, literalH A N (s ^ 2) s := by
          rw [Finset.sum_add_distrib]
    _ = goldbachVStrict A N z y + goldbachQ A N z y := by
          simp [goldbachVStrict, goldbachQ]

/-- Summing the fixed-pair double-difference identities gives the strict
triple sum `W`. -/
theorem goldbachUStrict_sub_goldbachVStrict_eq_goldbachWStrict
    (A : Finset ℕ) (N : ℕ) (z y : ℝ) :
    goldbachUStrict A N z y - goldbachVStrict A N z y = goldbachWStrict A N z y := by
  unfold goldbachUStrict goldbachVStrict goldbachWStrict
  calc
    (∑ s ∈ goldbachHalfOpenPrimes N z y,
        ∑ r ∈ (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)),
          literalH A N (r * s) r) -
      (∑ s ∈ goldbachHalfOpenPrimes N z y,
        ∑ r ∈ (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)),
          literalH A (N * r) (r * s) s) =
        ∑ s ∈ goldbachHalfOpenPrimes N z y,
          ((∑ r ∈ (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)),
              literalH A N (r * s) r) -
            ∑ r ∈ (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)),
              literalH A (N * r) (r * s) s) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ t ∈ goldbachHalfOpenPrimes N z y,
          ∑ r ∈ (siftingPrimes N t).filter (fun r : ℕ => z ≤ (r : ℝ)),
            (literalH A N (r * t) r - literalH A (N * r) (r * t) t) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.sum_sub_distrib]
    _ = goldbachWStrict A N z y := by
          apply Finset.sum_congr rfl
          intro t ht
          apply Finset.sum_congr rfl
          intro r hr
          have htSift : t ∈ siftingPrimes N y := (Finset.mem_filter.mp ht).1
          have htPrime : t.Prime := (mem_siftingPrimes.mp htSift).1
          have hrSift : r ∈ siftingPrimes N t := (Finset.mem_filter.mp hr).1
          have hrPrime : r.Prime := (mem_siftingPrimes.mp hrSift).1
          have hrt : r < t := by exact_mod_cast (mem_siftingPrimes.mp hrSift).2.1
          simpa [goldbachHalfOpenPrimes, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
            goldbachDoubleDifference_fixed_pair A N r t hrPrime htPrime hrt

/-- Exact finite `H3`: the strict double difference equals the strict triple
sum minus the actual diagonal square term. -/
theorem goldbachDoubleDifference_eq_goldbachWStrict_sub_goldbachQ
    (A : Finset ℕ) (N : ℕ) (z y : ℝ) :
    goldbachUStrict A N z y - goldbachV A N z y =
      goldbachWStrict A N z y - goldbachQ A N z y := by
  calc
    goldbachUStrict A N z y - goldbachV A N z y =
        goldbachUStrict A N z y - (goldbachVStrict A N z y + goldbachQ A N z y) := by
          rw [goldbachV_eq_goldbachVStrict_add_goldbachQ]
    _ = (goldbachUStrict A N z y - goldbachVStrict A N z y) - goldbachQ A N z y := by
          ring
    _ = goldbachWStrict A N z y - goldbachQ A N z y := by
          rw [goldbachUStrict_sub_goldbachVStrict_eq_goldbachWStrict]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig