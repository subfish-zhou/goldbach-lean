import MathlibNt.SieveTheory.LiLiuGoldbachClosedTriples

open scoped BigOperators

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachWeightInitial (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The weakly ordered closed double sum
`Σ_{z≤r≤s≤b, r,s∈P(N)} H(A,N,rs;z)`. -/
noncomputable def goldbachWeightG6 (A : Finset ℕ) (N : ℕ) (z b : ℝ) : ℤ :=
  ∑ s ∈ goldbachClosedPrimes N z b,
    ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
      literalH A N (r * s) z

/-- The closed cross double sum
`Σ_{z≤r≤b≤t≤c, r,t∈P(N)} H(A,N,rt;z)`. -/
noncomputable def goldbachWeightG7 (A : Finset ℕ) (N : ℕ) (z b c : ℝ) : ℤ :=
  ∑ t ∈ goldbachClosedPrimes N b c,
    ∑ r ∈ goldbachClosedPrimes N z b,
      literalH A N (r * t) z

/-- The weakly ordered closed triple sum
`Σ_{z≤r≤s≤t≤b, r,s,t∈P(N)} H(A,N,rst;r)`. -/
noncomputable def goldbachWeightG14 (A : Finset ℕ) (N : ℕ) (z b : ℝ) : ℤ :=
  ∑ t ∈ goldbachClosedPrimes N z b,
    ∑ s ∈ goldbachClosedPrimes N z (t : ℝ),
      ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
        literalH A N (r * s * t) r

/-- The closed cross triple sum
`Σ_{z≤r≤s≤b≤t≤c, r,s,t∈P(N)} H(A,N,rst;r)`. -/
noncomputable def goldbachWeightG15 (A : Finset ℕ) (N : ℕ) (z b c : ℝ) : ℤ :=
  ∑ t ∈ goldbachClosedPrimes N b c,
    ∑ s ∈ goldbachClosedPrimes N z b,
      ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
        literalH A N (r * s * t) r

/-- The actual diagonal square contribution
`Σ_{z≤r<b, r∈P(N)} H(A,N,r²;z)`. -/
noncomputable def goldbachWeightD6 (A : Finset ℕ) (N : ℕ) (z b : ℝ) : ℤ :=
  ∑ r ∈ goldbachHalfOpenPrimes N z b, literalH A N (r ^ 2) z

/-- The closed endpoint pair mass
`Σ_{z≤r≤s=b, r,s∈P(N)} H(A,N,rs;z)`, including `r = s = b`. -/
noncomputable def goldbachWeightB6pair (A : Finset ℕ) (N : ℕ) (z b : ℝ) : ℤ :=
  ∑ s ∈ (goldbachClosedPrimes N z b).filter (fun s : ℕ => b ≤ (s : ℝ)),
    ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
      literalH A N (r * s) z

/-- The closed endpoint cross mass
`Σ_{r=b≤t≤c, r,t∈P(N)} H(A,N,rt;z)`, including `r = t = b`. -/
noncomputable def goldbachWeightB7 (A : Finset ℕ) (N : ℕ) (z b c : ℝ) : ℤ :=
  ∑ t ∈ goldbachClosedPrimes N b c,
    ∑ r ∈ (goldbachClosedPrimes N z b).filter (fun r : ℕ => b ≤ (r : ℝ)),
      literalH A N (r * t) z

private noncomputable def goldbachWeightPStrict (A : Finset ℕ) (N : ℕ) (z b : ℝ) : ℤ :=
  ∑ s ∈ goldbachHalfOpenPrimes N z b,
    ∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ),
      literalH A N (r * s) z

private noncomputable def goldbachWeightA14 (A : Finset ℕ) (N : ℕ) (z b : ℝ) : ℤ :=
  ∑ t ∈ goldbachHalfOpenPrimes N z b,
    ∑ s ∈ goldbachHalfOpenPrimes N z (t : ℝ),
      ∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ),
        literalH A N (r * s * t) r

private noncomputable def goldbachWeightCStrict
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ) : ℤ :=
  ∑ t ∈ goldbachClosedPrimes N b c,
    ∑ r ∈ goldbachHalfOpenPrimes N z b,
      literalH A N (r * t) z

private noncomputable def goldbachWeightA15
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ) : ℤ :=
  ∑ t ∈ goldbachClosedPrimes N b c,
    ∑ s ∈ goldbachHalfOpenPrimes N z b,
      ∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ),
        literalH A N (r * s * t) r

private theorem goldbachHalfOpenPrimes_subset_closed
    (N : ℕ) (z y : ℝ) :
    goldbachHalfOpenPrimes N z y ⊆ goldbachClosedPrimes N z y := by
  intro p hp
  rcases mem_goldbachHalfOpenPrimes_iff.mp hp with ⟨hpPrime, hpN, hpz, hpy⟩
  exact mem_goldbachClosedPrimes_iff.mpr ⟨hpPrime, hpN, hpz, hpy.le⟩

private theorem goldbachWeightClosedPrimes_filter_lt_eq_halfOpen
    (N : ℕ) (z y : ℝ) :
    (goldbachClosedPrimes N z y).filter (fun p : ℕ => (p : ℝ) < y) =
      goldbachHalfOpenPrimes N z y := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpClosed, hpy⟩
    rcases mem_goldbachClosedPrimes_iff.mp hpClosed with ⟨hpPrime, hpN, hpz, _⟩
    exact mem_goldbachHalfOpenPrimes_iff.mpr ⟨hpPrime, hpN, hpz, hpy⟩
  · intro hp
    rcases mem_goldbachHalfOpenPrimes_iff.mp hp with ⟨hpPrime, hpN, hpz, hpy⟩
    exact Finset.mem_filter.mpr
      ⟨mem_goldbachClosedPrimes_iff.mpr ⟨hpPrime, hpN, hpz, hpy.le⟩, hpy⟩

private theorem goldbachWeightClosedPrimes_filter_not_lt_self_eq_singleton
    (N : ℕ) (z : ℝ) {t : ℕ}
    (ht : t ∈ goldbachClosedPrimes N z (t : ℝ)) :
    ((goldbachClosedPrimes N z (t : ℝ)).filter fun p : ℕ => ¬(p : ℝ) < t) = {t} := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpClosed, hpNotLt⟩
    rcases mem_goldbachClosedPrimes_iff.mp hpClosed with ⟨_, _, _, hpt⟩
    have htp : (t : ℝ) ≤ p := not_lt.mp hpNotLt
    have hptNat : p ≤ t := by exact_mod_cast hpt
    have htpNat : t ≤ p := by exact_mod_cast htp
    exact Finset.mem_singleton.mpr (le_antisymm hptNat htpNat)
  · intro hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact Finset.mem_filter.mpr ⟨ht, not_lt.mpr le_rfl⟩

private theorem goldbachWeightClosedPrimes_filter_lt_eq_halfOpen_of_le
    (N : ℕ) (z b c : ℝ) (hbc : b ≤ c) :
    (goldbachClosedPrimes N z c).filter (fun p : ℕ => (p : ℝ) < b) =
      goldbachHalfOpenPrimes N z b := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpClosed, hpb⟩
    rcases mem_goldbachClosedPrimes_iff.mp hpClosed with ⟨hpPrime, hpN, hpz, _⟩
    exact mem_goldbachHalfOpenPrimes_iff.mpr ⟨hpPrime, hpN, hpz, hpb⟩
  · intro hp
    rcases mem_goldbachHalfOpenPrimes_iff.mp hp with ⟨hpPrime, hpN, hpz, hpb⟩
    exact Finset.mem_filter.mpr
      ⟨mem_goldbachClosedPrimes_iff.mpr ⟨hpPrime, hpN, hpz, hpb.le.trans hbc⟩, hpb⟩

private theorem goldbachWeightClosedPrimes_filter_not_lt_eq_closed
    (N : ℕ) (z b c : ℝ) (hzb : z ≤ b) :
    (goldbachClosedPrimes N z c).filter (fun p : ℕ => ¬(p : ℝ) < b) =
      goldbachClosedPrimes N b c := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpClosed, hpNotLt⟩
    rcases mem_goldbachClosedPrimes_iff.mp hpClosed with ⟨hpPrime, hpN, _, hpc⟩
    exact mem_goldbachClosedPrimes_iff.mpr ⟨hpPrime, hpN, not_lt.mp hpNotLt, hpc⟩
  · intro hp
    rcases mem_goldbachClosedPrimes_iff.mp hp with ⟨hpPrime, hpN, hpb, hpc⟩
    exact Finset.mem_filter.mpr
      ⟨mem_goldbachClosedPrimes_iff.mpr ⟨hpPrime, hpN, hzb.trans hpb, hpc⟩, not_lt.mpr hpb⟩

private theorem goldbachWeightClosedPairSlice_eq
    (A : Finset ℕ) (N : ℕ) (z : ℝ) {s : ℕ}
    (hsClosed : s ∈ goldbachClosedPrimes N z (s : ℝ)) :
    (∑ r ∈ goldbachClosedPrimes N z (s : ℝ), literalH A N (r * s) z) =
      (∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ), literalH A N (r * s) z) +
        literalH A N (s ^ 2) z := by
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (goldbachClosedPrimes N z (s : ℝ))
      (fun r : ℕ => (r : ℝ) < s)
      (fun r => literalH A N (r * s) z)
  rw [goldbachWeightClosedPrimes_filter_lt_eq_halfOpen,
    goldbachWeightClosedPrimes_filter_not_lt_self_eq_singleton N z hsClosed,
    Finset.sum_singleton] at hsplit
  simpa [pow_two] using hsplit.symm

private theorem goldbachUStrict_eq_goldbachWeightPStrict_sub_goldbachWeightA14
    (A : Finset ℕ) (N : ℕ) (z b : ℝ) :
    goldbachUStrict A N z b = goldbachWeightPStrict A N z b - goldbachWeightA14 A N z b := by
  unfold goldbachUStrict goldbachWeightPStrict goldbachWeightA14
  calc
    ∑ s ∈ goldbachHalfOpenPrimes N z b,
        ∑ r ∈ (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)),
          literalH A N (r * s) r =
      ∑ s ∈ goldbachHalfOpenPrimes N z b,
        (∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ), literalH A N (r * s) r) := by
          simp [goldbachHalfOpenPrimes]
    _ =
      ∑ s ∈ goldbachHalfOpenPrimes N z b,
        ((∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ), literalH A N (r * s) z) -
          ∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ),
            ∑ q ∈ goldbachHalfOpenPrimes N z (r : ℝ),
              literalH A N (q * r * s) q) := by
          apply Finset.sum_congr rfl
          intro s hs
          calc
            ∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ), literalH A N (r * s) r =
              ∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ),
                (literalH A N (r * s) z -
                  ∑ q ∈ goldbachHalfOpenPrimes N z (r : ℝ),
                    literalH A N (q * r * s) q) := by
                  apply Finset.sum_congr rfl
                  intro r hr
                  rcases mem_goldbachHalfOpenPrimes_iff.mp hs with ⟨hsPrime, _, _, _⟩
                  rcases mem_goldbachHalfOpenPrimes_iff.mp hr with ⟨hrPrime, _, hzr, hrs⟩
                  have hbuch := literalH_buchstab_interval A N (r * s) hzr
                  have hsum :
                      ∑ q ∈ (siftingPrimes N r).filter (fun q : ℕ => z ≤ (q : ℝ)),
                          literalH (A.filter fun n => r * s ∣ n) N q q =
                        ∑ q ∈ goldbachHalfOpenPrimes N z (r : ℝ),
                          literalH A N (q * r * s) q := by
                    apply Finset.sum_congr rfl
                    intro q hq
                    have hqSift : q ∈ siftingPrimes N r := (Finset.mem_filter.mp hq).1
                    rcases mem_siftingPrimes.mp hqSift with ⟨hqPrime, hqr, _⟩
                    have hqrNat : q < r := by exact_mod_cast hqr
                    have hrsNat : r < s := by exact_mod_cast hrs
                    have hqsNat : q < s := lt_trans hqrNat hrsNat
                    have hqrcop : Nat.Coprime q r :=
                      (Nat.coprime_primes hqPrime hrPrime).mpr (ne_of_lt hqrNat)
                    have hqscop : Nat.Coprime q s :=
                      (Nat.coprime_primes hqPrime hsPrime).mpr (ne_of_lt hqsNat)
                    have hqrs : Nat.Coprime (r * s) q := by
                      rw [Nat.coprime_mul_iff_left]
                      exact ⟨hqrcop.symm, hqscop.symm⟩
                    simpa [goldbachHalfOpenPrimes, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
                      literalH_filter_mul_of_coprime A N (r * s) q q hqrs
                  rw [hsum] at hbuch
                  omega
            _ =
              (∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ), literalH A N (r * s) z) -
                ∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ),
                  ∑ q ∈ goldbachHalfOpenPrimes N z (r : ℝ),
                    literalH A N (q * r * s) q := by
                rw [Finset.sum_sub_distrib]
    _ =
      (∑ s ∈ goldbachHalfOpenPrimes N z b,
          ∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ), literalH A N (r * s) z) -
        ∑ s ∈ goldbachHalfOpenPrimes N z b,
          ∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ),
            ∑ q ∈ goldbachHalfOpenPrimes N z (r : ℝ),
              literalH A N (q * r * s) q := by
          rw [Finset.sum_sub_distrib]
    _ = goldbachWeightPStrict A N z b - goldbachWeightA14 A N z b := by
          rfl

private theorem goldbachWeightCrossSlice_eq
    (A : Finset ℕ) (N : ℕ) (z b : ℝ) {t : ℕ}
    (htClosed : t ∈ goldbachClosedPrimes N b (t : ℝ))
    (hzb : z ≤ b) :
    literalH A N t b =
      literalH A N t z -
        (∑ r ∈ goldbachHalfOpenPrimes N z b, literalH A N (r * t) z) +
        ∑ r ∈ goldbachHalfOpenPrimes N z b,
          ∑ s ∈ goldbachHalfOpenPrimes N z (r : ℝ),
            literalH A N (s * r * t) s := by
  rcases mem_goldbachClosedPrimes_iff.mp htClosed with ⟨htPrime, _, hbt, _⟩
  have hbuch := literalH_buchstab_interval A N t hzb
  have hsum1 :
      ∑ r ∈ (siftingPrimes N b).filter (fun r : ℕ => z ≤ (r : ℝ)),
          literalH (A.filter fun n => t ∣ n) N r r =
        ∑ r ∈ goldbachHalfOpenPrimes N z b, literalH A N (r * t) r := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrSift : r ∈ siftingPrimes N b := (Finset.mem_filter.mp hr).1
    rcases mem_siftingPrimes.mp hrSift with ⟨hrPrime, hrb, _⟩
    have hrtReal : (r : ℝ) < t := lt_of_lt_of_le hrb hbt
    have hrtNat : r < t := by exact_mod_cast hrtReal
    have htr : Nat.Coprime t r :=
      (Nat.coprime_primes htPrime hrPrime).mpr (ne_of_gt hrtNat)
    simpa [goldbachHalfOpenPrimes, Nat.mul_comm] using
      literalH_filter_mul_of_coprime A N t r r htr
  rw [hsum1] at hbuch
  have hsum2 :
      ∑ r ∈ goldbachHalfOpenPrimes N z b, literalH A N (r * t) r =
        (∑ r ∈ goldbachHalfOpenPrimes N z b, literalH A N (r * t) z) -
          ∑ r ∈ goldbachHalfOpenPrimes N z b,
            ∑ s ∈ goldbachHalfOpenPrimes N z (r : ℝ),
              literalH A N (s * r * t) s := by
    calc
      ∑ r ∈ goldbachHalfOpenPrimes N z b, literalH A N (r * t) r =
        ∑ r ∈ goldbachHalfOpenPrimes N z b,
          (literalH A N (r * t) z -
            ∑ s ∈ goldbachHalfOpenPrimes N z (r : ℝ),
              literalH A N (s * r * t) s) := by
            apply Finset.sum_congr rfl
            intro r hr
            rcases mem_goldbachHalfOpenPrimes_iff.mp hr with ⟨hrPrime, _, hzr, hrb⟩
            have hbuchr := literalH_buchstab_interval A N (r * t) hzr
            have hsumr :
                ∑ s ∈ (siftingPrimes N r).filter (fun s : ℕ => z ≤ (s : ℝ)),
                    literalH (A.filter fun n => r * t ∣ n) N s s =
                  ∑ s ∈ goldbachHalfOpenPrimes N z (r : ℝ),
                    literalH A N (s * r * t) s := by
              apply Finset.sum_congr rfl
              intro s hs
              have hsSift : s ∈ siftingPrimes N r := (Finset.mem_filter.mp hs).1
              rcases mem_siftingPrimes.mp hsSift with ⟨hsPrime, hsr, _⟩
              have hsrNat : s < r := by exact_mod_cast hsr
              have hstReal : (s : ℝ) < t := lt_of_lt_of_le (lt_trans hsr hrb) hbt
              have hstNat : s < t := by exact_mod_cast hstReal
              have hsrcop : Nat.Coprime s r :=
                (Nat.coprime_primes hsPrime hrPrime).mpr (ne_of_lt hsrNat)
              have hstcop : Nat.Coprime s t :=
                (Nat.coprime_primes hsPrime htPrime).mpr (ne_of_lt hstNat)
              have hsrt : Nat.Coprime (r * t) s := by
                rw [Nat.coprime_mul_iff_left]
                exact ⟨hsrcop.symm, hstcop.symm⟩
              simpa [goldbachHalfOpenPrimes, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
                literalH_filter_mul_of_coprime A N (r * t) s s hsrt
            rw [hsumr] at hbuchr
            omega
      _ =
        (∑ r ∈ goldbachHalfOpenPrimes N z b, literalH A N (r * t) z) -
          ∑ r ∈ goldbachHalfOpenPrimes N z b,
            ∑ s ∈ goldbachHalfOpenPrimes N z (r : ℝ),
              literalH A N (s * r * t) s := by
            rw [Finset.sum_sub_distrib]
  omega

private theorem goldbachS3Closed_split
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ)
    (hzb : z ≤ b) (hbc : b ≤ c) :
    goldbachS3Closed A N z c =
      goldbachS3HalfOpen A N z b +
        ∑ t ∈ goldbachClosedPrimes N b c, literalH A N t z := by
  unfold goldbachS3Closed goldbachS3HalfOpen
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (goldbachClosedPrimes N z c)
      (fun t : ℕ => (t : ℝ) < b)
      (fun t => literalH A N t z)
  rw [goldbachWeightClosedPrimes_filter_lt_eq_halfOpen_of_le N z b c hbc,
    goldbachWeightClosedPrimes_filter_not_lt_eq_closed N z b c hzb] at hsplit
  simpa [not_lt] using hsplit.symm

private theorem goldbachS3Closed_eq_weightCross
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ) (hzb : z ≤ b) :
    goldbachS3Closed A N b c =
      (∑ t ∈ goldbachClosedPrimes N b c, literalH A N t z) -
        goldbachWeightCStrict A N z b c + goldbachWeightA15 A N z b c := by
  unfold goldbachS3Closed goldbachWeightCStrict goldbachWeightA15
  calc
    ∑ t ∈ goldbachClosedPrimes N b c, literalH A N t b =
      ∑ t ∈ goldbachClosedPrimes N b c,
        (literalH A N t z -
          ∑ r ∈ goldbachHalfOpenPrimes N z b, literalH A N (r * t) z +
          ∑ r ∈ goldbachHalfOpenPrimes N z b,
            ∑ s ∈ goldbachHalfOpenPrimes N z (r : ℝ),
              literalH A N (s * r * t) s) := by
          apply Finset.sum_congr rfl
          intro t ht
          have htClosed : t ∈ goldbachClosedPrimes N b (t : ℝ) := by
            rcases mem_goldbachClosedPrimes_iff.mp ht with ⟨htPrime, htN, hbt, _⟩
            exact mem_goldbachClosedPrimes_iff.mpr ⟨htPrime, htN, hbt, le_rfl⟩
          exact goldbachWeightCrossSlice_eq A N z b htClosed hzb
    _ =
      (∑ t ∈ goldbachClosedPrimes N b c, literalH A N t z) -
        ∑ t ∈ goldbachClosedPrimes N b c,
          ∑ r ∈ goldbachHalfOpenPrimes N z b, literalH A N (r * t) z +
        ∑ t ∈ goldbachClosedPrimes N b c,
          ∑ r ∈ goldbachHalfOpenPrimes N z b,
            ∑ s ∈ goldbachHalfOpenPrimes N z (r : ℝ),
              literalH A N (s * r * t) s := by
          simp_rw [sub_eq_add_neg]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = (∑ t ∈ goldbachClosedPrimes N b c, literalH A N t z) -
          goldbachWeightCStrict A N z b c + goldbachWeightA15 A N z b c := by
          rfl

theorem goldbachWeightD6_nonneg (A : Finset ℕ) (N : ℕ) (z b : ℝ) :
    0 ≤ goldbachWeightD6 A N z b := by
  unfold goldbachWeightD6
  refine Finset.sum_nonneg ?_
  intro r hr
  exact literalH_nonneg A N (r ^ 2) z

theorem goldbachWeightB6pair_nonneg (A : Finset ℕ) (N : ℕ) (z b : ℝ) :
    0 ≤ goldbachWeightB6pair A N z b := by
  unfold goldbachWeightB6pair
  refine Finset.sum_nonneg ?_
  intro s hs
  refine Finset.sum_nonneg ?_
  intro r hr
  exact literalH_nonneg A N (r * s) z

theorem goldbachWeightB7_nonneg (A : Finset ℕ) (N : ℕ) (z b c : ℝ) :
    0 ≤ goldbachWeightB7 A N z b c := by
  unfold goldbachWeightB7
  refine Finset.sum_nonneg ?_
  intro t ht
  refine Finset.sum_nonneg ?_
  intro r hr
  exact literalH_nonneg A N (r * t) z

private theorem goldbachWeightG6_eq_goldbachWeightPStrict_add_goldbachWeightD6_add_goldbachWeightB6pair
    (A : Finset ℕ) (N : ℕ) (z b : ℝ) :
    goldbachWeightG6 A N z b =
      goldbachWeightPStrict A N z b + goldbachWeightD6 A N z b + goldbachWeightB6pair A N z b := by
  unfold goldbachWeightG6 goldbachWeightB6pair goldbachWeightPStrict goldbachWeightD6
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (goldbachClosedPrimes N z b)
      (fun s : ℕ => (s : ℝ) < b)
      (fun s =>
        ∑ r ∈ goldbachClosedPrimes N z (s : ℝ), literalH A N (r * s) z)
  rw [goldbachWeightClosedPrimes_filter_lt_eq_halfOpen] at hsplit
  have hslices :
      ∑ s ∈ goldbachHalfOpenPrimes N z b,
          ∑ r ∈ goldbachClosedPrimes N z (s : ℝ), literalH A N (r * s) z =
        ∑ s ∈ goldbachHalfOpenPrimes N z b,
          ((∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ), literalH A N (r * s) z) +
            literalH A N (s ^ 2) z) := by
    apply Finset.sum_congr rfl
    intro s hs
    have hsClosed : s ∈ goldbachClosedPrimes N z (s : ℝ) := by
      rcases mem_goldbachHalfOpenPrimes_iff.mp hs with ⟨hsPrime, hsN, hzs, _⟩
      exact mem_goldbachClosedPrimes_iff.mpr ⟨hsPrime, hsN, hzs, le_rfl⟩
    exact goldbachWeightClosedPairSlice_eq A N z hsClosed
  calc
    ∑ s ∈ goldbachClosedPrimes N z b,
        ∑ r ∈ goldbachClosedPrimes N z (s : ℝ), literalH A N (r * s) z =
      (∑ s ∈ goldbachHalfOpenPrimes N z b,
          ∑ r ∈ goldbachClosedPrimes N z (s : ℝ), literalH A N (r * s) z) +
        ∑ s ∈ (goldbachClosedPrimes N z b).filter (fun s : ℕ => b ≤ (s : ℝ)),
          ∑ r ∈ goldbachClosedPrimes N z (s : ℝ), literalH A N (r * s) z := by
          simpa [not_lt] using hsplit.symm
    _ =
      (∑ s ∈ goldbachHalfOpenPrimes N z b,
          ((∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ), literalH A N (r * s) z) +
            literalH A N (s ^ 2) z)) +
        ∑ s ∈ (goldbachClosedPrimes N z b).filter (fun s : ℕ => b ≤ (s : ℝ)),
          ∑ r ∈ goldbachClosedPrimes N z (s : ℝ), literalH A N (r * s) z := by
          rw [hslices]
    _ =
      ((∑ s ∈ goldbachHalfOpenPrimes N z b,
          ∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ), literalH A N (r * s) z) +
        ∑ s ∈ goldbachHalfOpenPrimes N z b, literalH A N (s ^ 2) z) +
        ∑ s ∈ (goldbachClosedPrimes N z b).filter (fun s : ℕ => b ≤ (s : ℝ)),
          ∑ r ∈ goldbachClosedPrimes N z (s : ℝ), literalH A N (r * s) z := by
          rw [Finset.sum_add_distrib]
    _ =
      goldbachWeightPStrict A N z b + goldbachWeightD6 A N z b + goldbachWeightB6pair A N z b := by
          rfl

private theorem goldbachWeightG7_eq_goldbachWeightCStrict_add_goldbachWeightB7
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ) :
    goldbachWeightG7 A N z b c =
      goldbachWeightCStrict A N z b c + goldbachWeightB7 A N z b c := by
  unfold goldbachWeightG7 goldbachWeightCStrict goldbachWeightB7
  calc
    ∑ t ∈ goldbachClosedPrimes N b c,
        ∑ r ∈ goldbachClosedPrimes N z b, literalH A N (r * t) z =
      ∑ t ∈ goldbachClosedPrimes N b c,
        ((∑ r ∈ goldbachHalfOpenPrimes N z b, literalH A N (r * t) z) +
          ∑ r ∈ (goldbachClosedPrimes N z b).filter (fun r : ℕ => b ≤ (r : ℝ)),
            literalH A N (r * t) z) := by
          apply Finset.sum_congr rfl
          intro t ht
          have hsplit :=
            Finset.sum_filter_add_sum_filter_not
              (goldbachClosedPrimes N z b)
              (fun r : ℕ => (r : ℝ) < b)
              (fun r => literalH A N (r * t) z)
          rw [goldbachWeightClosedPrimes_filter_lt_eq_halfOpen] at hsplit
          simpa [not_lt] using hsplit.symm
    _ =
      (∑ t ∈ goldbachClosedPrimes N b c,
          ∑ r ∈ goldbachHalfOpenPrimes N z b, literalH A N (r * t) z) +
        ∑ t ∈ goldbachClosedPrimes N b c,
          ∑ r ∈ (goldbachClosedPrimes N z b).filter (fun r : ℕ => b ≤ (r : ℝ)),
            literalH A N (r * t) z := by
          rw [Finset.sum_add_distrib]
    _ = goldbachWeightCStrict A N z b c + goldbachWeightB7 A N z b c := by
          rfl

private theorem goldbachWeightA14_le_goldbachWeightG14
    (A : Finset ℕ) (N : ℕ) (z b : ℝ) :
    goldbachWeightA14 A N z b ≤ goldbachWeightG14 A N z b := by
  unfold goldbachWeightA14 goldbachWeightG14
  calc
    ∑ t ∈ goldbachHalfOpenPrimes N z b,
        ∑ s ∈ goldbachHalfOpenPrimes N z (t : ℝ),
          ∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ),
            literalH A N (r * s * t) r
      ≤
    ∑ t ∈ goldbachClosedPrimes N z b,
        ∑ s ∈ goldbachHalfOpenPrimes N z (t : ℝ),
          ∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ),
            literalH A N (r * s * t) r := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (goldbachHalfOpenPrimes_subset_closed N z b) ?_
        intro t ht htnot
        refine Finset.sum_nonneg ?_
        intro s hs
        refine Finset.sum_nonneg ?_
        intro r hr
        exact literalH_nonneg A N (r * s * t) r
    _ ≤
      ∑ t ∈ goldbachClosedPrimes N z b,
          ∑ s ∈ goldbachClosedPrimes N z (t : ℝ),
            ∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ),
              literalH A N (r * s * t) r := by
        refine Finset.sum_le_sum ?_
        intro t ht
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (goldbachHalfOpenPrimes_subset_closed N z (t : ℝ)) ?_
        intro s hs hsnot
        refine Finset.sum_nonneg ?_
        intro r hr
        exact literalH_nonneg A N (r * s * t) r
    _ ≤ goldbachWeightG14 A N z b := by
        refine Finset.sum_le_sum ?_
        intro t ht
        refine Finset.sum_le_sum ?_
        intro s hs
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (goldbachHalfOpenPrimes_subset_closed N z (s : ℝ)) ?_
        intro r hr hrnot
        exact literalH_nonneg A N (r * s * t) r

private theorem goldbachWeightA15_le_goldbachWeightG15
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ) :
    goldbachWeightA15 A N z b c ≤ goldbachWeightG15 A N z b c := by
  unfold goldbachWeightA15 goldbachWeightG15
  refine Finset.sum_le_sum ?_
  intro t ht
  calc
    ∑ s ∈ goldbachHalfOpenPrimes N z b,
        ∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ),
          literalH A N (r * s * t) r
      ≤
    ∑ s ∈ goldbachClosedPrimes N z b,
        ∑ r ∈ goldbachHalfOpenPrimes N z (s : ℝ),
          literalH A N (r * s * t) r := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (goldbachHalfOpenPrimes_subset_closed N z b) ?_
        intro s hs hsnot
        refine Finset.sum_nonneg ?_
        intro r hr
        exact literalH_nonneg A N (r * s * t) r
    _ ≤
      ∑ s ∈ goldbachClosedPrimes N z b,
          ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
            literalH A N (r * s * t) r := by
        refine Finset.sum_le_sum ?_
        intro s hs
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (goldbachHalfOpenPrimes_subset_closed N z (s : ℝ)) ?_
        intro r hr hrnot
        exact literalH_nonneg A N (r * s * t) r

theorem goldbachWeight_initial_refinement
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ)
    (_hz : 2 ≤ z) (hzb : z ≤ b) (hbc : b ≤ c) :
    goldbachS1 A N b - goldbachS3Closed A N b c ≥
      goldbachS1 A N z - goldbachS3Closed A N z c +
        goldbachWeightG6 A N z b + goldbachWeightG7 A N z b c -
        goldbachWeightG14 A N z b - goldbachWeightG15 A N z b c -
        goldbachWeightD6 A N z b - goldbachWeightB6pair A N z b -
        goldbachWeightB7 A N z b c := by
  have hS1 :
      goldbachS1 A N b =
        goldbachS1 A N z - goldbachS3HalfOpen A N z b +
          goldbachWeightPStrict A N z b - goldbachWeightA14 A N z b := by
    rw [goldbachS1_two_buchstab_exact A N hzb]
    rw [goldbachUStrict_eq_goldbachWeightPStrict_sub_goldbachWeightA14]
    ring
  have hSplit :
      goldbachS3Closed A N z c =
        goldbachS3HalfOpen A N z b +
          ∑ t ∈ goldbachClosedPrimes N b c, literalH A N t z :=
    goldbachS3Closed_split A N z b c hzb hbc
  have hS3 :
      goldbachS3Closed A N b c =
        goldbachS3Closed A N z c - goldbachS3HalfOpen A N z b -
          goldbachWeightCStrict A N z b c + goldbachWeightA15 A N z b c := by
    have hCross := goldbachS3Closed_eq_weightCross A N z b c hzb
    omega
  have hG6 :
      goldbachWeightG6 A N z b =
        goldbachWeightPStrict A N z b +
          goldbachWeightD6 A N z b + goldbachWeightB6pair A N z b :=
    goldbachWeightG6_eq_goldbachWeightPStrict_add_goldbachWeightD6_add_goldbachWeightB6pair
      A N z b
  have hG7 :
      goldbachWeightG7 A N z b c =
        goldbachWeightCStrict A N z b c + goldbachWeightB7 A N z b c :=
    goldbachWeightG7_eq_goldbachWeightCStrict_add_goldbachWeightB7 A N z b c
  have hA14 : goldbachWeightA14 A N z b ≤ goldbachWeightG14 A N z b :=
    goldbachWeightA14_le_goldbachWeightG14 A N z b
  have hA15 : goldbachWeightA15 A N z b c ≤ goldbachWeightG15 A N z b c :=
    goldbachWeightA15_le_goldbachWeightG15 A N z b c
  have hMain :
      goldbachS1 A N b - goldbachS3Closed A N b c =
        goldbachS1 A N z - goldbachS3Closed A N z c +
          goldbachWeightG6 A N z b + goldbachWeightG7 A N z b c -
          goldbachWeightA14 A N z b - goldbachWeightA15 A N z b c -
          goldbachWeightD6 A N z b - goldbachWeightB6pair A N z b -
          goldbachWeightB7 A N z b c := by
    omega
  have hzInt : (0 : ℤ) ≤ 0 := by omega
  omega

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig