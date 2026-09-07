import MathlibNt.SieveTheory.LiLiuGoldbachS3Carrier

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open MathlibNt.SieveTheory.BombieriVinogradov

/-! Composite outer-modulus bridges for the original S3 sieve.
No new carrier, center, or sieve record is introduced. -/

theorem goldbachCompositeSieve_multSum_eq_primesInAP
    {N : ℕ} (hEven : Even N) {ε z : ℝ} {k d : ℕ}
    (hε : 0 ≤ ε) (hm : 2 ≤ goldbachS1Endpoint N ε)
    (hkd : Nat.Coprime k d) :
    (goldbachS3BoundingSieve N hEven ε z k).multSum d =
      (primesInAP (goldbachS1Endpoint N ε) (k * d) (N % (k * d)) : ℝ) := by
  classical
  rw [← goldbachS1BoundingSieve_multSum_eq_primesInAP
    (hEven := hEven) (z := z) (d := k * d) hε hm]
  unfold BoundingSieve.multSum
  change (∑ n ∈ (goldbachDifferenceCarrier N ε).filter (fun n => k ∣ n),
      if d ∣ n then (1 : ℝ) else 0) =
    ∑ n ∈ goldbachDifferenceCarrier N ε, if k * d ∣ n then (1 : ℝ) else 0
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  have hiff : k * d ∣ n ↔ k ∣ n ∧ d ∣ n := by
    constructor
    · intro h
      exact ⟨(dvd_mul_right k d).trans h, (dvd_mul_left d k).trans h⟩
    · rintro ⟨hkn, hdn⟩
      exact (Nat.coprime_iff_isRelPrime.mp hkd).mul_dvd hkn hdn
  simp only [hiff]
  by_cases hkn : k ∣ n <;> simp [hkn]

theorem goldbachCompositeSieve_rem_eq_standardPrimeAPError
    {N : ℕ} (hEven : Even N) {ε z : ℝ} {k d : ℕ}
    (hε : 0 ≤ ε) (hm : 2 ≤ goldbachS1Endpoint N ε)
    (hkd : Nat.Coprime k d) (hd : d ∣ goldbachS1ProdPrimes N z) :
    (goldbachS3BoundingSieve N hEven ε z k).rem d =
      standardPrimeAPError (goldbachS1Endpoint N ε) (k * d) (N % (k * d)) := by
  unfold BoundingSieve.rem
  rw [goldbachCompositeSieve_multSum_eq_primesInAP hEven hε hm hkd]
  have hnu : (goldbachS3BoundingSieve N hEven ε z k).nu d =
      (1 : ℝ) / Nat.totient d :=
    goldbachS1BoundingSieve_nu_eq_inv_totient (ε := ε) hEven hd
  rw [hnu]
  simp only [goldbachS3BoundingSieve, standardPrimeAPError,
    Nat.totient_mul hkd, Nat.cast_mul]
  ring

theorem goldbachCompositeSieve_mod_mem_unitResidues
    {N k d : ℕ} {z : ℝ} (hk : 0 < k) (hkN : Nat.Coprime k N)
    (hd : d ∣ goldbachS1ProdPrimes N z) :
    N % (k * d) ∈ AnalyticNumberTheory.Sieve.unitResidues (k * d) := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (goldbachS1ProdPrimes_ne_zero N z) hd
  have hcop : Nat.Coprime (k * d) N :=
    hkN.mul_left (goldbachS1_dvd_prodPrimes_coprime_N hd)
  rw [AnalyticNumberTheory.Sieve.unitResidues]
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.mod_lt N (Nat.mul_pos hk (Nat.pos_of_ne_zero hd0))),
      (ZMod.coprime_mod_iff_coprime N (k * d)).2 hcop.symm⟩

theorem goldbachCompositeSieve_abs_rem_le_prefix
    {N : ℕ} (hEven : Even N) {ε z : ℝ} {k d : ℕ}
    (hε : 0 ≤ ε) (hm : 2 ≤ goldbachS1Endpoint N ε)
    (hk : 0 < k) (hkd : Nat.Coprime k d) (hkN : Nat.Coprime k N)
    (hd : d ∣ goldbachS1ProdPrimes N z) :
    |(goldbachS3BoundingSieve N hEven ε z k).rem d| ≤
      standardPrimeAPPrefixMaxError N (k * d) := by
  classical
  rw [goldbachCompositeSieve_rem_eq_standardPrimeAPError hEven hε hm hkd hd]
  refine (abs_standardPrimeAPError_le_max
    (goldbachCompositeSieve_mod_mem_unitResidues hk hkN hd)).trans ?_
  unfold standardPrimeAPPrefixMaxError
  exact Finset.le_max'
    ((range (N + 1)).image (fun m => standardPrimeAPMaxError m (k * d))) _
    (Finset.mem_image.mpr ⟨goldbachS1Endpoint N ε,
      Finset.mem_range.mpr (Nat.lt_succ_of_le (goldbachS1Endpoint_le N hε)), rfl⟩)

/-- Only each outer prime versus the small sieve matters; `r = s` is allowed. -/
theorem goldbachCompositeSieve_pair_coprime_of_dvd_prodPrimes
    {N r s d : ℕ} {z y₁ y₂ : ℝ}
    (hr : r ∈ goldbachClosedPrimes N z y₁)
    (hs : s ∈ goldbachClosedPrimes N z y₂)
    (hd : d ∣ goldbachS1ProdPrimes N z) : Nat.Coprime (r * s) d := by
  exact (goldbachS3_coprime_of_dvd_prodPrimes hr hd).mul_left
    (goldbachS3_coprime_of_dvd_prodPrimes hs hd)

theorem goldbachCompositeSieve_pair_coprime_N
    {N r s : ℕ} {z y₁ y₂ : ℝ}
    (hr : r ∈ goldbachClosedPrimes N z y₁)
    (hs : s ∈ goldbachClosedPrimes N z y₂) : Nat.Coprime (r * s) N := by
  rcases mem_goldbachClosedPrimes_iff.mp hr with ⟨hrp, hrN, _, _⟩
  rcases mem_goldbachClosedPrimes_iff.mp hs with ⟨hsp, hsN, _, _⟩
  exact (hrp.coprime_iff_not_dvd.mpr hrN).mul_left (hsp.coprime_iff_not_dvd.mpr hsN)

theorem goldbachCompositeSieve_pair_rem_eq_standardPrimeAPError
    {N : ℕ} (hEven : Even N) {ε z y₁ y₂ : ℝ} {r s d : ℕ}
    (hε : 0 ≤ ε) (hm : 2 ≤ goldbachS1Endpoint N ε)
    (hr : r ∈ goldbachClosedPrimes N z y₁)
    (hs : s ∈ goldbachClosedPrimes N z y₂)
    (hd : d ∣ goldbachS1ProdPrimes N z) :
    (goldbachS3BoundingSieve N hEven ε z (r * s)).rem d =
      standardPrimeAPError (goldbachS1Endpoint N ε) ((r * s) * d)
        (N % ((r * s) * d)) := by
  exact goldbachCompositeSieve_rem_eq_standardPrimeAPError hEven hε hm
    (goldbachCompositeSieve_pair_coprime_of_dvd_prodPrimes hr hs hd) hd

theorem goldbachCompositeSieve_pair_abs_rem_le_prefix
    {N : ℕ} (hEven : Even N) {ε z y₁ y₂ : ℝ} {r s d : ℕ}
    (hε : 0 ≤ ε) (hm : 2 ≤ goldbachS1Endpoint N ε)
    (hr : r ∈ goldbachClosedPrimes N z y₁)
    (hs : s ∈ goldbachClosedPrimes N z y₂)
    (hd : d ∣ goldbachS1ProdPrimes N z) :
    |(goldbachS3BoundingSieve N hEven ε z (r * s)).rem d| ≤
      standardPrimeAPPrefixMaxError N ((r * s) * d) := by
  exact goldbachCompositeSieve_abs_rem_le_prefix hEven hε hm
    (Nat.mul_pos (mem_goldbachClosedPrimes_iff.mp hr).1.pos
      (mem_goldbachClosedPrimes_iff.mp hs).1.pos)
    (goldbachCompositeSieve_pair_coprime_of_dvd_prodPrimes hr hs hd)
    (goldbachCompositeSieve_pair_coprime_N hr hs) hd

/-- The diagonal keeps `φ(r²)`, not `φ(r)²`. -/
theorem goldbachCompositeSieve_square_rem_eq
    {N : ℕ} (hEven : Even N) {ε z y : ℝ} {r d : ℕ}
    (hε : 0 ≤ ε) (hm : 2 ≤ goldbachS1Endpoint N ε)
    (hr : r ∈ goldbachClosedPrimes N z y)
    (hd : d ∣ goldbachS1ProdPrimes N z) :
    (goldbachS3BoundingSieve N hEven ε z (r ^ 2)).rem d =
      (primesInAP (goldbachS1Endpoint N ε) (r ^ 2 * d) (N % (r ^ 2 * d)) : ℝ) -
        trueLogarithmicIntegral (goldbachS1Endpoint N ε) /
          ((Nat.totient (r ^ 2) : ℝ) * Nat.totient d) := by
  have hcop : Nat.Coprime (r ^ 2) d := by
    simpa only [pow_two] using
      goldbachCompositeSieve_pair_coprime_of_dvd_prodPrimes hr hr hd
  rw [goldbachCompositeSieve_rem_eq_standardPrimeAPError hEven hε hm hcop hd]
  simp only [standardPrimeAPError, Nat.totient_mul hcop, Nat.cast_mul]

theorem goldbachCompositeSieve_square_abs_rem_le_prefix
    {N : ℕ} (hEven : Even N) {ε z y : ℝ} {r d : ℕ}
    (hε : 0 ≤ ε) (hm : 2 ≤ goldbachS1Endpoint N ε)
    (hr : r ∈ goldbachClosedPrimes N z y)
    (hd : d ∣ goldbachS1ProdPrimes N z) :
    |(goldbachS3BoundingSieve N hEven ε z (r ^ 2)).rem d| ≤
      standardPrimeAPPrefixMaxError N (r ^ 2 * d) := by
  simpa only [pow_two] using
    goldbachCompositeSieve_pair_abs_rem_le_prefix hEven hε hm hr hr hd

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
