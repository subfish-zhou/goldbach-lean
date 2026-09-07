import MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier
import MathlibNt.SieveTheory.LiLiuGoldbachClosedTriples

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open MathlibNt.SieveTheory.BombieriVinogradov

/-- The genuine difference carrier conditioned by divisibility by `p`;
the sieve still acts on `n`, not on `n / p`. -/
noncomputable def goldbachS3BoundingSieve
    (N : ℕ) (hEven : Even N) (ε z : ℝ) (p : ℕ) : BoundingSieve :=
  { goldbachS1BoundingSieve N hEven ε z with
    support := (goldbachDifferenceCarrier N ε).filter (fun n => p ∣ n)
    totalMass := trueLogarithmicIntegral (goldbachS1Endpoint N ε) / Nat.totient p }

theorem goldbachS3_coprime_of_dvd_prodPrimes
    {N p d : ℕ} {z y : ℝ} (hp : p ∈ goldbachClosedPrimes N z y)
    (hd : d ∣ goldbachS1ProdPrimes N z) : Nat.Coprime p d := by
  rcases mem_goldbachClosedPrimes_iff.mp hp with ⟨hpp, _, hzp, _⟩
  apply hpp.coprime_iff_not_dvd.mpr
  intro hpd
  have hpz := ((prime_dvd_goldbachS1ProdPrimes_iff hpp).mp (hpd.trans hd)).1
  exact (not_lt_of_ge hzp) hpz

theorem goldbachS3BoundingSieve_siftedSum_eq
    {N : ℕ} (hEven : Even N) (ε z : ℝ) (p : ℕ) :
    (goldbachS3BoundingSieve N hEven ε z p).siftedSum =
      (literalH (goldbachDifferenceCarrier N ε) N p z : ℝ) := by
  classical
  unfold BoundingSieve.siftedSum
  change (∑ n ∈ (goldbachDifferenceCarrier N ε).filter (fun n => p ∣ n),
      if Nat.Coprime (goldbachS1ProdPrimes N z) n then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole]
  have hset :
      ((goldbachDifferenceCarrier N ε).filter (fun n => p ∣ n)).filter
          (fun n => Nat.Coprime (goldbachS1ProdPrimes N z) n) =
        (goldbachDifferenceCarrier N ε).filter (literalHPoint N p z) := by
    ext n
    simp [goldbachS1_coprime_prodPrimes_iff_literalHPoint, literalHPoint, and_assoc]
  rw [hset]
  simp [literalH]

/-- The product-modulus identity is restricted to the coprime sieve support. -/
theorem goldbachS3BoundingSieve_multSum_eq_primesInAP
    {N : ℕ} (hEven : Even N) {ε z y : ℝ} {p d : ℕ}
    (hε : 0 ≤ ε) (hm : 2 ≤ goldbachS1Endpoint N ε)
    (hp : p ∈ goldbachClosedPrimes N z y)
    (hd : d ∣ goldbachS1ProdPrimes N z) :
    (goldbachS3BoundingSieve N hEven ε z p).multSum d =
      (primesInAP (goldbachS1Endpoint N ε) (p * d) (N % (p * d)) : ℝ) := by
  classical
  have hcop := goldbachS3_coprime_of_dvd_prodPrimes hp hd
  rw [← goldbachS1BoundingSieve_multSum_eq_primesInAP
    (hEven := hEven) (z := z) (d := p * d) hε hm]
  unfold BoundingSieve.multSum
  change (∑ n ∈ (goldbachDifferenceCarrier N ε).filter (fun n => p ∣ n),
      if d ∣ n then (1 : ℝ) else 0) =
    ∑ n ∈ goldbachDifferenceCarrier N ε, if p * d ∣ n then (1 : ℝ) else 0
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  have hiff : p * d ∣ n ↔ p ∣ n ∧ d ∣ n := by
    constructor
    · intro h
      exact ⟨(dvd_mul_right p d).trans h, (dvd_mul_left d p).trans h⟩
    · rintro ⟨hpn, hdn⟩
      exact (Nat.coprime_iff_isRelPrime.mp hcop).mul_dvd hpn hdn
  simp only [hiff]
  by_cases hpn : p ∣ n <;> simp [hpn]

theorem goldbachS3BoundingSieve_mainSum_eq_totientSum
    {N : ℕ} (hEven : Even N) (ε z : ℝ) (p : ℕ) (μ : ℕ → ℝ) :
    (goldbachS3BoundingSieve N hEven ε z p).mainSum μ =
      ∑ d ∈ (goldbachS1ProdPrimes N z).divisors, μ d / Nat.totient d := by
  exact goldbachS1BoundingSieve_mainSum_eq_totientSum hEven ε z μ

theorem goldbachS3BoundingSieve_rem_eq_standardPrimeAPError
    {N : ℕ} (hEven : Even N) {ε z y : ℝ} {p d : ℕ}
    (hε : 0 ≤ ε) (hm : 2 ≤ goldbachS1Endpoint N ε)
    (hp : p ∈ goldbachClosedPrimes N z y)
    (hd : d ∣ goldbachS1ProdPrimes N z) :
    (goldbachS3BoundingSieve N hEven ε z p).rem d =
      standardPrimeAPError (goldbachS1Endpoint N ε) (p * d) (N % (p * d)) := by
  have hcop := goldbachS3_coprime_of_dvd_prodPrimes hp hd
  unfold BoundingSieve.rem
  rw [goldbachS3BoundingSieve_multSum_eq_primesInAP hEven hε hm hp hd]
  have hnu : (goldbachS3BoundingSieve N hEven ε z p).nu d =
      (1 : ℝ) / Nat.totient d :=
    goldbachS1BoundingSieve_nu_eq_inv_totient (ε := ε) hEven hd
  rw [hnu]
  simp only [goldbachS3BoundingSieve, standardPrimeAPError,
    Nat.totient_mul hcop, Nat.cast_mul]
  ring

theorem goldbachS3_mod_mem_unitResidues
    {N p d : ℕ} {z y : ℝ} (hp : p ∈ goldbachClosedPrimes N z y)
    (hd : d ∣ goldbachS1ProdPrimes N z) :
    N % (p * d) ∈ AnalyticNumberTheory.Sieve.unitResidues (p * d) := by
  rcases mem_goldbachClosedPrimes_iff.mp hp with ⟨hpp, hpN, _, _⟩
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (goldbachS1ProdPrimes_ne_zero N z) hd
  have hcop : Nat.Coprime (p * d) N :=
    (hpp.coprime_iff_not_dvd.mpr hpN).mul_left (goldbachS1_dvd_prodPrimes_coprime_N hd)
  rw [AnalyticNumberTheory.Sieve.unitResidues]
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.mod_lt N (Nat.mul_pos hpp.pos (Nat.pos_of_ne_zero hd0))),
      (ZMod.coprime_mod_iff_coprime N (p * d)).2 hcop.symm⟩

theorem goldbachS3BoundingSieve_abs_rem_le_prefix
    {N : ℕ} (hEven : Even N) {ε z y : ℝ} {p d : ℕ}
    (hε : 0 ≤ ε) (hm : 2 ≤ goldbachS1Endpoint N ε)
    (hp : p ∈ goldbachClosedPrimes N z y)
    (hd : d ∣ goldbachS1ProdPrimes N z) :
    |(goldbachS3BoundingSieve N hEven ε z p).rem d| ≤
      standardPrimeAPPrefixMaxError N (p * d) := by
  classical
  rw [goldbachS3BoundingSieve_rem_eq_standardPrimeAPError hEven hε hm hp hd]
  refine (abs_standardPrimeAPError_le_max (goldbachS3_mod_mem_unitResidues hp hd)).trans ?_
  unfold standardPrimeAPPrefixMaxError
  exact Finset.le_max'
    ((range (N + 1)).image (fun m => standardPrimeAPMaxError m (p * d))) _
    (Finset.mem_image.mpr ⟨goldbachS1Endpoint N ε,
      Finset.mem_range.mpr (Nat.lt_succ_of_le (goldbachS1Endpoint_le N hε)), rfl⟩)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig