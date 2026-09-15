import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryPrimeSWFamily
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectC2

noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Geometry only: no analytic assertion is stored in the interval index. -/
structure PrimeC2Interval where
  scale : ℝ
  lower : ℝ
  upper : ℝ
  one_le_scale : 1 ≤ scale
  scale_le_lower : scale ≤ lower
  lower_le_upper : lower ≤ upper
  upper_le_twice : upper ≤ 2*scale

theorem primeC2Interval_support (z : PrimeC2Interval) :
    ∀ n ∈ primeSWInterval z.lower z.upper,
      z.scale ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*z.scale := by
  intro n hn
  obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hn
  refine ⟨z.scale_le_lower.trans (Nat.lt_of_floor_lt hlo).le, ?_⟩
  exact (Nat.le_floor_iff (by linarith [z.one_le_scale,z.scale_le_lower,z.lower_le_upper])).mp hhi |>.trans z.upper_le_twice

theorem primeSWBeta_le_order_one (n : ℕ) : |primeSWBeta n| ≤ (fouvryTau 1 n : ℝ) := by
  by_cases hp : n.Prime
  · simp [primeSWBeta,hp,fouvryTau_order_one hp.ne_zero]
  · simp [primeSWBeta,hp]

/-- No SW premise: the actual prime-interval producer is consumed here. -/
theorem primeC2_unconditional (i j A : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ z : PrimeC2Interval, ∀ M ν : ℝ,
      1 ≤ M → 4*M*z.scale = x → ε ≤ ν → ν ≤ 1/10 → z.scale = x^ν →
      ∀ U : Finset ℕ, (∀ n ∈ U, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*M) →
      ∀ α c : ℕ → ℝ, (∀ n ∈ U, |α n| ≤ (fouvryTau i n : ℝ)) →
      SignedWellFactorable j (x^((5-5*ν)/9-ε)) c →
      ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ x →
      |signedError U (primeSWInterval z.lower z.upper)
        (Ioc 0 ⌊x^((5-5*ν)/9-ε)⌋₊) α primeSWBeta c a| ≤ x/Real.log x^A := by
  have hSW := primeSW_BetaCoprimeSWFamily PrimeC2Interval.scale
    PrimeC2Interval.lower PrimeC2Interval.upper PrimeC2Interval.one_le_scale
    PrimeC2Interval.scale_le_lower PrimeC2Interval.lower_le_upper PrimeC2Interval.upper_le_twice
  exact direct_wellFactorable_signedError_c2 (i := i) (j := j) (k := 1) A hSW
    PrimeC2Interval.one_le_scale primeC2Interval_support (fun _ n _ => primeSWBeta_le_order_one n) hε

/-- For primes, divisor deletion is exactly the actual Goldbach coprime mask. -/
theorem primeSWBeta_clean_nat (N n : ℕ) :
    betaClean primeSWBeta (N : ℤ) n = if n.Coprime N then primeSWBeta n else 0 := by
  by_cases hp : n.Prime
  · have he : ((n : ℤ) ∣ (N : ℤ)) ↔ ¬n.Coprime N := by
      rw [Int.natCast_dvd_natCast]
      exact hp.dvd_iff_not_coprime
    simp only [betaClean,he]
    by_cases hc : n.Coprime N <;> simp [hc]
  · simp [betaClean,primeSWBeta,hp]

/-- The independent sieve order increases, while all changing residues stay after the constants. -/
theorem primeC2_clean_family {ε : ℝ} (hε : 0 < ε) :
    BetaCoprimeSWFamily 3
      (fun z : BetaCleanIndex PrimeC2Interval.scale ε => z.index.scale)
      (fun z => primeSWInterval z.index.lower z.index.upper)
      (fun z => betaClean primeSWBeta z.residue) := by
  have hSW := primeSW_BetaCoprimeSWFamily PrimeC2Interval.scale
    PrimeC2Interval.lower PrimeC2Interval.upper PrimeC2Interval.one_le_scale
    PrimeC2Interval.scale_le_lower PrimeC2Interval.lower_le_upper PrimeC2Interval.upper_le_twice
  exact hSW.betaClean (k := 1) (fun _ n _ => primeSWBeta_le_order_one n) hε

/-- Concrete cleaned prime intervals feed C.2 without an analytic premise. -/
theorem primeC2_clean_unconditional (i j A : ℕ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ z : BetaCleanIndex PrimeC2Interval.scale δ, ∀ M ν : ℝ,
      1 ≤ M → 4*M*z.index.scale = x → ε ≤ ν → ν ≤ 1/10 → z.index.scale = x^ν →
      ∀ U : Finset ℕ, (∀ n ∈ U, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*M) →
      ∀ α c : ℕ → ℝ, (∀ n ∈ U, |α n| ≤ (fouvryTau i n : ℝ)) →
      SignedWellFactorable j (x^((5-5*ν)/9-ε)) c →
      ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ x →
      |signedError U (primeSWInterval z.index.lower z.index.upper)
        (Ioc 0 ⌊x^((5-5*ν)/9-ε)⌋₊) α (betaClean primeSWBeta z.residue) c a| ≤
        x/Real.log x^A := by
  exact direct_wellFactorable_signedError_c2 (i := i) (j := j) (k := 1) A
    (primeC2_clean_family hδ) (fun z => z.one_le_T)
    (fun z => primeC2Interval_support z.index)
    (fun z n _ => (abs_betaClean_le _ _ _).trans (primeSWBeta_le_order_one n)) hε

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
