import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryPrimeSWFamily
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPayZero
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPayMainUniform
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPaySecondaryScalar
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPrefixAssembly
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectErrorScalar


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


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
