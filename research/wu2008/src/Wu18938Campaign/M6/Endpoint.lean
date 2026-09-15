import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Wu18938Campaign.M6

theorem prime_ne_tenthRoot {N p : ℕ} (hp : p.Prime) (hc : p.Coprime N) :
    (p : ℝ) ≠ (N : ℝ) ^ (1 / 10 : ℝ) := by
  intro h
  have hpow : (p : ℝ) ^ (10 : ℕ) = (N : ℝ) := by
    rw [h, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  have hN : p ^ 10 = N := by exact_mod_cast hpow
  apply (hp.coprime_iff_not_dvd.mp hc)
  refine ⟨p ^ 9, ?_⟩
  rw [← hN, pow_succ]
  ring

theorem prime_le_tenthRoot_iff_lt {N p : ℕ} (hp : p.Prime) (hc : p.Coprime N) :
    (p : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) ↔
      (p : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ) :=
  ⟨fun h => lt_of_le_of_ne h (prime_ne_tenthRoot hp hc), le_of_lt⟩

theorem tenthRoot_le_prime_iff_lt {N p : ℕ} (hp : p.Prime) (hc : p.Coprime N) :
    (N : ℝ) ^ (1 / 10 : ℝ) ≤ (p : ℝ) ↔
      (N : ℝ) ^ (1 / 10 : ℝ) < (p : ℝ) :=
  ⟨fun h => lt_of_le_of_ne h (prime_ne_tenthRoot hp hc).symm, le_of_lt⟩

end Wu18938Campaign.M6
