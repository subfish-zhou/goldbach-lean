import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergUniformEuler

open MathlibNt.SieveTheory.LiuWeight
-- New unconditional statements.
example (N : ℕ) (p : Nat.Primes) : 0 ≤ liuSelbergAbsPrimeDeviation N p :=
  liuSelbergAbsPrimeDeviation_nonneg_core (N := N) p
example (N : ℕ) (p : Nat.Primes) : 0 ≤ liuSelbergAbsPrimeDeviation N p :=
  liuSelbergAbsPrimeDeviation_nonneg (N := N) p
example (N : ℕ) (p : Nat.Primes) : 1 ≤ liuAbsoluteEulerFactor N p :=
  liuAbsoluteEulerFactor_one_le (N := N) p
-- Original statements remain consequences, with the same quantifier order.
example {N : ℕ} (_hNeven : Even N) (p : Nat.Primes) :
    0 ≤ liuSelbergAbsPrimeDeviation N p :=
  liuSelbergAbsPrimeDeviation_nonneg_core (N := N) p
example {N : ℕ} (_hNeven : Even N) (p : Nat.Primes) :
    0 ≤ liuSelbergAbsPrimeDeviation N p :=
  liuSelbergAbsPrimeDeviation_nonneg (N := N) p
example {N : ℕ} (_hNeven : Even N) (p : Nat.Primes) :
    1 ≤ liuAbsoluteEulerFactor N p :=
  liuAbsoluteEulerFactor_one_le (N := N) p
