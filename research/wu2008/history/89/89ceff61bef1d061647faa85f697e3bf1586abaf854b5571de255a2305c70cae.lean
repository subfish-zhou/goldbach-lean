import MathlibNt.Wu2008DoubleSieve.NinthUpperSieveIdentity
import MathlibNt.Wu2008DoubleSieve.NinthUpperSieveSmallOutput

/-!
# The physical finite T9 upper sieve

The generic Rosser certificate is applied to the actual B9 output weights.
Both the coprime AP error and the noncoprime missing main mass remain
exposed, together with the independently counted small prime outputs.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical
open MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SwitchingPrinciple

theorem ninthBoundingSieve_upperErrSum_le (N D : ℕ) (he : Even N) (Z : ℝ) :
    upperErrSum (ninthBoundingSieve N he Z) D
      (upperRosserWeight (ordinarySievePrimeProduct N Z) D) ≤
        ninthSieveR1 N D Z + ninthSieveR2 N D Z := by
  unfold upperErrSum ninthSieveR1 ninthSieveR2
  change (∑ q ∈ omega3SieveModuli N D Z, _) ≤ _
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro q hq
  have hd := (Nat.mem_divisors.mp (mem_filter.mp hq).1).1
  rw [ninthBoundingSieve_rem he Z hd]
  have hmissing : 0 ≤ ninthSieveMissingMass N q / (Nat.totient q : ℝ) :=
    div_nonneg (ninthSieveMissingMass_nonneg N q) (Nat.cast_nonneg _)
  have habs :
      |ninthSieveAPResidual N q - ninthSieveMissingMass N q / (Nat.totient q : ℝ)| ≤
        |ninthSieveAPResidual N q| + ninthSieveMissingMass N q / (Nat.totient q : ℝ) := by
    simpa only [abs_of_nonneg hmissing] using
      abs_sub (ninthSieveAPResidual N q) (ninthSieveMissingMass N q / (Nat.totient q : ℝ))
  have hw : |upperRosserWeight (ordinarySievePrimeProduct N Z) D q| ≤
      (3 : ℝ) ^ q.primeFactors.card :=
    (abs_upperRosserWeight_le_one _ _ _).trans (one_le_pow₀ (by norm_num))
  calc
    _ ≤ (3 : ℝ) ^ q.primeFactors.card *
        (|ninthSieveAPResidual N q| + ninthSieveMissingMass N q / (Nat.totient q : ℝ)) :=
      mul_le_mul hw habs (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem ninth_sifted_upper_finite {N D : ℕ} (he : Even N) (Z : ℝ)
    (hD : 1 < D) (hZ : Z ≤ (D : ℝ)) :
    ninthSiftedCount N Z ≤ X9 N * ordinaryRosserMainSum true N 1 D Z +
      ninthSieveR1 N D Z + ninthSieveR2 N D Z := by
  have hprime : ∀ p ∈ (ordinarySievePrimeProduct N Z).primeFactors, p < D := by
    rw [ordinarySievePrimeProduct_primeFactors]
    intro p hp
    exact_mod_cast (mem_primeWindow.mp hp).2.2.2.trans_le hZ
  have hcert := upperRosserWeight_certificate (ordinarySievePrimeProduct_squarefree N Z)
    (ordinarySievePrimeProduct_pos N Z).ne' hD hprime
  have hfinite := siftedSum_le_mainSum_add_upperErrSum_upperRosser
    (S := ninthBoundingSieve N he Z) D hcert
  rw [ninthBoundingSieve_siftedSum] at hfinite
  change ninthSiftedCount N Z ≤ X9 N *
    (ninthBoundingSieve N he Z).mainSum
      (upperRosserWeight (ordinarySievePrimeProduct N Z) D) +
        upperErrSum (ninthBoundingSieve N he Z) D
          (upperRosserWeight (ordinarySievePrimeProduct N Z) D) at hfinite
  rw [ninthBoundingSieve_mainSum] at hfinite
  have herr := ninthBoundingSieve_upperErrSum_le N D he Z
  linarith

/-- The actual finite T9 upper sieve, not a wrapper assuming that sieve.
No lower bound on Z is needed for this finite statement. -/
theorem T9_upper_finite {N D : ℕ} (hN : 512 ≤ N) (he : Even N) (Z : ℝ)
    (hD : 1 < D) (hZ : Z ≤ (D : ℝ)) :
    ((T9 N (ninthProfileW N) (ninthProfileU N)).card : ℝ) ≤
      X9 N * ordinaryRosserMainSum true N 1 D Z +
        ninthSieveR1 N D Z + ninthSieveR2 N D Z + ninthSmallOutputBudget Z := by
  have hcount := T9_card_le_sifted_add_small hN he Z
  have hsieve := ninth_sifted_upper_finite he Z hD hZ
  linarith

end Wu2008DoubleSieve
