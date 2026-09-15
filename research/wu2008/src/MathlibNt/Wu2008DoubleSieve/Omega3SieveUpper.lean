import MathlibNt.Wu2008DoubleSieve.Omega3SieveIdentity

/-!
# A certified finite upper sieve for the actual switched sequence

Only the aggregate coprime AP residual receives an absolute value. The
missing non-coprime main mass is retained as the separate positive R2.
The exact Rosser density is not replaced by a delta-independent constant.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical
open MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SwitchingPrinciple

theorem omega3GoldbachBoundingSieve_upperErrSum_le {i : ℕ}
    (N D : ℕ) (he : Even N) (δ s t Z : ℝ) (W : Fin i → Finset ℕ) :
    upperErrSum (omega3GoldbachBoundingSieve N he δ s t Z W) D
        (upperRosserWeight (ordinarySievePrimeProduct N Z) D) ≤
      omega3SieveR1 N D δ s t Z W + omega3SieveR2 N D δ s t Z W := by
  unfold upperErrSum omega3SieveR1 omega3SieveR2
  change (∑ q ∈ omega3SieveModuli N D Z, _) ≤ _
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro q hq
  have hd := (Nat.mem_divisors.mp (mem_filter.mp hq).1).1
  rw [omega3GoldbachBoundingSieve_rem he δ s t Z W hd]
  have hmissing : 0 ≤ omega3SieveMissingMass N δ s t W q / (Nat.totient q : ℝ) :=
    div_nonneg (omega3SieveMissingMass_nonneg N δ s t W q) (Nat.cast_nonneg _)
  have habs :
      |omega3SieveAPResidual N δ s t W q -
        omega3SieveMissingMass N δ s t W q / (Nat.totient q : ℝ)| ≤
      |omega3SieveAPResidual N δ s t W q| +
        omega3SieveMissingMass N δ s t W q / (Nat.totient q : ℝ) := by
    simpa only [abs_of_nonneg hmissing] using
      abs_sub (omega3SieveAPResidual N δ s t W q)
        (omega3SieveMissingMass N δ s t W q / (Nat.totient q : ℝ))
  have hw : |upperRosserWeight (ordinarySievePrimeProduct N Z) D q| ≤
      (3 : ℝ) ^ q.primeFactors.card :=
    (abs_upperRosserWeight_le_one _ _ _).trans (one_le_pow₀ (by norm_num))
  calc
    _ ≤ (3 : ℝ) ^ q.primeFactors.card *
        (|omega3SieveAPResidual N δ s t W q| +
          omega3SieveMissingMass N δ s t W q / (Nat.totient q : ℝ)) :=
      mul_le_mul hw habs (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- The physical finite upper bound. No distribution estimate or
goal-shaped upper-sieve hypothesis is an input. -/
theorem omega3_switched_upper_finite {i N D : ℕ} (he : Even N)
    (δ s t Z : ℝ) (W : Fin i → Finset ℕ)
    (hD : 1 < D) (hZ : Z ≤ (D : ℝ)) :
    omega3SwitchedSiftedCountLE N δ s t Z W ≤
      omega3SieveX N δ s t W * ordinaryRosserMainSum true N 1 D Z +
        omega3SieveR1 N D δ s t Z W + omega3SieveR2 N D δ s t Z W := by
  have hprime : ∀ p ∈ (ordinarySievePrimeProduct N Z).primeFactors, p < D := by
    rw [ordinarySievePrimeProduct_primeFactors]
    intro p hp
    exact_mod_cast (mem_primeWindow.mp hp).2.2.2.trans_le hZ
  have hcert := upperRosserWeight_certificate (ordinarySievePrimeProduct_squarefree N Z)
    (ordinarySievePrimeProduct_pos N Z).ne' hD hprime
  have hfinite := siftedSum_le_mainSum_add_upperErrSum_upperRosser
    (S := omega3GoldbachBoundingSieve N he δ s t Z W) D hcert
  rw [omega3GoldbachBoundingSieve_siftedSum] at hfinite
  change omega3SwitchedSiftedCountLE N δ s t Z W ≤
    omega3SieveX N δ s t W *
      (omega3GoldbachBoundingSieve N he δ s t Z W).mainSum
        (upperRosserWeight (ordinarySievePrimeProduct N Z) D) +
      upperErrSum (omega3GoldbachBoundingSieve N he δ s t Z W) D
        (upperRosserWeight (ordinarySievePrimeProduct N Z) D) at hfinite
  rw [omega3GoldbachBoundingSieve_mainSum] at hfinite
  have herr := omega3GoldbachBoundingSieve_upperErrSum_le N D he δ s t Z W
  change omega3SwitchedSiftedCountLE N δ s t Z W ≤
    omega3SieveX N δ s t W * ordinaryRosserMainSum true N 1 D Z + _ at hfinite
  linarith

theorem omega3_switched_strict_upper_finite {i N D : ℕ} (he : Even N)
    (δ s t Z : ℝ) (W : Fin i → Finset ℕ)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hD : 1 < D) (hZ : Z ≤ (D : ℝ)) :
    omega3SwitchedSiftedCount N δ s t Z W ≤
      omega3SieveX N δ s t W * ordinaryRosserMainSum true N 1 D Z +
        omega3SieveR1 N D δ s t Z W + omega3SieveR2 N D δ s t Z W :=
  (omega3_switched_sifted_le_closed N δ s t Z W hd).trans
    (omega3_switched_upper_finite he δ s t Z W hD hZ)

/-- The frozen uniform upper-density producer is consumed with its true
log-level ratio. The actual X and the two actual residuals remain exposed. -/
theorem omega3_switched_upper_density {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ Z0 : ℝ, ∀ (N : ℕ), Even N → ∀ (i : ℕ) (δ s t Z level r : ℝ)
      (W : Fin i → Finset ℕ),
      Z0 ≤ Z → 2 ≤ Z → 0 < level →
      r = Real.log level / Real.log Z → 3 / 2 ≤ r → r ≤ 4 →
      omega3SwitchedSiftedCountLE N δ s t Z W ≤
        omega3SieveX N δ s t W *
          ((jurkatRichertUpperLinearSieveFactor r + ρ) * localSieveProduct N Z) +
        omega3SieveR1 N (⌊level⌋₊ + 1) δ s t Z W +
        omega3SieveR2 N (⌊level⌋₊ + 1) δ s t Z W := by
  obtain ⟨Z0, hdensity⟩ := ordinaryRosser_upper_density_uniform hρ
  refine ⟨Z0, ?_⟩
  intro N he i δ s t Z level r W hZ0 hZ hl hr hrlo hrhi
  have hlogZ : 0 < Real.log Z := Real.log_pos (by linarith)
  have hratio : 1 ≤ Real.log level / Real.log Z := by rw [← hr]; linarith
  have hlogs : Real.log Z ≤ Real.log level := by
    simpa only [one_mul] using (le_div_iff₀ hlogZ).mp hratio
  have hZl : Z ≤ level := (Real.log_le_log_iff (by linarith) hl).mp hlogs
  have hlD : level < (⌊level⌋₊ + 1 : ℕ) := by
    exact_mod_cast Nat.lt_floor_add_one level
  have hZD : Z ≤ (⌊level⌋₊ + 1 : ℕ) := hZl.trans hlD.le
  have hD : 1 < ⌊level⌋₊ + 1 := by
    exact_mod_cast (show (1 : ℝ) < (⌊level⌋₊ + 1 : ℕ) by linarith)
  have hd := hdensity N 1 he Z level r hZ0 hZ hl hr hrlo hrhi
  simp only [one_mul, ← localSievePrimes_eq_primeWindow] at hd
  change ordinaryRosserMainSum true N 1 (⌊level⌋₊ + 1) Z ≤
    (jurkatRichertUpperLinearSieveFactor r + ρ) * localSieveProduct N Z at hd
  have hmain := mul_le_mul_of_nonneg_left hd (omega3SieveX_nonneg N δ s t W)
  have hfinite := omega3_switched_upper_finite he δ s t Z W hD hZD
  linarith

/-- In particular ep=N is not discarded: zero survives precisely when
the sifting product is one. -/
theorem omega3_sifted_zero_iff (N : ℕ) (Z : ℝ) :
    Sifted N 0 Z ↔ ordinarySievePrimeProduct N Z = 1 := by
  rw [sifted_iff_product_coprime]
  simp

end Wu2008DoubleSieve
