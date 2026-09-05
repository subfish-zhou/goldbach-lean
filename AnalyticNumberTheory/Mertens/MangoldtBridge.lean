import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Zeta--von Mangoldt bridge for Mertens constants

This module begins the constant-identification workline.  It records the
analytic normalization at `s = 1`; connecting it to hard prime cutoffs is the
remaining Abelian bridge.
-/

namespace AnalyticNumberTheory.Mertens

open Filter Topology Asymptotics

/-- The logarithm of zeta, expressed through the von Mangoldt Dirichlet
series, has the standard normalized `O(s - 1)` behavior at `1` from the
right. -/
theorem zeta_log_vonMangoldt_isBigO :
    (fun s : ℝ =>
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
        ((n : ℝ) ^ s * Real.log n)) + Real.log (s - 1)) =O[𝓝[>] 1]
      fun s => s - 1 := by
  refine log_riemannZeta_add_log_sub_isBigO_ofReal.congr' ?_ .rfl
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  rw [log_riemannZeta_eq hs]

/-- The prime Euler-log expansion of the zeta logarithm.  This is the
analytic prime-side counterpart of the finite product bridge. -/
theorem zeta_euler_log_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    ∑' p : Nat.Primes, -Complex.log
      (1 - (1 : DirichletCharacter ℂ 1) p * (p : ℂ) ^ (-s)) =
      LSeries
        (fun n : ℕ => (1 : DirichletCharacter ℂ 1) n *
          ArithmeticFunction.vonMangoldt n / Real.log n) s :=
  DirichletCharacter.eulerProduct_log_eq_LSeries
    (χ := (1 : DirichletCharacter ℂ 1)) hs

/-- Above the line of absolute convergence, the prime Euler-log series is
summable. -/
theorem summable_zeta_primeEulerLog {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes =>
      -Complex.log (1 - (1 : DirichletCharacter ℂ 1) p * (p : ℂ) ^ (-s)) := by
  exact DirichletCharacter.summable_neg_log_one_sub_mul_prime_cpow
    (χ := (1 : DirichletCharacter ℂ 1)) hs

/-- The prime Dirichlet series is summable in the half-plane `Re(s) > 1`. -/
theorem summable_zeta_primeDirichlet {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes => (p : ℂ) ^ (-s) := by
  refine Summable.of_norm_bounded (g := fun p : Nat.Primes => (p : ℝ) ^ (-s.re))
    (Nat.Primes.summable_rpow.mpr (by linarith)) ?_
  intro p
  change ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ ((p : ℕ) : ℝ) ^ (-s.re)
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  simp

/-- The quadratic-and-higher analytic correction is summable above `Re(s)=1`. -/
theorem summable_zeta_primeEulerCorrection {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes =>
      -Complex.log (1 - (p : ℂ) ^ (-s)) - (p : ℂ) ^ (-s) := by
  refine ((summable_zeta_primeEulerLog hs).sub (summable_zeta_primeDirichlet hs)).congr ?_
  intro p
  rw [MulChar.one_apply (isUnit_of_subsingleton _)]
  ring

/-- Algebraic decomposition of the Euler-log summand into its prime Dirichlet
term and its quadratic-and-higher correction.  Summability is kept explicit:
establishing it uniformly as `s → 1⁺` is part of the Abelian workline. -/
theorem primeEulerLog_tsum_decomposition {s : ℂ}
    (hprime : Summable fun p : Nat.Primes => (p : ℂ) ^ (-s))
    (hcorrection : Summable fun p : Nat.Primes =>
      -Complex.log (1 - (p : ℂ) ^ (-s)) - (p : ℂ) ^ (-s)) :
    ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s)) =
      (∑' p : Nat.Primes, (p : ℂ) ^ (-s)) +
        ∑' p : Nat.Primes,
          (-Complex.log (1 - (p : ℂ) ^ (-s)) - (p : ℂ) ^ (-s)) := by
  rw [← hprime.tsum_add hcorrection]
  apply tsum_congr
  intro p
  ring

/-- Unconditional Euler-log decomposition in the half-plane of absolute
convergence. -/
theorem zeta_primeEulerLog_decomposition {s : ℂ} (hs : 1 < s.re) :
    ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s)) =
      (∑' p : Nat.Primes, (p : ℂ) ^ (-s)) +
        ∑' p : Nat.Primes,
          (-Complex.log (1 - (p : ℂ) ^ (-s)) - (p : ℂ) ^ (-s)) :=
  primeEulerLog_tsum_decomposition
    (summable_zeta_primeDirichlet hs)
    (summable_zeta_primeEulerCorrection hs)

/-- Real specialization of the prime Euler-log expansion.  This is the
normalization interface used by the Abelian finite-part argument at `s = 1`.-/
theorem real_primeEulerLog_eq_log_riemannZeta {s : ℝ} (hs : 1 < s) :
    (∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-s))) =
      Real.log (riemannZeta (s : ℂ)).re := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum, log_riemannZeta_eq hs, Complex.ofReal_tsum]
  have h := zeta_euler_log_eq_LSeries (s := (s : ℂ)) (by simpa using hs)
  rw [LSeries_def₀ (by simp)] at h
  calc
    ∑' p : Nat.Primes, (↑(-Real.log (1 - (p : ℝ) ^ (-s))) : ℂ) =
        ∑' p : Nat.Primes, -Complex.log
          (1 - (1 : DirichletCharacter ℂ 1) p * (p : ℂ) ^ (-(s : ℂ))) := by
      apply tsum_congr
      intro p
      have hp0 : (0 : ℝ) ≤ p := by positivity
      have hp1 : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
      have hpow : (p : ℝ) ^ (-s) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
      rw [Complex.ofReal_neg, Complex.ofReal_log (by linarith),
        Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cpow hp0]
      rw [MulChar.one_apply (isUnit_of_subsingleton _)]
      simp
    _ = ∑' n : ℕ,
        (1 : DirichletCharacter ℂ 1) n * ArithmeticFunction.vonMangoldt n /
          Real.log n / (n : ℂ) ^ (s : ℂ) := h
    _ = ∑' n : ℕ,
        (↑(ArithmeticFunction.vonMangoldt n /
          ((n : ℝ) ^ s * Real.log n)) : ℂ) := by
      apply tsum_congr
      intro n
      rw [Complex.ofReal_div, Complex.ofReal_mul,
        Complex.ofReal_cpow (Nat.cast_nonneg n)]
      rw [MulChar.one_apply (isUnit_of_subsingleton _)]
      simp
      ring

end AnalyticNumberTheory.Mertens
