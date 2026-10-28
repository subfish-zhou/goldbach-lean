import PrimeNumberTheoremAnd.MediumPNTQualitativeBridge
import PrimeNumberTheoremAnd.MediumPNT

/-!
# Prime-distribution API

This module is the stable facade over the ported PNTAnd implementation.
-/

namespace AnalyticNumberTheory.PrimeDistribution

open Asymptotics Filter Real
open scoped Chebyshev

/-- A medium-strength prime number theorem for Chebyshev's psi function. -/
theorem chebyshevPsi_medium_error :
    ∃ c > 0,
      (Chebyshev.psi - id) =O[atTop]
        fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 10)) :=
  MediumPNT

/-- The prime-counting PNT in the real-variable normal form proved by PNTAnd. -/
theorem primeCounting_asymptotic_real :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ,
        Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x :=
  pi_alt

/-- A natural-number interface for the prime-counting PNT. -/
def NatPrimeCountingPNT : Prop :=
  ∃ c : ℕ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
    ∀ x : ℕ,
      (Nat.primeCounting x : ℝ) = (1 + c x) * (x : ℝ) / log x

/-- Restrict the real-variable prime-counting PNT to natural arguments. -/
theorem natPrimeCountingPNT : NatPrimeCountingPNT := by
  obtain ⟨c, hc, hcount⟩ := primeCounting_asymptotic_real
  refine ⟨fun n => c n, hc.comp_tendsto tendsto_natCast_atTop_atTop, ?_⟩
  intro n
  simpa using hcount (n : ℝ)

/-- **Upper bound for π**: Chebyshev's estimate supplies a constant such that
`π(x) ≤ C·x/log x` uniformly for `x ≥ 2`. This gives the analytic
bound `≤ C·N/(a·log(N/a))` for `switchingCount ≤ π(N/a)`
in the three-factor main-term estimate. -/
theorem primeCounting_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 2 ≤ x →
      (Nat.primeCounting x : ℝ) ≤ C * (x : ℝ) / log (x : ℝ) := by
  refine ⟨2 * log 4 + 2, ?_, ?_⟩
  · have h4 : 0 < log (4 : ℝ) := Real.log_pos (by norm_num)
    linarith
  · intro x hx
    have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
    have hx0 : (0 : ℝ) ≤ x := by positivity
    have hlog : 0 < log (x : ℝ) := Real.log_pos hx1
    have hlog_le : log (x : ℝ) ≤ 2 * sqrt (x : ℝ) := by
      simpa [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm] using
        (Real.log_le_rpow_div (x := (x : ℝ)) (ε := 1 / 2) hx0 (by norm_num))
    have hsqrt : sqrt (x : ℝ) * log (x : ℝ) ≤ 2 * (x : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hlog_le (Real.sqrt_nonneg (x : ℝ)),
        Real.sq_sqrt hx0]
    have hpi := Chebyshev.pi_le_log4_mul_div hx1
    simp only [Nat.floor_natCast, Real.log_sqrt hx0] at hpi
    apply (le_div_iff₀ hlog).2
    calc
      (Nat.primeCounting x : ℝ) * log (x : ℝ) ≤
          (log 4 * (x : ℝ) / (log (x : ℝ) / 2) + sqrt (x : ℝ)) * log (x : ℝ) :=
        mul_le_mul_of_nonneg_right hpi hlog.le
      _ = 2 * log 4 * (x : ℝ) + sqrt (x : ℝ) * log (x : ℝ) := by
        field_simp [hlog.ne']
      _ ≤ (2 * log 4 + 2) * (x : ℝ) := by nlinarith only [hsqrt]

end AnalyticNumberTheory.PrimeDistribution
