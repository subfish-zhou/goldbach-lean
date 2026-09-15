import PrimeNumberTheoremAnd.Consequences
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

/-- **Upper bound for π**: the PNT supplies a constant such that
`π(x) ≤ C·x/log x` uniformly for `x ≥ 2`. This gives the analytic
bound `≤ C·N/(a·log(N/a))` for `switchingCount ≤ π(N/a)`
in the three-factor main-term estimate. -/
theorem primeCounting_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 2 ≤ x →
      (Nat.primeCounting x : ℝ) ≤ C * (x : ℝ) / log (x : ℝ) := by
  obtain ⟨c, hc, hcount⟩ := natPrimeCountingPNT
  obtain ⟨C₀, hC₀ev⟩ := (hc.isBigO).bound
  rcases Filter.eventually_atTop.mp hC₀ev with ⟨X₀, hX₀⟩
  let C₀b : ℝ := max C₀ 1
  have hC0b : 1 ≤ C₀b := by
    dsimp [C₀b]
    exact le_max_right _ _
  let X : ℕ := max X₀ 2
  let C : ℝ := max (1 + C₀b) (2 * log (X : ℝ))
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    have h1 : 0 < 1 + C₀b := by linarith
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  · intro x hx
    by_cases hxbig : X ≤ x
    · have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
      have hlog : 0 < log (x : ℝ) := Real.log_pos hx1
      have hcx : |c x| ≤ C₀b := by
        have h0 : |c x| ≤ C₀ := by
          simpa using hX₀ x (le_trans (le_max_left X₀ 2) hxbig)
        exact le_trans h0 (le_max_left _ _)
      have hmain : (Nat.primeCounting x : ℝ) ≤ (1 + C₀b) * (x : ℝ) / log (x : ℝ) := by
        rw [hcount]
        have hle : 1 + c x ≤ 1 + C₀b := by linarith [le_trans (le_abs_self (c x)) hcx]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hle (by positivity : 0 ≤ (x : ℝ))) (le_of_lt hlog)
      have hC : (1 + C₀b) * (x : ℝ) / log (x : ℝ) ≤ C * (x : ℝ) / log (x : ℝ) := by
        have hC1 : 1 + C₀b ≤ C := by
          dsimp [C]
          exact le_max_left _ _
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC1 (by positivity : 0 ≤ (x : ℝ))) (le_of_lt hlog)
      exact le_trans hmain hC
    · have hxlt : x < X := lt_of_not_ge hxbig
      have hpi : (Nat.primeCounting x : ℝ) ≤ (x : ℝ) + 1 := by
        have hle : Nat.primeCounting x ≤ x + 1 := by
          change Nat.count Nat.Prime (x + 1) ≤ x + 1
          exact Nat.count_le Nat.Prime
        exact_mod_cast hle
      have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
      have hlog : 0 < log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
      have hlogX : 0 < log (X : ℝ) := by
        have hX2 : (2 : ℝ) ≤ X := by exact_mod_cast (le_max_right X₀ 2)
        exact Real.log_pos (by linarith)
      have hlogx_le : log (x : ℝ) ≤ log (X : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (le_of_lt hxlt))
      have hC2 : 2 * log (x : ℝ) ≤ C := by
        dsimp [C]
        calc
          2 * log (x : ℝ) ≤ 2 * log (X : ℝ) := by gcongr
          _ ≤ max (1 + C₀b) (2 * log (X : ℝ)) := le_max_right _ _
      calc
        (Nat.primeCounting x : ℝ) ≤ (x : ℝ) + 1 := hpi
        _ ≤ 2 * (x : ℝ) := by linarith
        _ = (2 * log (x : ℝ)) * (x : ℝ) / log (x : ℝ) := by
              field_simp [hlog.ne']
        _ ≤ C * (x : ℝ) / log (x : ℝ) := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hC2 (by positivity : 0 ≤ (x : ℝ))) (le_of_lt hlog)

end AnalyticNumberTheory.PrimeDistribution
