import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryR1
import MathlibNt.Wu2008DoubleSieve.ReboxingRepeatedPrimes
import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientIntegralBounds

/-!
# Actual coefficient-weighted lower-boundary payment R3

Wu04 (3.18), source lines 1096--1100 and 1125--1127.
The printed totient denominator and the actual effective coefficients
are retained. The proof also handles the signed lower coefficient.
-/

namespace Wu2008DoubleSieve

open Finset Filter Real
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- On the added lower interval the coefficient parameter can exceed
`t-1`, so its upper bound uses the uniform source mesh condition. -/
theorem reboxingR3_parameter_mem {q D Δ t p : ℝ} {i : ℕ}
    (hq : 1 < q) (hΔ : 1 < Δ) (ht : 2 ≤ t) (ht10 : t ≤ 10)
    (hDlo : q ≤ D) (hDhi : D ≤ q * Δ ^ i)
    (hmesh : 10 * (i : ℝ) * log Δ ≤ log q)
    (hp : q ^ (1 / t) ≤ p) (hp' : p < D ^ (1 / t)) :
    1 ≤ log D / log p - 1 ∧ log D / log p - 1 ≤ 10 := by
  have hq0 : 0 < q := by linarith
  have hD0 : 0 < D := hq0.trans_le hDlo
  have hΔ0 : 0 < Δ := by linarith
  have ht0 : 0 < t := by linarith
  have hp1 : 1 < p := (one_lt_rpow hq (by positivity : 0 < 1 / t)).trans_le hp
  have hLp : 0 < log p := log_pos hp1
  have hlow : log q / t ≤ log p := by
    have hh := log_le_log (rpow_pos_of_pos hq0 _) hp
    rw [log_rpow hq0] at hh
    convert hh using 1
    ring
  have hhigh : log p ≤ log D / t := by
    have hh := log_le_log (by linarith : 0 < p) hp'.le
    rw [log_rpow hD0] at hh
    convert hh using 1
    ring
  have hLD : log D ≤ log q + (i : ℝ) * log Δ := by
    have hh := log_le_log hD0 hDhi
    simpa [log_mul hq0.ne' (pow_pos hΔ0 i).ne', log_pow] using hh
  constructor
  · have hh := (le_div_iff₀ ht0).1 hhigh
    have hratio : 2 ≤ log D / log p := (le_div_iff₀ hLp).2 (by nlinarith)
    linarith
  · have hLq : 0 < log q := log_pos hq
    have hten : log q / 10 ≤ log p :=
      (div_le_div_of_nonneg_left hLq.le ht0 ht10).trans hlow
    have hratio : log D / log p ≤ 11 := (div_le_iff₀ hLp).2 (by nlinarith)
    linarith

theorem reboxing_totient_weight_le_four_div {p : ℕ} {D : ℝ}
    (hp : p.Prime) (hD : 1 < D) (hp4 : (4 : ℝ) ≤ p)
    (hupper : (p : ℝ) ≤ D ^ (1 / 2 : ℝ)) :
    0 ≤ 1 / ((Nat.totient p : ℝ) * (1 - log (p : ℝ) / log D)) ∧
      1 / ((Nat.totient p : ℝ) * (1 - log (p : ℝ) / log D)) ≤ 4 / p := by
  have hgap := reboxing_log_ratio_half hD (by linarith : (0 : ℝ) < p) hupper
  have ht : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  rw [ht]
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  have hgap0 : 0 < 1 - log (p : ℝ) / log D := by linarith
  refine ⟨by positivity, ?_⟩
  have hden : 0 < ((p : ℝ) - 2) * (1 - log (p : ℝ) / log D) :=
    mul_pos (by linarith) (by linarith)
  calc
    _ ≤ 1 / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log D)) :=
      one_div_le_one_div_of_le hden (by nlinarith)
    _ ≤ _ := (reboxing_prime_weight_le_four_div hD hp4 hupper).2

/-- The source R3 for upper=true; upper=false is the analogous signed
lower coefficient boundary, estimated in absolute value. -/
noncomputable def reboxingR3 {i : ℕ} (upper : Bool) (k N0 N : ℕ) (δ Δ : ℝ)
    (V : Fin i → ℝ) (t : ℝ) : ℝ :=
  4 * logarithmicIntegral N *
    ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ((convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) * wuSingularSeries (d * N) /
        ((Nat.totient d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d))) *
      ∑ p ∈ primeWindow N (((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / t))
          (((N : ℝ) ^ (1 / 2 - δ) / d) ^ (1 / t)),
        wuEffectiveCoefficient upper (k + 1) δ N0
          (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1) /
          ((Nat.totient p : ℝ) * (1 - log (p : ℝ) / log ((N : ℝ) ^ (1 / 2 - δ) / d)))


end Wu2008DoubleSieve
