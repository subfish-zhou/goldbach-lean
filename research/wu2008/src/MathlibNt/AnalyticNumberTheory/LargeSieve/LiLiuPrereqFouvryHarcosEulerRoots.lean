import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosEulerSeries
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Harcos's irreducible sum equals the negative root power sum

The input character is the actual polynomial character. The Euler logarithmic
identity is produced by finite factorization, not assumed.
-/

noncomputable section

open Finset
open scoped Polynomial

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem euler_coeff_cancel (A F G : PowerSeries ℂ)
    (hA : PowerSeries.constantCoeff A = 1) (N : ℕ)
    (h : ∀ n ≤ N, PowerSeries.coeff n (F * A) = PowerSeries.coeff n (G * A)) :
    PowerSeries.coeff N F = PowerSeries.coeff N G := by
  obtain ⟨u, hu⟩ := PowerSeries.isUnit_iff_constantCoeff.mpr
    (show IsUnit (PowerSeries.constantCoeff A) by rw [hA]; exact isUnit_one)
  have he : PowerSeries.coeff N ((F * A) * (↑u⁻¹ : PowerSeries ℂ)) =
      PowerSeries.coeff N ((G * A) * (↑u⁻¹ : PowerSeries ℂ)) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply sum_congr rfl
    intro ij hij
    rw [h ij.1 (by have := mem_antidiagonal.mp hij; omega)]
  simpa [mul_assoc, ← hu] using he

private def eulerRootLog (α β : ℂ) : PowerSeries ℂ :=
  -((harcosEulerGeometric 1 α - 1) + (harcosEulerGeometric 1 β - 1))

private theorem eulerRootLog_mul (α β : ℂ) :
    eulerRootLog α β *
        ((1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X)) =
      PowerSeries.X * (PowerSeries.derivative ℂ)
        ((1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X)) := by
  have ha := harcosEulerGeometric_mul 1 (by omega) α
  have hb := harcosEulerGeometric_mul 1 (by omega) β
  simp only [pow_one] at ha hb
  simp only [eulerRootLog, Derivation.leibniz, map_sub, PowerSeries.derivative_one,
    PowerSeries.derivative_C, PowerSeries.derivative_X, smul_eq_mul,
    mul_zero, mul_one, zero_sub]
  linear_combination
    -(1 - PowerSeries.C β * PowerSeries.X) * ha -
    (1 - PowerSeries.C α * PowerSeries.X) * hb

private theorem eulerRootLog_coeff (α β : ℂ) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff n (eulerRootLog α β) = -(α ^ n + β ^ n) := by
  simp [eulerRootLog, harcosEulerGeometric, PowerSeries.coeff_one, hn]

variable {p : ℕ} [Fact p.Prime]

theorem harcosEulerCoefficient_zero (η : (ZMod p)[X] →* ℂ) :
    harcosEulerCoefficient η 0 = 1 := by
  classical
  simp [harcosEulerCoefficient, harcosMonicPolynomials, harcosMonic_zero]

/-- A quadratic factorization of the actual monic series determines all prime-power sums. -/
theorem harcosEulerLogCoefficient_eq_powerSum (η : (ZMod p)[X] →* ℂ) (α β : ℂ)
    (hA : harcosEulerSeries η =
      (1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X))
    (n : ℕ) (hn : n ≠ 0) :
    harcosEulerLogCoefficient η n = -(α ^ n + β ^ n) := by
  have h0 : PowerSeries.constantCoeff (harcosEulerSeries η) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, harcosEulerSeries,
      PowerSeries.coeff_mk, harcosEulerCoefficient_zero]
  have he := euler_coeff_cancel (harcosEulerSeries η)
    (harcosEulerLog η n) (eulerRootLog α β) h0 n (by
      intro j hj
      rw [harcosEulerLog_mul_coeff η n j hj, hA, eulerRootLog_mul, ← hA]
      cases j with
      | zero => simp
      | succ j =>
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
            harcosEulerSeries, PowerSeries.coeff_mk]
          push_cast
          ring)
  rw [harcosEulerLog_coeff η n n le_rfl, eulerRootLog_coeff α β n hn] at he
  exact he

theorem harcosEulerSeries_character (a b : ZMod p) :
    harcosEulerSeries (harcosEtaHom a b).toMonoidHom = harcosLSeries a b := by
  apply PowerSeries.ext
  intro n
  rw [harcosEulerSeries, harcosLSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    harcosCoefficient_eq_sum_monic]
  rfl

/-- The finite algebraic content of Harcos's equation (10), for the actual character. -/
theorem harcosEuler_character_powerSum (a : ZMod p) (b : ℤ)
    (ha : a ≠ 0) (hb : (b : ZMod p) ≠ 0) (α β : ℂ)
    (hsum : α + β = -completeKloosterman p a b) (hprod : α * β = (p : ℂ))
    (n : ℕ) (hn : n ≠ 0) :
    harcosEulerLogCoefficient (harcosEtaHom a (b : ZMod p)).toMonoidHom n =
      -(α ^ n + β ^ n) := by
  apply harcosEulerLogCoefficient_eq_powerSum _ α β _ n hn
  rw [harcosEulerSeries_character, harcosLSeries_eq_polynomial a (b : ZMod p) ha,
    harcosLPolynomial_eq a b ha hb]
  simp only [Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_pow]
  have hs := congrArg PowerSeries.C hsum
  have hp := congrArg PowerSeries.C hprod
  simp only [map_add, map_neg, map_mul] at hs hp
  linear_combination PowerSeries.X * hs - PowerSeries.X ^ 2 * hp

/-- The actual irreducible coefficients for the explicitly constructed reciprocal roots. -/
theorem harcosEuler_character_reciprocalRoots (a b : ZMod p) (ha : a ≠ 0)
    (n : ℕ) (hn : n ≠ 0) :
    harcosEulerLogCoefficient (harcosEtaHom a b).toMonoidHom n =
      -(harcosReciprocalRootPlus a b ^ n + harcosReciprocalRootMinus a b ^ n) := by
  apply harcosEulerLogCoefficient_eq_powerSum _ _ _ _ n hn
  rw [harcosEulerSeries_character]
  exact harcosLSeries_factorization a b ha

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
