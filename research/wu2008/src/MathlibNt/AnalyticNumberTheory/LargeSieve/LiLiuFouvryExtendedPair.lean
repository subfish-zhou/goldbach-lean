import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryExtendedPayment
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryActualCoprimePartition
noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
theorem wCoprimePairBound_extended_le {x ν ε : ℝ} (hx : 4 ≤ x)
    (hε : 0 < ε) (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10+ε/10)
    {N : Finset ℕ} (hN : ∀ n ∈ N, (n : ℝ) ≤ 2 * x ^ ν) :
    (wCoprimePairBound N (x ^ c2SExponent ν ε) : ℝ) ≤ x := by
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ : 0 < x := by linarith
  have hS : 1 ≤ x ^ c2SExponent ν ε :=
    (c2_extended_factor_levels hx₁ hε hεν hν).2.1
  have hs := c2_extended_short_add_S_le_half hε hεν hν
  have hp : x ^ ν * x ^ c2SExponent ν ε ≤ Real.sqrt x := by
    rw [← Real.rpow_add hx₀, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx₁ hs
  have hsup : ((N.sup id : ℕ) : ℝ) ≤ 2 * x ^ ν :=
    (Nat.cast_le.mpr (Finset.sup_le (fun n hn => Nat.le_floor (hN n hn)))).trans
      (Nat.floor_le (by positivity))
  have hprod : ((N.sup id : ℕ) : ℝ) * ⌊x ^ c2SExponent ν ε⌋₊ ≤ x := by
    have he : ((N.sup id : ℕ) : ℝ) * ⌊x ^ c2SExponent ν ε⌋₊ ≤
        2 * Real.sqrt x := by
      calc
        _ ≤ (2 * x ^ ν) * x ^ c2SExponent ν ε :=
          mul_le_mul hsup (Nat.floor_le (by positivity)) (Nat.cast_nonneg _) (by positivity)
        _ ≤ 2 * Real.sqrt x := by nlinarith
    have hsqrt := Real.sq_sqrt hx₀.le
    have hsqrt₀ := Real.sqrt_nonneg x
    nlinarith
  have hf : (1 : ℝ) ≤ ⌊x ^ c2SExponent ν ε⌋₊ := by
    exact_mod_cast (Nat.le_floor (by simpa using hS) : 1 ≤ ⌊x ^ c2SExponent ν ε⌋₊)
  have hn : ((N.sup id : ℕ) : ℝ) ≤ x :=
    (le_mul_of_one_le_right (Nat.cast_nonneg _) hf).trans hprod
  simpa only [wCoprimePairBound, Nat.cast_max, Nat.cast_ofNat, Nat.cast_mul] using
    max_le (by linarith : (2 : ℝ) ≤ x) (max_le hn hprod)


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
