import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma143UniformTailCore
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Suzuki Lemma 14.3: explicit logarithmic exponent

This file converts a bound of the form

`T ≤ L^M / M! * exp L`

into a completely explicit exponential bound.  The final theorem takes
`M = ⌊s - 2⌋₊ + 1`; the hypothesis `exp 1 * L ≤ s - 2` is an explicit
(non-asymptotic) large-cutoff condition ensuring that the floor error has the
favourable sign.
-/

open scoped Classical BigOperators

namespace MathlibNt.SieveTheory

/-- The elementary lower bound `m! ≥ exp (m log m - m)`.  We retain only the
main two terms of Mathlib's global Stirling lower bound. -/
theorem exp_nat_mul_log_sub_nat_le_factorial
    (m : ℕ) (hm : 0 < m) :
    Real.exp ((m : ℝ) * Real.log (m : ℝ) - (m : ℝ)) ≤
      (m.factorial : ℝ) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    have hpi := Real.pi_gt_three
    linarith
  have hmain :
      (m : ℝ) * Real.log (m : ℝ) - (m : ℝ) ≤
        Real.log (m.factorial : ℝ) := by
    calc
      (m : ℝ) * Real.log (m : ℝ) - (m : ℝ) ≤
          (m : ℝ) * Real.log (m : ℝ) - (m : ℝ) +
            Real.log (m : ℝ) / 2 + Real.log (2 * Real.pi) / 2 := by
        linarith
      _ ≤ Real.log (m.factorial : ℝ) :=
        Stirling.le_log_factorial_stirling (Nat.ne_of_gt hm)
  rw [← Real.exp_log (show (0 : ℝ) < (m.factorial : ℝ) by positivity)]
  exact Real.exp_le_exp.mpr hmain

/-- Exact log-exponent conversion at a positive integer cutoff.  This is the
form to use immediately after obtaining the standard exponential-tail bound
`L^M / M! * exp L`. -/
theorem pow_div_factorial_mul_exp_le_logExponent
    {L T : ℝ} {M : ℕ} (hL : 0 < L) (hM : 0 < M)
    (hT : T ≤ L ^ M / (M.factorial : ℝ) * Real.exp L) :
    T ≤ Real.exp
      (L + (M : ℝ) * (1 + Real.log L - Real.log (M : ℝ))) := by
  have hfac := exp_nat_mul_log_sub_nat_le_factorial M hM
  have hpow0 : 0 ≤ L ^ M := pow_nonneg hL.le M
  have hquot :
      L ^ M / (M.factorial : ℝ) ≤
        L ^ M /
          Real.exp ((M : ℝ) * Real.log (M : ℝ) - (M : ℝ)) :=
    div_le_div_of_nonneg_left hpow0 (Real.exp_pos _) hfac
  have hmul := mul_le_mul_of_nonneg_right hquot (Real.exp_pos L).le
  calc
    T ≤ L ^ M / (M.factorial : ℝ) * Real.exp L := hT
    _ ≤ L ^ M /
          Real.exp ((M : ℝ) * Real.log (M : ℝ) - (M : ℝ)) *
        Real.exp L := hmul
    _ = Real.exp
          (L + (M : ℝ) * (1 + Real.log L - Real.log (M : ℝ))) := by
      have hpowexp : L ^ M = Real.exp ((M : ℝ) * Real.log L) := by
        calc
          L ^ M = Real.exp (Real.log L) ^ M := by rw [Real.exp_log hL]
          _ = Real.exp ((M : ℝ) * Real.log L) :=
            (Real.exp_nat_mul (Real.log L) M).symm
      rw [hpowexp, ← Real.exp_sub, ← Real.exp_add]
      congr 1
      ring

/-- Floor-error conversion in the exact cutoff used by Suzuki Lemma 14.3.

The explicit condition `exp 1 * L ≤ s - 2` implies both positivity and that
`x ↦ x (1 + log L - log x)` is already decreasing in the only comparison
needed here.  Since

` s - 2 < ⌊s - 2⌋₊ + 1`,

the integer exponent can therefore be replaced by the real endpoint `s - 2`
without any hidden asymptotic predicate or Big-O constant. -/
theorem floorTail_le_claim145_logExponent
    {s L T : ℝ} (hL : 0 < L)
    (hlarge : Real.exp 1 * L ≤ s - 2)
    (hT : T ≤
      L ^ (⌊s - 2⌋₊ + 1) /
          (((⌊s - 2⌋₊ + 1).factorial : ℕ) : ℝ) * Real.exp L) :
    T ≤ Real.exp
      (L + (s - 2) * (1 + Real.log L - Real.log (s - 2))) := by
  let M : ℕ := ⌊s - 2⌋₊ + 1
  have hM : 0 < M := by simp [M]
  have hbasePos : 0 < Real.exp 1 * L := mul_pos (Real.exp_pos _) hL
  have hx : 0 < s - 2 := hbasePos.trans_le hlarge
  have hfloorNonneg : 0 ≤ s - 2 := hx.le
  have hxM : s - 2 < (M : ℝ) := by
    simpa [M, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (s - 2))
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hlogxM : Real.log (s - 2) ≤ Real.log (M : ℝ) := by
    exact (Real.strictMonoOn_log hx hMreal hxM).le
  have hprodPos : 0 < Real.exp 1 * L := hbasePos
  have hlogLarge :
      Real.log (Real.exp 1 * L) ≤ Real.log (s - 2) :=
    Real.strictMonoOn_log.monotoneOn hprodPos hx hlarge
  have hlogProd :
      Real.log (Real.exp 1 * L) = 1 + Real.log L := by
    rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hL), Real.log_exp]
  have hcoef : 1 + Real.log L - Real.log (s - 2) ≤ 0 := by
    rw [hlogProd] at hlogLarge
    linarith
  have hMlog :
      (M : ℝ) * (1 + Real.log L - Real.log (M : ℝ)) ≤
        (M : ℝ) * (1 + Real.log L - Real.log (s - 2)) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hlogxM _) hMreal.le
  have hfloorError :
      (M : ℝ) * (1 + Real.log L - Real.log (s - 2)) ≤
        (s - 2) * (1 + Real.log L - Real.log (s - 2)) :=
    mul_le_mul_of_nonpos_right hxM.le hcoef
  have hexact :
      T ≤ Real.exp
        (L + (M : ℝ) * (1 + Real.log L - Real.log (M : ℝ))) := by
    apply pow_div_factorial_mul_exp_le_logExponent hL hM
    simpa [M] using hT
  exact hexact.trans (Real.exp_le_exp.mpr
    (add_le_add le_rfl (hMlog.trans hfloorError)))

/-- Direct consumer for the tail object occurring in Lemma 14.3.  The standard
`L^M/M! * exp L` estimate is kept as an explicit premise, so this theorem can be
composed with any proof of that estimate without changing constants. -/
theorem suzukiExponentialTail_le_claim145_logExponent
    {s L : ℝ} (hL : 0 < L)
    (hlarge : Real.exp 1 * L ≤ s - 2)
    (htail : suzukiExponentialTail L (⌊s - 2⌋₊ + 1) ≤
      L ^ (⌊s - 2⌋₊ + 1) /
          (((⌊s - 2⌋₊ + 1).factorial : ℕ) : ℝ) * Real.exp L) :
    suzukiExponentialTail L (⌊s - 2⌋₊ + 1) ≤
      Real.exp
        (L + (s - 2) * (1 + Real.log L - Real.log (s - 2))) :=
  floorTail_le_claim145_logExponent hL hlarge htail

/-- Suzuki Lemma 14.3 with the exponential tail converted all the way to the
logarithmic exponent consumed in subsequent Claim-14.5 comparisons.  Every
constant and threshold condition is explicit. -/
theorem suzukiLemma14_3_uniform_logExponent
    (S : BoundingSieve) {N D z : ℕ} {s L : ℝ}
    (hz : 0 < z) (hL : 0 < L)
    (hpow : z ^ (⌊s - 2⌋₊ + 2) ≤ D)
    (h141 : SuzukiLemma141Majorant S D z L)
    (hlarge : Real.exp 1 * L ≤ s - 2)
    (htail : suzukiExponentialTail L (⌊s - 2⌋₊ + 1) ≤
      L ^ (⌊s - 2⌋₊ + 1) /
          (((⌊s - 2⌋₊ + 1).factorial : ℕ) : ℝ) * Real.exp L) :
    suzukiActualT S N D z ≤
      Real.exp
        (L + (s - 2) * (1 + Real.log L - Real.log (s - 2))) := by
  have hs : 2 ≤ s := by
    have hpos : 0 < Real.exp 1 * L := mul_pos (Real.exp_pos _) hL
    linarith
  exact (suzukiLemma14_3_uniform_exponentialTail S hz hs hL.le hpow h141).trans
    (suzukiExponentialTail_le_claim145_logExponent hL hlarge htail)


end MathlibNt.SieveTheory
