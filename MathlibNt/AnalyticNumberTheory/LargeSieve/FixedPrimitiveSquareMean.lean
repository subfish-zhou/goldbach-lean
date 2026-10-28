/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma2PrimitiveLargeSieve

/-! # Fixed primitive large-sieve constant for complex coefficients

The constant is chosen before the coefficients, interval and conductor bounds.
This shared tool is independent of Chen's later moment and contour estimates.
-/

noncomputable section
open Classical Complex Finset Set
open scoped BigOperators ArithmeticFunction
namespace AnalyticNumberTheory.LargeSieve

/-- The real sharp Lemma-2 package, with its absolute constant selected once. -/
private theorem eq19SharpRealPackage : Chen1973Lemma2EquationThree :=
  chen1973Lemma2_equationThree_of_equationTwo
    (chen1973Lemma2_equationTwo_of_fareyEquationFour chen1973FareyEquationFour)

/-- One fixed global constant for all complex-coefficient uses of sharp Lemma 2. -/
def chen1973Lemma6Eq19SharpConstant : ℝ :=
  2 * Classical.choose eq19SharpRealPackage

lemma chen1973Lemma6_eq19SharpConstant_pos :
    0 < chen1973Lemma6Eq19SharpConstant := by
  unfold chen1973Lemma6Eq19SharpConstant
  exact mul_pos (by norm_num) (Classical.choose_spec eq19SharpRealPackage).1

/-- Complex sharp Lemma 2 with a single constant chosen before the coefficient
sequence and all interval/conductor parameters. -/
theorem chen1973Lemma2_equationThree_complex_fixed
    (c : ℤ → ℂ) (M : ℤ) (N D Q : ℕ) (hD : 0 < D) :
    (∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖∑ n ∈ Icc (M + 1) (M + N), c n * χ.1 (n : ZMod q)‖ ^ 2) ≤
      chen1973Lemma6Eq19SharpConstant *
        ((Q : ℝ) + (N : ℝ) / D) *
        ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2 := by
  let C : ℝ := Classical.choose eq19SharpRealPackage
  change _ ≤ 2 * C * ((Q : ℝ) + (N : ℝ) / D) *
    ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2
  have hC := (Classical.choose_spec eq19SharpRealPackage).2
  let aR : ℤ → ℝ := fun n => (c n).re
  let aI : ℤ → ℝ := fun n => (c n).im
  have hp (q : ℕ) (χ : PrimitiveCharacter q) :
      ‖∑ n ∈ Icc (M + 1) (M + N), c n * χ.1 (n : ZMod q)‖ ^ 2 ≤
        2 * (‖chen1973PrimitiveAmplitude aR M N q χ‖ ^ 2 +
          ‖chen1973PrimitiveAmplitude aI M N q χ‖ ^ 2) := by
    let AR := chen1973PrimitiveAmplitude aR M N q χ
    let AI := chen1973PrimitiveAmplitude aI M N q χ
    have heq : (∑ n ∈ Icc (M + 1) (M + N), c n * χ.1 (n : ZMod q)) =
        AR + I * AI := by
      dsimp [AR, AI, chen1973PrimitiveAmplitude]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [aR, aI]
      calc
        c n * χ.1 (n : ZMod q) =
            (((c n).re : ℂ) + ((c n).im : ℂ) * I) * χ.1 (n : ZMod q) := by
              rw [Complex.re_add_im]
        _ = ((c n).re : ℂ) * χ.1 (n : ZMod q) +
            I * (((c n).im : ℂ) * χ.1 (n : ZMod q)) := by ring
    rw [heq]
    have h := norm_add_le AR (I * AI)
    have hI : ‖I * AI‖ = ‖AI‖ := by simp
    rw [hI] at h
    have hsquare : ‖AR + I * AI‖ ^ 2 ≤ (‖AR‖ + ‖AI‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    dsimp [AR, AI]
    nlinarith [sq_nonneg (‖AR‖ - ‖AI‖)]
  have hR := hC aR M N D Q hD
  have hI := hC aI M N D Q hD
  calc
    _ ≤ ∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          2 * (‖chen1973PrimitiveAmplitude aR M N q χ‖ ^ 2 +
            ‖chen1973PrimitiveAmplitude aI M N q χ‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun χ hχ => hp q χ) (by positivity)
    _ = 2 * ((∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q, ‖chen1973PrimitiveAmplitude aR M N q χ‖ ^ 2) +
        (∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q, ‖chen1973PrimitiveAmplitude aI M N q χ‖ ^ 2)) := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hmul (a b : ℝ) : a * (2 * b) = 2 * (a * b) := by ring
      simp_rw [hmul]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (C * ((Q : ℝ) + (N : ℝ) / D) * chen1973CoefficientEnergy aR M N +
        C * ((Q : ℝ) + (N : ℝ) / D) * chen1973CoefficientEnergy aI M N) := by
      gcongr
    _ = 2 * C * ((Q : ℝ) + (N : ℝ) / D) *
        ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2 := by
      unfold chen1973CoefficientEnergy
      rw [show 2 * C * ((Q : ℝ) + (N : ℝ) / D) *
          (∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2) =
        2 * (C * ((Q : ℝ) + (N : ℝ) / D) *
          ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2) by ring]
      apply congrArg (fun z : ℝ => 2 * z)
      rw [← mul_add, ← Finset.sum_add_distrib]
      apply congrArg (fun z : ℝ => C * ((Q : ℝ) + (N : ℝ) / D) * z)
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [aR, aI]
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply, sq_abs]
      ring

end AnalyticNumberTheory.LargeSieve
