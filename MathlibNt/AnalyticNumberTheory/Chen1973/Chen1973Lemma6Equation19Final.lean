/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19UniformMoments

/-!
# Chen 1973, Lemma 6, equation (19): final Hölder reduction

This module closes the second, three-factor Hölder step on the literal equation-(17)
cell and imports the uniform equation-(14), equation-(15), `L'`, and exact
prime-pair-energy interfaces.  It deliberately stops before claiming the final
`x / log(x)^20` estimate: that final cell still requires the equation-(17)
height-integration assembly.
-/

noncomputable section

open Classical Complex Finset Set
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

private lemma eq19_sum_mul_le_sqrt
    {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    (∑ i, f i * g i) ≤
      Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) := by
  simpa using Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι) f g

private lemma eq19_sqrt_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab

/-- The second displayed Hölder step in (19).  All factors are the literal
pair polynomial, natural Möbius polynomial, and totalized primitive `L'` from
(17); there is no free analytic function and no conclusion-shaped premise. -/
theorem chen1973Lemma6B_le_moment_product
    (x L level B k m H : ℕ) (s : ℂ) :
    chen1973Lemma6B x L level B k m H s ≤
      Real.sqrt (chen1973Lemma6Eq19PairSecondMoment x L level B k m s) *
        Real.sqrt
          (Real.sqrt (chen1973Lemma6Eq19LDerivFourthMoment x L level s) *
            Real.sqrt (chen1973Lemma6Eq19MobiusFourthMoment x L level H s)) := by
  let S := chen1973Lemma6ConductorBlock x L level
  let w : ℕ → ℝ := fun d => chen1973Lemma6Eq19Weight d
  let P : ℕ → ℝ := fun d => ∑ χ : PrimitiveCharacter d,
    ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
      χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
        ((pp.1 * pp.2 : ℂ) ^ s *
          Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))‖ ^ 2
  let R : ℕ → ℝ := fun d => ∑ χ : PrimitiveCharacter d,
    (‖chen1973PrimitiveLDeriv d s χ‖ *
      ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖) ^ 2
  let D4 : ℕ → ℝ := fun d => ∑ χ : PrimitiveCharacter d,
    ‖chen1973PrimitiveLDeriv d s χ‖ ^ 4
  let M4 : ℕ → ℝ := fun d => ∑ χ : PrimitiveCharacter d,
    ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 4
  have hw (d : ℕ) : 0 ≤ w d := chen1973Lemma6_eq19Weight_nonneg d
  have hP (d : ℕ) : 0 ≤ P d := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hR (d : ℕ) : 0 ≤ R d := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hD4 (d : ℕ) : 0 ≤ D4 d := Finset.sum_nonneg fun _ _ => by positivity
  have hM4 (d : ℕ) : 0 ≤ M4 d := Finset.sum_nonneg fun _ _ => by positivity
  have hchar (d : ℕ) :
      (∑ χ : PrimitiveCharacter d,
        ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
            ((pp.1 * pp.2 : ℂ) ^ s *
              Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))‖ *
        (‖chen1973PrimitiveLDeriv d s χ‖ *
          ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖)) ≤
        Real.sqrt (P d) * Real.sqrt (R d) := by
    simpa [P, R] using eq19_sum_mul_le_sqrt
      (fun χ : PrimitiveCharacter d =>
        ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
            ((pp.1 * pp.2 : ℂ) ^ s *
              Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))‖)
      (fun χ : PrimitiveCharacter d =>
        ‖chen1973PrimitiveLDeriv d s χ‖ *
          ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖)
  have hRpoint (d : ℕ) : R d ≤ Real.sqrt (D4 d) * Real.sqrt (M4 d) := by
    have h := eq19_sum_mul_le_sqrt
      (fun χ : PrimitiveCharacter d => ‖chen1973PrimitiveLDeriv d s χ‖ ^ 2)
      (fun χ : PrimitiveCharacter d =>
        ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 2)
    simpa only [R, D4, M4, pow_two, pow_succ, pow_zero, mul_one, one_mul,
      mul_assoc, mul_left_comm, mul_comm] using h
  have houter :
      (∑ d ∈ S, w d * (Real.sqrt (P d) * Real.sqrt (R d))) ≤
        Real.sqrt (∑ d ∈ S, w d * P d) *
          Real.sqrt (∑ d ∈ S, w d * R d) := by
    calc
      _ = ∑ d ∈ S,
          (Real.sqrt (w d) * Real.sqrt (P d)) *
            (Real.sqrt (w d) * Real.sqrt (R d)) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [show (Real.sqrt (w d) * Real.sqrt (P d)) *
              (Real.sqrt (w d) * Real.sqrt (R d)) =
              Real.sqrt (w d) ^ 2 *
                (Real.sqrt (P d) * Real.sqrt (R d)) by ring,
            Real.sq_sqrt (hw d)]
      _ ≤ Real.sqrt (∑ d ∈ S,
            (Real.sqrt (w d) * Real.sqrt (P d)) ^ 2) *
          Real.sqrt (∑ d ∈ S,
            (Real.sqrt (w d) * Real.sqrt (R d)) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt S _ _
      _ = _ := by
        congr 1 <;> apply congrArg Real.sqrt <;>
          apply Finset.sum_congr rfl <;> intro d hd <;>
          rw [mul_pow, Real.sq_sqrt (hw d)]
        · rw [Real.sq_sqrt (hP d)]
        · rw [Real.sq_sqrt (hR d)]
  have hprod :
      (∑ d ∈ S, w d * R d) ≤
        Real.sqrt (∑ d ∈ S, w d * D4 d) *
          Real.sqrt (∑ d ∈ S, w d * M4 d) := by
    calc
      _ ≤ ∑ d ∈ S, w d * (Real.sqrt (D4 d) * Real.sqrt (M4 d)) := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (hRpoint d) (hw d)
      _ = ∑ d ∈ S,
          (Real.sqrt (w d) * Real.sqrt (D4 d)) *
            (Real.sqrt (w d) * Real.sqrt (M4 d)) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [show (Real.sqrt (w d) * Real.sqrt (D4 d)) *
            (Real.sqrt (w d) * Real.sqrt (M4 d)) =
            Real.sqrt (w d) ^ 2 *
              (Real.sqrt (D4 d) * Real.sqrt (M4 d)) by ring,
          Real.sq_sqrt (hw d)]
      _ ≤ Real.sqrt (∑ d ∈ S,
            (Real.sqrt (w d) * Real.sqrt (D4 d)) ^ 2) *
          Real.sqrt (∑ d ∈ S,
            (Real.sqrt (w d) * Real.sqrt (M4 d)) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt S _ _
      _ = _ := by
        congr 1 <;> apply congrArg Real.sqrt <;>
          apply Finset.sum_congr rfl <;> intro d hd <;>
          rw [mul_pow, Real.sq_sqrt (hw d)]
        · rw [Real.sq_sqrt (hD4 d)]
        · rw [Real.sq_sqrt (hM4 d)]
  unfold chen1973Lemma6B
  change (∑ d ∈ S, w d * ∑ χ : PrimitiveCharacter d,
      _ * ‖chen1973PrimitiveLDeriv d s χ *
        chen1973Lemma6MobiusPartialSum H s χ‖) ≤ _
  have hfirst :
      (∑ d ∈ S, w d * ∑ χ : PrimitiveCharacter d,
        ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
            ((pp.1 * pp.2 : ℂ) ^ s *
              Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))‖ *
        ‖chen1973PrimitiveLDeriv d s χ *
          chen1973Lemma6MobiusPartialSum H s χ‖) ≤
        ∑ d ∈ S, w d * (Real.sqrt (P d) * Real.sqrt (R d)) := by
    apply Finset.sum_le_sum
    intro d hd
    apply mul_le_mul_of_nonneg_left
    · simpa [norm_mul, chen1973Lemma6NaturalMobiusPolynomial] using hchar d
    · exact hw d
  calc
    _ ≤ ∑ d ∈ S, w d * (Real.sqrt (P d) * Real.sqrt (R d)) := hfirst
    _ ≤ Real.sqrt (∑ d ∈ S, w d * P d) *
        Real.sqrt (∑ d ∈ S, w d * R d) := houter
    _ ≤ Real.sqrt (∑ d ∈ S, w d * P d) *
        Real.sqrt
          (Real.sqrt (∑ d ∈ S, w d * D4 d) *
            Real.sqrt (∑ d ∈ S, w d * M4 d)) := by
      exact mul_le_mul_of_nonneg_left
        (eq19_sqrt_mono (Finset.sum_nonneg fun d hd => mul_nonneg (hw d) (hR d)) hprod)
        (Real.sqrt_nonneg _)
    _ = _ := by
      simp only [chen1973Lemma6Eq19PairSecondMoment,
        chen1973Lemma6Eq19LDerivFourthMoment,
        chen1973Lemma6Eq19MobiusFourthMoment]
      rfl

end AnalyticNumberTheory.LargeSieve
