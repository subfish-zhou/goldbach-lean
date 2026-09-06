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

/-- Weighted Cauchy-Schwarz for nonnegative conductor weights and factors. -/
lemma eq19_weighted_sum_sqrt_mul_sqrt_le
    {ι : Type*} (S : Finset ι) (w f g : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    (∑ i ∈ S, w i * (Real.sqrt (f i) * Real.sqrt (g i))) ≤
      Real.sqrt (∑ i ∈ S, w i * f i) * Real.sqrt (∑ i ∈ S, w i * g i) := by
  convert Real.sum_sqrt_mul_sqrt_le S
    (fun i => mul_nonneg (hw i) (hf i))
    (fun i => mul_nonneg (hw i) (hg i)) using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.sqrt_mul (hw i), Real.sqrt_mul (hw i)]
  calc
    _ = Real.sqrt (w i) ^ 2 * (Real.sqrt (f i) * Real.sqrt (g i)) := by
      rw [Real.sq_sqrt (hw i)]
    _ = _ := by ring

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
    exact eq19_weighted_sum_sqrt_mul_sqrt_le S w P R hw hP hR
  have hprod :
      (∑ d ∈ S, w d * R d) ≤
        Real.sqrt (∑ d ∈ S, w d * D4 d) *
          Real.sqrt (∑ d ∈ S, w d * M4 d) := by
    calc
      _ ≤ ∑ d ∈ S, w d * (Real.sqrt (D4 d) * Real.sqrt (M4 d)) := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (hRpoint d) (hw d)
      _ ≤ Real.sqrt (∑ d ∈ S, w d * D4 d) *
          Real.sqrt (∑ d ∈ S, w d * M4 d) :=
        eq19_weighted_sum_sqrt_mul_sqrt_le S w D4 M4 hw hD4 hM4
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
        (Real.sqrt_le_sqrt hprod)
        (Real.sqrt_nonneg _)
    _ = _ := by
      simp only [chen1973Lemma6Eq19PairSecondMoment,
        chen1973Lemma6Eq19LDerivFourthMoment,
        chen1973Lemma6Eq19MobiusFourthMoment]
      rfl

end AnalyticNumberTheory.LargeSieve
