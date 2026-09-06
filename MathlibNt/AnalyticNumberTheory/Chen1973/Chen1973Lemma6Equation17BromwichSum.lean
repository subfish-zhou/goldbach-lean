/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equations16And17

/-!
# Chen 1973, Lemma 6, equation (17): finite Bromwich sums

This module closes the finite-sum part of the passage to (17).  It proves that
Chen's actual finite `Φ` is a Bochner integral over the full real Bromwich line,
exchanges that integral with the finite von-Mangoldt, prime-pair, and primitive
character sums, and then records the resulting exact conductor-block identity.
No equation-(17) majorization or contour-deformation conclusion is assumed.
-/

noncomputable section

open Classical Complex Finset MeasureTheory Set
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

/-- The Bromwich integrand is Bochner integrable for every positive argument. -/
theorem integrable_chen1973BromwichIntegrand
    {x y : ℝ} (hx : 1 < x) (hy : 0 < y) :
    Integrable (fun t : ℝ => chen1973BromwichIntegrand x y t) := by
  have hk : Integrable
      (fun t : ℝ => chen1973MellinKernel x (((2 : ℝ) : ℂ) + t * I)) := by
    simpa only [Complex.VerticalIntegrable] using
      (verticalIntegrable_chen1973MellinKernel hx)
  have hp : AEStronglyMeasurable
      (fun t : ℝ => (y : ℂ) ^ (((2 : ℝ) : ℂ) + t * I)) := by
    have he : Continuous (fun t : ℝ => (((2 : ℝ) : ℂ) + t * I)) := by
      fun_prop
    exact (he.const_cpow (Or.inl (by exact_mod_cast hy.ne'))).aestronglyMeasurable
  have hpow : ∀ t : ℝ,
      ‖(y : ℂ) ^ (((2 : ℝ) : ℂ) + t * I)‖ ≤ y ^ (2 : ℕ) := by
    intro t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp
  have hmul : Integrable (fun t : ℝ =>
      (y : ℂ) ^ (((2 : ℝ) : ℂ) + t * I) *
        chen1973MellinKernel x (((2 : ℝ) : ℂ) + t * I)) :=
    hk.bdd_mul hp (ae_of_all _ hpow)
  apply hmul.congr
  filter_upwards with t
  unfold chen1973BromwichIntegrand chen1973MellinKernel
  norm_num [div_eq_mul_inv]

/-- The literal finite von-Mangoldt/character integrand whose full-line integral
is `chen1973Lemma6ActualPhi`.  The normalization `1/(2π)` is inside the
integrand, so the result is a single Bochner integral. -/
def chen1973Lemma6BromwichVonMangoldtIntegrand
    (x d : ℕ) (χ : PrimitiveCharacter d) (pp : ℕ × ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ chen1973Lemma5NCarrier x pp,
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        chen1973BromwichIntegrand (x : ℝ)
          ((x : ℝ) / ((pp.1 : ℝ) * pp.2 * n)) t) *
      χ.1 (n : ZMod d)

/-- Every summand in the finite von-Mangoldt Bromwich sum is Bochner
integrable.  The `n=0` term vanishes; positive `n` use the closed Mellin
integrability theorem. -/
theorem integrable_chen1973Lemma6BromwichVonMangoldtTerm
    {x d n : ℕ} {pp : ℕ × ℕ} (χ : PrimitiveCharacter d)
    (hx : 1 < x) (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2) :
    Integrable (fun t : ℝ =>
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          chen1973BromwichIntegrand (x : ℝ)
            ((x : ℝ) / ((pp.1 : ℝ) * pp.2 * n)) t) *
        χ.1 (n : ZMod d)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hy : 0 < (x : ℝ) / ((pp.1 : ℝ) * pp.2 * n) := by
      positivity
    exact (((integrable_chen1973BromwichIntegrand
      (by exact_mod_cast hx) hy).const_mul
        (((1 / (2 * Real.pi) : ℝ) : ℂ))).const_mul
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)).mul_const
            (χ.1 (n : ZMod d))

/-- The complete finite von-Mangoldt Bromwich integrand is Bochner integrable. -/
theorem integrable_chen1973Lemma6BromwichVonMangoldtIntegrand
    {x d : ℕ} {pp : ℕ × ℕ} (χ : PrimitiveCharacter d)
    (hx : 1 < x) (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2) :
    Integrable (chen1973Lemma6BromwichVonMangoldtIntegrand x d χ pp) := by
  unfold chen1973Lemma6BromwichVonMangoldtIntegrand
  apply integrable_finsetSum
  intro n hn
  exact integrable_chen1973Lemma6BromwichVonMangoldtTerm χ hx hp₁ hp₂

/-- `chen1973Lemma6ActualPhi` is exactly the full real-line integral of its
finite von-Mangoldt twisted sum. -/
theorem chen1973Lemma6ActualPhi_eq_integral_bromwichSum
    {x d : ℕ} {pp : ℕ × ℕ} (χ : PrimitiveCharacter d)
    (hx : 1 < x) (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2) :
    chen1973Lemma6ActualPhi x d χ pp =
      ∫ t : ℝ, chen1973Lemma6BromwichVonMangoldtIntegrand x d χ pp t := by
  unfold chen1973Lemma6ActualPhi chen1973Lemma6BromwichVonMangoldtIntegrand
  rw [integral_finsetSum (chen1973Lemma5NCarrier x pp)]
  · apply Finset.sum_congr rfl
    intro n hnmem
    by_cases hn : n = 0
    · subst n
      simp
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      rw [chen1973Lemma6ActualPhi_termwise_bromwich χ hx hnpos hp₁ hp₂]
      symm
      rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_const_mul]
  · intro n hnmem
    exact integrable_chen1973Lemma6BromwichVonMangoldtTerm χ hx hp₁ hp₂

/-- Membership in a source prime-pair shell forces both coordinates positive. -/
theorem chen1973Lemma6PrimePairShell_pos
    {x B k m : ℕ} {pp : ℕ × ℕ}
    (hpp : pp ∈ chen1973Lemma6PrimePairShell x B k m) :
    0 < pp.1 ∧ 0 < pp.2 := by
  simp only [chen1973Lemma6PrimePairShell, chen1973Lemma6DyadicShell,
    Finset.mem_filter] at hpp
  have hpairs : pp ∈ chen1973Lemma5PrimePairs x := by
    exact hpp.1.1
  simp only [chen1973Lemma5PrimePairs, Finset.mem_filter] at hpairs
  exact ⟨hpairs.2.1.pos, hpairs.2.2.1.pos⟩

/-- The prime-pair sum after moving its finite sum inside the Bromwich
integral. -/
def chen1973Lemma6BromwichPrimePairIntegrand
    (x d B k m : ℕ) (χ : PrimitiveCharacter d) (t : ℝ) : ℂ :=
  ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
    (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
      chen1973Lemma6BromwichVonMangoldtIntegrand x d χ pp t *
      χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d)

/-- Every prime-pair integrand is Bochner integrable. -/
theorem integrable_chen1973Lemma6BromwichPrimePairIntegrand
    {x d B k m : ℕ} (χ : PrimitiveCharacter d) (hx : 1 < x) :
    Integrable (chen1973Lemma6BromwichPrimePairIntegrand x d B k m χ) := by
  unfold chen1973Lemma6BromwichPrimePairIntegrand
  apply integrable_finsetSum
  intro pp hpp
  obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
  simpa only [Complex.ofReal_inv] using
    ((integrable_chen1973Lemma6BromwichVonMangoldtIntegrand χ hx hp₁ hp₂).const_mul
      (((Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ : ℝ) : ℂ)).mul_const
        (χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d))

/-- Exact finite prime-pair/integral exchange. -/
theorem chen1973Lemma6PrimePairSum_eq_integral_bromwichSum
    {x d B k m : ℕ} (χ : PrimitiveCharacter d) (hx : 1 < x) :
    (∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
      (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
        chen1973Lemma6ActualPhi x d χ pp *
        χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d)) =
      ∫ t : ℝ, chen1973Lemma6BromwichPrimePairIntegrand x d B k m χ t := by
  unfold chen1973Lemma6BromwichPrimePairIntegrand
  rw [integral_finsetSum (chen1973Lemma6PrimePairShell x B k m)]
  · apply Finset.sum_congr rfl
    intro pp hpp
    obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
    rw [chen1973Lemma6ActualPhi_eq_integral_bromwichSum χ hx hp₁ hp₂]
    symm
    rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul]
  · intro pp hpp
    obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
    simpa only [Complex.ofReal_inv] using
      ((integrable_chen1973Lemma6BromwichVonMangoldtIntegrand χ hx hp₁ hp₂).const_mul
        (((Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ : ℝ) : ℂ)).mul_const
          (χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d))

/-- The complete primitive-character integrand for one conductor. -/
def chen1973Lemma6BromwichCharacterIntegrand
    (x d B k m : ℕ) (t : ℝ) : ℂ :=
  ∑ χ : PrimitiveCharacter d,
    star (χ.1 (x : ZMod d)) *
      chen1973Lemma6BromwichPrimePairIntegrand x d B k m χ t

/-- The finite primitive-character integrand is Bochner integrable. -/
theorem integrable_chen1973Lemma6BromwichCharacterIntegrand
    {x d B k m : ℕ} (hx : 1 < x) :
    Integrable (chen1973Lemma6BromwichCharacterIntegrand x d B k m) := by
  unfold chen1973Lemma6BromwichCharacterIntegrand
  apply integrable_finsetSum
  intro χ hχ
  exact (integrable_chen1973Lemma6BromwichPrimePairIntegrand χ hx).const_mul _

/-- Exact exchange of the primitive-character sum with the full-line
Bromwich integral. -/
theorem chen1973Lemma6CharacterSum_eq_integral_bromwichSum
    {x d B k m : ℕ} (hx : 1 < x) :
    (∑ χ : PrimitiveCharacter d,
      star (χ.1 (x : ZMod d)) *
        ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
            chen1973Lemma6ActualPhi x d χ pp *
            χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d)) =
      ∫ t : ℝ, chen1973Lemma6BromwichCharacterIntegrand x d B k m t := by
  unfold chen1973Lemma6BromwichCharacterIntegrand
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro χ hχ
    rw [chen1973Lemma6PrimePairSum_eq_integral_bromwichSum χ hx]
    symm
    rw [MeasureTheory.integral_const_mul]
  · intro χ hχ
    exact (integrable_chen1973Lemma6BromwichPrimePairIntegrand χ hx).const_mul _

/-- The exact conductor-block expression after all finite sums have been moved
inside their full-line Bromwich integrals.  The conductor sum and norm remain
outside, exactly as in the definition of `N_m`. -/
def chen1973Lemma6NmBlockBromwich
    (x L level B k m : ℕ) : ℝ :=
  ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * (3 : ℝ) ^ d.primeFactors.card / d *
      ‖∫ t : ℝ, chen1973Lemma6BromwichCharacterIntegrand x d B k m t‖

/-- Exact conductor-block lift of the finite Bromwich identity.  This is the
finite-sum closure needed before any contour deformation toward equation (17),
and it has no equation-(17) conclusion premise. -/
theorem chen1973Lemma6NmBlockActual_eq_bromwich
    {x L level B k m : ℕ} (hx : 1 < x) :
    chen1973Lemma6NmBlockActual x L level B k m =
      chen1973Lemma6NmBlockBromwich x L level B k m := by
  unfold chen1973Lemma6NmBlockActual chen1973Lemma6NmBlockBromwich
  apply Finset.sum_congr rfl
  intro d hd
  rw [chen1973Lemma6CharacterSum_eq_integral_bromwichSum hx]

end AnalyticNumberTheory.LargeSieve
