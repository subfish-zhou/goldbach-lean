/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem
import Mathlib.Tactic

/-!
# Chen 1973, Lemma 6, equation (21): analytic payments

This disjoint leaf pays the finite low-conductor bookkeeping in the literal
`(log x)^200` contour estimate and isolates the genuinely analytic input at the
primitive-character, prime-pair level.  It also records a source-region prime
sum decay with the exponential factor produced by the line
`Re s = 1 - 1 / sqrt(log x)`.
-/

noncomputable section
set_option maxHeartbeats 1200000

open Classical Complex Finset MeasureTheory Set
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

/-- The remaining external analytic input for equation (21), stated at the
primitive-character and individual prime-pair level.  Its left side is the
actual vertical integral, including the corrected high-power Mellin kernel.
This is deliberately not an equation-(21) terminal bound. -/
def Chen1973Lemma6Eq21PrimitiveVerticalEstimate
    (Cvert : ℝ) (x L B k m : ℕ) : Prop :=
  0 ≤ Cvert ∧
    ∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
      ∀ χ : PrimitiveCharacter d,
        ∀ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          ‖(Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
              chen1973Lemma6Eq21VerticalIntegral x d χ pp‖ ≤
            Cvert * (((x : ℝ) / ((pp.1 : ℝ) * pp.2)) ^
              chen1973Lemma6Eq21Sigma x)

private lemma three_pow_primeFactors_card_le_two_mul
    {d : ℕ} (hd : Squarefree d) :
    (3 : ℕ) ^ d.primeFactors.card ≤ 2 * d := by
  have hprod : ∏ p ∈ d.primeFactors, p = d :=
    Nat.prod_primeFactors_of_squarefree hd
  calc
    (3 : ℕ) ^ d.primeFactors.card = ∏ _p ∈ d.primeFactors, 3 := by simp
    _ ≤ 2 * ∏ p ∈ d.primeFactors, p := by
      by_cases htwo : 2 ∈ d.primeFactors
      · rw [show d.primeFactors = insert 2 (d.primeFactors.erase 2) by
          exact (Finset.insert_erase htwo).symm]
        rw [Finset.prod_insert (by simp : 2 ∉ d.primeFactors.erase 2)]
        simp only [Finset.prod_const,
          Finset.prod_insert (by simp : 2 ∉ d.primeFactors.erase 2)]
        have hfac : ∀ p ∈ d.primeFactors.erase 2, 3 ≤ p := by
          intro p hp
          have hp' := Finset.mem_of_mem_erase hp
          have hprime := (Nat.mem_primeFactors.mp hp').1
          have hpne : p ≠ 2 := (Finset.mem_erase.mp hp).1
          have hp2 := hprime.two_le
          omega
        have hm := Finset.prod_le_prod (fun p hp => by omega)
          (fun p hp => hfac p hp)
        have hm' : (3 : ℕ) ^ (d.primeFactors.erase 2).card ≤
            ∏ p ∈ d.primeFactors.erase 2, p := by simpa using hm
        omega
      · have hfac : ∀ p ∈ d.primeFactors, 3 ≤ p := by
          intro p hp
          have hprime := (Nat.mem_primeFactors.mp hp).1
          have hpne : p ≠ 2 := fun h => htwo (h ▸ hp)
          have hp2 := hprime.two_le
          omega
        have hm := Finset.prod_le_prod (fun p hp => by omega)
          (fun p hp => hfac p hp)
        nlinarith
    _ = 2 * d := by rw [hprod]

private lemma primitiveCharacter_card_le_totient (d : ℕ) (hd : 0 < d) :
    Fintype.card (PrimitiveCharacter d) ≤ d.totient := by
  let _ : NeZero d := ⟨Nat.ne_of_gt hd⟩
  calc
    Fintype.card (PrimitiveCharacter d) ≤
        Fintype.card (DirichletCharacter ℂ d) :=
      @Fintype.card_subtype_le (DirichletCharacter ℂ d) _
        (fun χ => χ.IsPrimitive) _
    _ = d.totient := by
      have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ
        (a := (1 : ZMod d)) isUnit_one (1 : ZMod d)
      simpa using h

/-- Low-conductor weighted primitive-character mass. -/
def chen1973Lemma6Eq21ConductorMass (x L : ℕ) : ℝ :=
  ∑ d ∈ chen1973Lemma6ConductorBlock x L 0,
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
      (3 : ℝ) ^ d.primeFactors.card / d *
        Fintype.card (PrimitiveCharacter d)

/-- The literal level-zero conductor carrier costs at most `2 L²`.  This uses
both squarefreeness of the actual carrier and the finite count
`# primitive characters mod d ≤ φ(d) ≤ d`. -/
theorem chen1973Lemma6_eq21_conductorMass_le
    (x L : ℕ) :
    chen1973Lemma6Eq21ConductorMass x L ≤ 2 * (L : ℝ) ^ 2 := by
  unfold chen1973Lemma6Eq21ConductorMass
  calc
    (∑ d ∈ chen1973Lemma6ConductorBlock x L 0,
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        (3 : ℝ) ^ d.primeFactors.card / d *
          Fintype.card (PrimitiveCharacter d)) ≤
      ∑ _d ∈ chen1973Lemma6ConductorBlock x L 0, (2 * L : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd1 := chen1973Lemma6_eq21_one_lt_conductor hd
        have hdpos : 0 < d := by omega
        have hdL := chen1973Lemma6_eq21_conductor_le hd
        have hsq : Squarefree d := by
          rw [chen1973Lemma6_eq21_conductorBlock_eq] at hd
          exact (Finset.mem_filter.mp hd).2.2
        have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
        have hcardNat := primitiveCharacter_card_le_totient d hdpos
        have hcard : (Fintype.card (PrimitiveCharacter d) : ℝ) ≤ d := by
          exact_mod_cast hcardNat.trans (Nat.totient_le d)
        have hthreeNat := three_pow_primeFactors_card_le_two_mul hsq
        have hthree : (3 : ℝ) ^ d.primeFactors.card ≤ 2 * d := by
          exact_mod_cast hthreeNat
        have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
        calc
          |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              (3 : ℝ) ^ d.primeFactors.card / d *
                Fintype.card (PrimitiveCharacter d) ≤
            1 * (2 * d) / d * d := by gcongr
          _ = 2 * d := by field_simp
          _ ≤ 2 * L := by exact_mod_cast (Nat.mul_le_mul_left 2 hdL)
    _ = ((chen1973Lemma6ConductorBlock x L 0).card : ℝ) * (2 * L) := by simp
    _ ≤ (L : ℝ) * (2 * L) := by
      gcongr
      have hsub : chen1973Lemma6ConductorBlock x L 0 ⊆ Finset.Ioc 1 L := by
        intro d hd
        rw [chen1973Lemma6_eq21_conductorBlock_eq] at hd
        exact (Finset.mem_filter.mp hd).1
      exact_mod_cast (Finset.card_le_card hsub).trans (by simp)
    _ = 2 * (L : ℝ) ^ 2 := by ring

/-- The finite low-conductor mass is paid by the source's `(log x)^200` once
`L ≤ (log x)^100`. -/
theorem chen1973Lemma6_eq21_conductorMass_le_log200
    {x L B k m l₂ : ℕ}
    (P : Chen1973Lemma6Eq21SourceParameters x L B k m l₂) :
    chen1973Lemma6Eq21ConductorMass x L ≤
      2 * Real.log x ^ (200 : ℕ) := by
  refine (chen1973Lemma6_eq21_conductorMass_le x L).trans ?_
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have hlog100 : 0 ≤ Real.log x ^ (100 : ℕ) := by positivity
  have hsquare := mul_self_le_mul_self hL0 P.hL_lower
  calc
    2 * (L : ℝ) ^ 2 ≤ 2 * (Real.log x ^ (100 : ℕ)) ^ 2 := by nlinarith
    _ = 2 * Real.log x ^ (200 : ℕ) := by ring

/-- The actual contour majorant is bounded by the actual prime-region sum.
The only analytic premise is the narrow primitive vertical estimate above;
all conductor and character counting is discharged in this theorem. -/
theorem chen1973Lemma6_eq21_contour_le_log200_primeSum
    (Cvert : ℝ) {x L B k m l₂ : ℕ}
    (P : Chen1973Lemma6Eq21SourceParameters x L B k m l₂)
    (hregion : chen1973Lemma6PrimePairShell x B k m ⊆
      chen1973Lemma6Eq21PrimeRegion x)
    (hvert : Chen1973Lemma6Eq21PrimitiveVerticalEstimate Cvert x L B k m) :
    chen1973Lemma6Eq21ContourMajorant x L B k m ≤
      (2 * Cvert) * Real.log x ^ (200 : ℕ) *
        chen1973Lemma6Eq21PrimeSum x := by
  have hC : 0 ≤ Cvert := hvert.1
  have hprime0 := chen1973Lemma6_eq21_primeSum_nonneg x
  have hinner : ∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
      ∀ χ : PrimitiveCharacter d,
        ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
            chen1973Lemma6Eq21VerticalIntegral x d χ pp‖ ≤
          Cvert * chen1973Lemma6Eq21PrimeSum x := by
    intro d hd χ
    calc
      ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
            chen1973Lemma6Eq21VerticalIntegral x d χ pp‖ ≤
        ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          ‖(Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
            chen1973Lemma6Eq21VerticalIntegral x d χ pp‖ := by
              exact norm_sum_le _ _
      _ ≤ ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          Cvert * (((x : ℝ) / ((pp.1 : ℝ) * pp.2)) ^
            chen1973Lemma6Eq21Sigma x) := by
              apply Finset.sum_le_sum
              intro pp hpp
              exact hvert.2 d hd χ pp hpp
      _ ≤ ∑ pp ∈ chen1973Lemma6Eq21PrimeRegion x,
          Cvert * (((x : ℝ) / ((pp.1 : ℝ) * pp.2)) ^
            chen1973Lemma6Eq21Sigma x) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg hregion
              intro pp hpp hnot
              positivity
      _ = Cvert * chen1973Lemma6Eq21PrimeSum x := by
            unfold chen1973Lemma6Eq21PrimeSum
            rw [Finset.mul_sum]
  unfold chen1973Lemma6Eq21ContourMajorant
  calc
    (∑ d ∈ chen1973Lemma6ConductorBlock x L 0,
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        (3 : ℝ) ^ d.primeFactors.card / d *
        ∑ χ : PrimitiveCharacter d,
          ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
            (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
              chen1973Lemma6Eq21VerticalIntegral x d χ pp‖) ≤
      ∑ d ∈ chen1973Lemma6ConductorBlock x L 0,
        |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
          (3 : ℝ) ^ d.primeFactors.card / d *
          (Fintype.card (PrimitiveCharacter d) *
            (Cvert * chen1973Lemma6Eq21PrimeSum x)) := by
              apply Finset.sum_le_sum
              intro d hd
              apply mul_le_mul_of_nonneg_left
              · simpa using Finset.sum_le_card_nsmul Finset.univ
                  (fun χ : PrimitiveCharacter d =>
                    ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
                      (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
                        chen1973Lemma6Eq21VerticalIntegral x d χ pp‖)
                  (Cvert * chen1973Lemma6Eq21PrimeSum x)
                  (fun χ hχ => hinner d hd χ)
              · positivity
    _ = chen1973Lemma6Eq21ConductorMass x L *
          (Cvert * chen1973Lemma6Eq21PrimeSum x) := by
            unfold chen1973Lemma6Eq21ConductorMass
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro d hd
            ring
    _ ≤ (2 * Real.log x ^ (200 : ℕ)) *
          (Cvert * chen1973Lemma6Eq21PrimeSum x) := by
            apply mul_le_mul_of_nonneg_right
              (chen1973Lemma6_eq21_conductorMass_le_log200 P)
            positivity
    _ = (2 * Cvert) * Real.log x ^ (200 : ℕ) *
          chen1973Lemma6Eq21PrimeSum x := by ring

/-- Reciprocal mass on the exact equation-(21) prime-pair region. -/
def chen1973Lemma6Eq21PrimeReciprocalMass (x : ℕ) : ℝ :=
  ∑ pp ∈ chen1973Lemma6Eq21PrimeRegion x,
    1 / ((pp.1 : ℝ) * pp.2)

private def eq21FirstPrimeRectangle (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun p => p.Prime ∧
    (x : ℝ) ^ ((1 : ℝ) / 10) < p ∧
    (p : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3)

private def eq21SecondPrimeRectangle (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun p => p.Prime ∧
    (x : ℝ) ^ ((1 : ℝ) / 3) < p ∧
    (p : ℝ) ≤ (x : ℝ) ^ (1 : ℝ)

private lemma eq21_primeRegion_subset_rectangles (x : ℕ) :
    chen1973Lemma6Eq21PrimeRegion x ⊆
      (eq21FirstPrimeRectangle x).product (eq21SecondPrimeRectangle x) := by
  intro pp hpp
  simp only [chen1973Lemma6Eq21PrimeRegion, Finset.mem_filter] at hpp
  rcases hpp with ⟨hpair, hp₁lower, hp₁upper, hp₂lower, hp₂root⟩
  rw [chen1973Lemma5PrimePairs, Finset.mem_filter] at hpair
  rcases hpair with ⟨hpairRange, hp₁prime, hp₂prime, _⟩
  rcases Finset.mem_product.mp hpairRange with ⟨hp₁range, hp₂range⟩
  apply Finset.mem_product.mpr
  constructor
  · simp only [eq21FirstPrimeRectangle, Finset.mem_filter, Finset.mem_range]
    exact ⟨Finset.mem_range.mp hp₁range, hp₁prime, hp₁lower, hp₁upper⟩
  · simp only [eq21SecondPrimeRectangle, Finset.mem_filter, Finset.mem_range]
    have hp₂le : pp.2 ≤ x := by
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hp₂range)
    have hp₂leR : (pp.2 : ℝ) ≤ (x : ℝ) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
      exact_mod_cast hp₂le
    exact ⟨Finset.mem_range.mp hp₂range, hp₂prime, hp₂lower, hp₂leR⟩

/-- Mertens' theorem gives one absolute bound for the reciprocal mass of the
actual equation-(21) pair region.  The constraints coupling `p₁` and `p₂` are
only discarded after embedding the actual region into its two source exponent
rectangles. -/
theorem chen1973Lemma6_eq21_primeReciprocalMass_bounded :
    ∃ Cpair : ℝ, 0 ≤ Cpair ∧ ∀ x : ℕ, 3 ≤ x →
      chen1973Lemma6Eq21PrimeReciprocalMass x ≤ Cpair := by
  obtain ⟨C₁, hC₁⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.prime_reciprocal_sum_bounded
      ((1 : ℝ) / 10) ((1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨C₂, hC₂⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.prime_reciprocal_sum_bounded
      ((1 : ℝ) / 3) (1 : ℝ) (by norm_num) (by norm_num)
  refine ⟨C₁ * C₂, ?_, ?_⟩
  · have h₁ := hC₁ 3 (by omega)
    have h₂ := hC₂ 3 (by omega)
    exact mul_nonneg (le_trans (abs_nonneg _) h₁) (le_trans (abs_nonneg _) h₂)
  · intro x hx
    let S₁ : ℝ := ∑ p ∈ eq21FirstPrimeRectangle x, 1 / (p : ℝ)
    let S₂ : ℝ := ∑ p ∈ eq21SecondPrimeRectangle x, 1 / (p : ℝ)
    have hS₁0 : 0 ≤ S₁ := by dsimp [S₁]; positivity
    have hS₂0 : 0 ≤ S₂ := by dsimp [S₂]; positivity
    have hS₁ : S₁ ≤ C₁ := by
      apply (le_abs_self S₁).trans
      change |∑ p ∈ (Finset.range (x + 1)).filter (fun (p : ℕ) => p.Prime ∧
        (x : ℝ) ^ ((1 : ℝ) / 10) < (p : ℝ) ∧
        (p : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3)), 1 / (p : ℝ)| ≤ C₁
      exact hC₁ x (by omega)
    have hS₂ : S₂ ≤ C₂ := by
      apply (le_abs_self S₂).trans
      change |∑ p ∈ (Finset.range (x + 1)).filter (fun (p : ℕ) => p.Prime ∧
        (x : ℝ) ^ ((1 : ℝ) / 3) < (p : ℝ) ∧
        (p : ℝ) ≤ (x : ℝ) ^ (1 : ℝ)), 1 / (p : ℝ)| ≤ C₂
      exact hC₂ x (by omega)
    calc
      chen1973Lemma6Eq21PrimeReciprocalMass x ≤
          ∑ pp ∈ (eq21FirstPrimeRectangle x).product
              (eq21SecondPrimeRectangle x),
            1 / ((pp.1 : ℝ) * pp.2) := by
        unfold chen1973Lemma6Eq21PrimeReciprocalMass
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (eq21_primeRegion_subset_rectangles x)
        intro pp hpp hnot
        positivity
      _ = S₁ * S₂ := by
        dsimp [S₁, S₂]
        rw [Finset.sum_product]
        simp_rw [one_div, mul_inv]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
      _ ≤ C₁ * C₂ := mul_le_mul hS₁ hS₂ hS₂0 (le_trans hS₁0 hS₁)

/-- Exact pointwise suppression required from the geometry of the printed
prime region.  It contains no characters and no contour integral. -/
def Chen1973Lemma6Eq21PrimePointwiseDecay (x : ℕ) : Prop :=
  ∀ pp ∈ chen1973Lemma6Eq21PrimeRegion x,
    (((x : ℝ) / ((pp.1 : ℝ) * pp.2)) ^ chen1973Lemma6Eq21Sigma x) ≤
      ((x : ℝ) * Real.exp (-Real.sqrt (Real.log x) / 3)) /
        ((pp.1 : ℝ) * pp.2)

/-- The literal prime region itself supplies the pointwise exponential
suppression; no analytic estimate or conclusion-shaped premise is needed. -/
theorem chen1973Lemma6_eq21_primePointwiseDecay
    {x : ℕ} (hx : 3 ≤ x) :
    Chen1973Lemma6Eq21PrimePointwiseDecay x := by
  intro pp hpp
  simp only [chen1973Lemma6Eq21PrimeRegion, Finset.mem_filter] at hpp
  rcases hpp with ⟨hpair, hp₁lower, hp₁upper, hp₂lower, hp₂root⟩
  rw [chen1973Lemma5PrimePairs, Finset.mem_filter] at hpair
  rcases hpair with ⟨_, hp₁prime, hp₂prime, _⟩
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_pos.2 hlog
  have hp₁0 : (0 : ℝ) < pp.1 := by exact_mod_cast hp₁prime.pos
  have hp₂0 : (0 : ℝ) < pp.2 := by exact_mod_cast hp₂prime.pos
  let A : ℝ := (x : ℝ) ^ ((1 : ℝ) / 3)
  let y : ℝ := (x : ℝ) / ((pp.1 : ℝ) * pp.2)
  have hA0 : 0 < A := by dsimp [A]; positivity
  have hden0 : 0 < (pp.1 : ℝ) * pp.2 := mul_pos hp₁0 hp₂0
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hA3 : A ^ 3 = (x : ℝ) := by
    dsimp [A]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hx0)]
    norm_num
  have hp₂sq : (pp.2 : ℝ) ^ 2 ≤ (x : ℝ) / pp.1 := by
    exact (Real.le_sqrt (by positivity) (by positivity)).mp hp₂root
  have hp₁p₂sq : (pp.1 : ℝ) * (pp.2 : ℝ) ^ 2 ≤ (x : ℝ) := by
    calc
      (pp.1 : ℝ) * (pp.2 : ℝ) ^ 2 ≤
          (pp.1 : ℝ) * ((x : ℝ) / pp.1) :=
        mul_le_mul_of_nonneg_left hp₂sq (le_of_lt hp₁0)
      _ = (x : ℝ) := by field_simp
  have hp₁leA : (pp.1 : ℝ) ≤ A := by exact hp₁upper
  have hp₁p₂leA2 : (pp.1 : ℝ) * pp.2 ≤ A ^ 2 := by
    by_contra hnot
    have hlt : A ^ 2 < (pp.1 : ℝ) * pp.2 := lt_of_not_ge hnot
    have hsq := mul_self_lt_mul_self (sq_nonneg A) hlt
    have hupper : ((pp.1 : ℝ) * pp.2) * ((pp.1 : ℝ) * pp.2) ≤
        (A ^ 2) * (A ^ 2) := by
      calc
        ((pp.1 : ℝ) * pp.2) * ((pp.1 : ℝ) * pp.2) =
            (pp.1 : ℝ) * ((pp.1 : ℝ) * (pp.2 : ℝ) ^ 2) := by ring
        _ ≤ A * (x : ℝ) :=
          mul_le_mul hp₁leA hp₁p₂sq (by positivity) (le_of_lt hA0)
        _ = (A ^ 2) * (A ^ 2) := by rw [← hA3]; ring
    exact (not_lt_of_ge hupper) hsq
  have hAy : A ≤ y := by
    rw [show y = (x : ℝ) / ((pp.1 : ℝ) * pp.2) by rfl]
    apply (le_div_iff₀ hden0).2
    calc
      A * ((pp.1 : ℝ) * pp.2) ≤ A * A ^ 2 :=
        mul_le_mul_of_nonneg_left hp₁p₂leA2 (le_of_lt hA0)
      _ = (x : ℝ) := by rw [← hA3]; ring
  have hlogy : Real.log (x : ℝ) / 3 ≤ Real.log y := by
    calc
      Real.log (x : ℝ) / 3 = Real.log A := by
        dsimp [A]
        rw [Real.log_rpow hx0]
        ring
      _ ≤ Real.log y := Real.log_le_log hA0 hAy
  change y ^ chen1973Lemma6Eq21Sigma x ≤
    (x : ℝ) * Real.exp (-Real.sqrt (Real.log x) / 3) /
      ((pp.1 : ℝ) * pp.2)
  rw [show (x : ℝ) * Real.exp (-Real.sqrt (Real.log x) / 3) /
      ((pp.1 : ℝ) * pp.2) =
      y * Real.exp (-Real.sqrt (Real.log x) / 3) by
        dsimp [y]
        ring]
  rw [Real.rpow_def_of_pos hy0]
  unfold chen1973Lemma6Eq21Sigma
  have hsqrt_sq : Real.sqrt (Real.log (x : ℝ)) ^ 2 = Real.log (x : ℝ) :=
    Real.sq_sqrt (le_of_lt hlog)
  calc
    Real.exp (Real.log y * (1 - 1 / Real.sqrt (Real.log (x : ℝ)))) ≤
        Real.exp (Real.log y - Real.sqrt (Real.log (x : ℝ)) / 3) := by
      apply Real.exp_le_exp.mpr
      rw [show Real.log y * (1 - 1 / Real.sqrt (Real.log (x : ℝ))) =
        Real.log y - Real.log y / Real.sqrt (Real.log (x : ℝ)) by ring]
      have hdiv := (div_le_div_iff_of_pos_right hsqrt).2 hlogy
      have hsqrt_ne : Real.sqrt (Real.log (x : ℝ)) ≠ 0 := ne_of_gt hsqrt
      have hnum : Real.log (x : ℝ) / 3 =
          Real.sqrt (Real.log (x : ℝ)) ^ 2 / 3 := by
        rw [hsqrt_sq]
      have hquot : Real.log (x : ℝ) / 3 /
          Real.sqrt (Real.log (x : ℝ)) =
          Real.sqrt (Real.log (x : ℝ)) / 3 := by
        rw [hnum]
        field_simp
      rw [hquot] at hdiv
      linarith
    _ = y * Real.exp (-Real.sqrt (Real.log (x : ℝ)) / 3) := by
      rw [show Real.log y - Real.sqrt (Real.log (x : ℝ)) / 3 =
        Real.log y + (-Real.sqrt (Real.log (x : ℝ)) / 3) by ring]
      rw [Real.exp_add, Real.exp_log hy0]

/-- Explicit exponential decay of the actual prime-pair sum.  All prime
counting is unconditional (Mertens); `hpoint` is the remaining elementary
rpow/geometric normalization on the literal source region. -/
theorem chen1973Lemma6_eq21_primeSum_exponential_decay
    (Cpair : ℝ)
    (hmertens : ∀ x : ℕ, 3 ≤ x →
      chen1973Lemma6Eq21PrimeReciprocalMass x ≤ Cpair)
    {x : ℕ} (hx : 3 ≤ x) :
    chen1973Lemma6Eq21PrimeSum x ≤
      Cpair * (x : ℝ) * Real.exp (-Real.sqrt (Real.log x) / 3) := by
  unfold chen1973Lemma6Eq21PrimeSum
  calc
    (∑ pp ∈ chen1973Lemma6Eq21PrimeRegion x,
      ((x : ℝ) / ((pp.1 : ℝ) * pp.2)) ^ chen1973Lemma6Eq21Sigma x) ≤
      ∑ pp ∈ chen1973Lemma6Eq21PrimeRegion x,
        ((x : ℝ) * Real.exp (-Real.sqrt (Real.log x) / 3)) /
          ((pp.1 : ℝ) * pp.2) := by
            apply Finset.sum_le_sum
            intro pp hpp
            exact chen1973Lemma6_eq21_primePointwiseDecay hx pp hpp
    _ = ((x : ℝ) * Real.exp (-Real.sqrt (Real.log x) / 3)) *
        chen1973Lemma6Eq21PrimeReciprocalMass x := by
          unfold chen1973Lemma6Eq21PrimeReciprocalMass
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro pp hpp
          ring
    _ ≤ ((x : ℝ) * Real.exp (-Real.sqrt (Real.log x) / 3)) * Cpair := by
          apply mul_le_mul_of_nonneg_left (hmertens x hx)
          positivity
    _ = Cpair * (x : ℝ) * Real.exp (-Real.sqrt (Real.log x) / 3) := by ring

/-- The explicit large-`x` scalar inequality that converts exponential
suppression into the printed `log^{-220}` payment. -/
theorem chen1973Lemma6_eq21_primeSum_log220_decay
    (Cpair : ℝ)
    (hmertens : ∀ x : ℕ, 3 ≤ x →
      chen1973Lemma6Eq21PrimeReciprocalMass x ≤ Cpair)
    {x : ℕ} (hx : 3 ≤ x)
    (hlarge : Cpair * Real.exp (-Real.sqrt (Real.log x) / 3) *
        Real.log x ^ (220 : ℕ) ≤ 1) :
    chen1973Lemma6Eq21PrimeSum x ≤
      (x : ℝ) / Real.log x ^ (220 : ℕ) := by
  have hdecay := chen1973Lemma6_eq21_primeSum_exponential_decay
    Cpair hmertens hx
  have hlog : 0 < Real.log x := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  rw [le_div_iff₀ (pow_pos hlog 220)]
  calc
    chen1973Lemma6Eq21PrimeSum x * Real.log x ^ (220 : ℕ) ≤
        (Cpair * (x : ℝ) * Real.exp (-Real.sqrt (Real.log x) / 3)) *
          Real.log x ^ (220 : ℕ) := by gcongr
    _ = (x : ℝ) * (Cpair * Real.exp (-Real.sqrt (Real.log x) / 3) *
          Real.log x ^ (220 : ℕ)) := by ring
    _ ≤ (x : ℝ) * 1 := by gcongr
    _ = (x : ℝ) := by ring

/-- Exponential decay dominates the exact `log^220` payment for every fixed
constant.  This theorem supplies the large-`x` threshold that was previously a
pointwise scalar premise. -/
theorem chen1973Lemma6_eq21_eventually_exp_log220_le_one (Cpair : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop,
      Cpair * Real.exp (-Real.sqrt (Real.log x) / 3) *
        Real.log x ^ (220 : ℕ) ≤ 1 := by
  have hsqrtLog : Filter.Tendsto
      (fun x : ℕ => Real.sqrt (Real.log (x : ℝ))) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlo := (isLittleO_pow_exp_pos_mul_atTop 440
    (by norm_num : (0 : ℝ) < 1 / 3)).comp_tendsto hsqrtLog
  have heps : 0 < (1 / (|Cpair| + 1) : ℝ) := by positivity
  have hbound := hlo.bound heps
  filter_upwards [hbound,
    Filter.eventually_ge_atTop (1 : ℕ)] with x hx hx1
  have hlog0 : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast hx1)
  have hsqrt0 : 0 ≤ Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_nonneg _
  have hpow : Real.sqrt (Real.log (x : ℝ)) ^ (440 : ℕ) ≤
      (1 / (|Cpair| + 1)) *
        Real.exp ((1 / 3 : ℝ) * Real.sqrt (Real.log (x : ℝ))) := by
    simpa only [Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hsqrt0 _),
      abs_of_pos (Real.exp_pos _)] using hx
  have hlogpow : Real.log (x : ℝ) ^ (220 : ℕ) =
      Real.sqrt (Real.log (x : ℝ)) ^ (440 : ℕ) := by
    calc
      Real.log (x : ℝ) ^ (220 : ℕ) =
          (Real.sqrt (Real.log (x : ℝ)) ^ 2) ^ (220 : ℕ) := by
            rw [Real.sq_sqrt hlog0]
      _ = Real.sqrt (Real.log (x : ℝ)) ^ (440 : ℕ) := by ring
  rw [hlogpow]
  calc
    Cpair * Real.exp (-Real.sqrt (Real.log (x : ℝ)) / 3) *
        Real.sqrt (Real.log (x : ℝ)) ^ (440 : ℕ) ≤
      |Cpair| * Real.exp (-Real.sqrt (Real.log (x : ℝ)) / 3) *
        Real.sqrt (Real.log (x : ℝ)) ^ (440 : ℕ) := by
          gcongr
          exact le_abs_self Cpair
    _ ≤ |Cpair| * Real.exp (-Real.sqrt (Real.log (x : ℝ)) / 3) *
        ((1 / (|Cpair| + 1)) *
          Real.exp ((1 / 3 : ℝ) * Real.sqrt (Real.log (x : ℝ)))) := by
            gcongr
    _ = |Cpair| / (|Cpair| + 1) := by
      rw [show -Real.sqrt (Real.log (x : ℝ)) / 3 =
        -((1 / 3 : ℝ) * Real.sqrt (Real.log (x : ℝ))) by ring,
        Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    _ ≤ 1 := by
      rw [div_le_one (by positivity : 0 < |Cpair| + 1)]
      linarith [abs_nonneg Cpair]

/-- Eventual equation-(21) prime-sum payment, with the scalar `hlarge`
completely discharged and the cutoff quantified before `x`. -/
theorem chen1973Lemma6_eq21_primeSum_log220_decay_eventually
    (Cpair : ℝ)
    (hmertens : ∀ x : ℕ, 3 ≤ x →
      chen1973Lemma6Eq21PrimeReciprocalMass x ≤ Cpair) :
    ∃ x₀ : ℕ, ∀ x ≥ x₀,
      chen1973Lemma6Eq21PrimeSum x ≤
        (x : ℝ) / Real.log x ^ (220 : ℕ) := by
  rw [← Filter.eventually_atTop]
  filter_upwards [chen1973Lemma6_eq21_eventually_exp_log220_le_one Cpair,
    Filter.eventually_ge_atTop (3 : ℕ)] with x hlarge hx
  exact chen1973Lemma6_eq21_primeSum_log220_decay Cpair hmertens hx hlarge

/-- Production analytic payment for equation (21).  For a fixed constant in the
primitive vertical estimate, one cutoff works for every later source cell; the
finite conductor mass, prime reciprocal mass, and the entire `log^220` scalar
payment are internal. -/
theorem chen1973Lemma6_eq21_contour_log20_decay_eventually
    (Cvert : ℝ) :
    ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ L B k m l₂ : ℕ,
      Chen1973Lemma6Eq21SourceParameters x L B k m l₂ →
      chen1973Lemma6PrimePairShell x B k m ⊆
        chen1973Lemma6Eq21PrimeRegion x →
      Chen1973Lemma6Eq21PrimitiveVerticalEstimate Cvert x L B k m →
      chen1973Lemma6Eq21ContourMajorant x L B k m ≤
        (x : ℝ) / Real.log x ^ (20 : ℕ) := by
  obtain ⟨Cpair, _, hmertens⟩ :=
    chen1973Lemma6_eq21_primeReciprocalMass_bounded
  rw [← Filter.eventually_atTop]
  filter_upwards [
    chen1973Lemma6_eq21_eventually_exp_log220_le_one (2 * Cvert * Cpair),
    Filter.eventually_ge_atTop (3 : ℕ)] with x hlarge hx
  intro L B k m l₂ P hregion hvert
  have hCvert : 0 ≤ Cvert := hvert.1
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hcontour := chen1973Lemma6_eq21_contour_le_log200_primeSum
    Cvert P hregion hvert
  have hprime := chen1973Lemma6_eq21_primeSum_exponential_decay
    Cpair hmertens hx
  rw [le_div_iff₀ (pow_pos hlog 20)]
  calc
    chen1973Lemma6Eq21ContourMajorant x L B k m *
        Real.log (x : ℝ) ^ (20 : ℕ) ≤
      ((2 * Cvert) * Real.log (x : ℝ) ^ (200 : ℕ) *
        chen1973Lemma6Eq21PrimeSum x) *
          Real.log (x : ℝ) ^ (20 : ℕ) := by gcongr
    _ ≤ ((2 * Cvert) * Real.log (x : ℝ) ^ (200 : ℕ) *
        (Cpair * (x : ℝ) *
          Real.exp (-Real.sqrt (Real.log (x : ℝ)) / 3))) *
            Real.log (x : ℝ) ^ (20 : ℕ) := by
              gcongr
    _ = (x : ℝ) * ((2 * Cvert * Cpair) *
        Real.exp (-Real.sqrt (Real.log (x : ℝ)) / 3) *
          Real.log (x : ℝ) ^ (220 : ℕ)) := by ring
    _ ≤ (x : ℝ) * 1 := by gcongr
    _ = (x : ℝ) := by ring

end AnalyticNumberTheory.LargeSieve
