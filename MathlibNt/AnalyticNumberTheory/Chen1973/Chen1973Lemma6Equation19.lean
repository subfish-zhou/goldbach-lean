/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equations16And17
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equations14And15ScalarPayments

/-!
# Chen 1973, Lemma 6, equation (19)

This file isolates the finite Cauchy--Schwarz/Hölder step in (19).  All four
moments below are moments of the literal pair polynomial, `1-LS`, `S`, and
`L'`; no free `Phi` occurs.  The legacy height uses a natural ceiling
with the finite conductor maximum W; the printed exponential cutoff
`H = 2^l (log x)^200 I_{l,x}` is treated in SourceWeightHeight.
-/

noncomputable section

open Classical Complex Finset MeasureTheory Set
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

/-- The actual conductor maximum W, not the printed exponential I_{l,x}.
Equation18Weight proves W² ≤ I_{l,x}; the legacy name Eq19I is retained.
The inserted value `1` makes the maximum total, including an empty cell. -/
def chen1973Lemma6Eq19I (x L level : ℕ) : ℝ :=
  ({1} ∪ (chen1973Lemma6ConductorBlock x L level).image
    (fun d => (3 : ℝ) ^ d.primeFactors.card)).max' (by simp)

/-- Legacy max-weight cutoff. The printed cutoff uses the larger exponential I;
see Eq19PrintedHeight in SourceWeightHeight. This definition is retained for
existing coarse-budget consumers, not asserted equal to the source cutoff. -/
def chen1973Lemma6Eq19Height (x L level : ℕ) : ℕ :=
  ⌈((2 : ℝ) ^ level * Real.log x ^ (200 : ℕ) *
    chen1973Lemma6Eq19I x L level)⌉₊

lemma chen1973Lemma6Eq19I_pos (x L level : ℕ) :
    0 < chen1973Lemma6Eq19I x L level := by
  unfold chen1973Lemma6Eq19I
  have h := Finset.le_max' ({1} ∪ (chen1973Lemma6ConductorBlock x L level).image
    (fun d => (3 : ℝ) ^ d.primeFactors.card)) 1 (by simp)
  linarith

lemma chen1973Lemma6_threePow_le_Eq19I
    {x L level d : ℕ} (hd : d ∈ chen1973Lemma6ConductorBlock x L level) :
    (3 : ℝ) ^ d.primeFactors.card ≤ chen1973Lemma6Eq19I x L level := by
  unfold chen1973Lemma6Eq19I
  apply Finset.le_max'
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩)

lemma chen1973Lemma6Eq19Height_cast_ge (x L level : ℕ) :
    ((2 : ℝ) ^ level * Real.log x ^ (200 : ℕ) *
      chen1973Lemma6Eq19I x L level) ≤ chen1973Lemma6Eq19Height x L level := by
  unfold chen1973Lemma6Eq19Height
  exact Nat.le_ceil
    ((2 : ℝ) ^ level * Real.log x ^ (200 : ℕ) *
      chen1973Lemma6Eq19I x L level)

private def eq19Weight (d : ℕ) : ℝ :=
  |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
    (3 : ℝ) ^ d.primeFactors.card / d

private def eq19PairPolynomial
    (x B k m : ℕ) {d : ℕ} (s : ℂ) (χ : PrimitiveCharacter d) : ℂ :=
  ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
    χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
      ((pp.1 * pp.2 : ℂ) ^ s *
        Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))

/-- The literal pair-polynomial second moment occurring in (19), with the
same squarefree cell weight as equation (17). -/
def chen1973Lemma6Eq19PairSecondMoment
    (x L level B k m : ℕ) (s : ℂ) : ℝ :=
  ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
    eq19Weight d * ∑ χ : PrimitiveCharacter d,
      ‖eq19PairPolynomial x B k m s χ‖ ^ 2

/-- The literal equation-(14) factor, retained on the actual equation-(17)
cell weight. -/
def chen1973Lemma6Eq19OneSubSecondMoment
    (x L level H : ℕ) (s : ℂ) : ℝ :=
  ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
    eq19Weight d * ∑ χ : PrimitiveCharacter d,
      ‖chen1973Lemma6OneSubLS H s χ‖ ^ 2

/-- The literal equation-(15) fourth moment on the equation-(17) cell. -/
def chen1973Lemma6Eq19MobiusFourthMoment
    (x L level H : ℕ) (s : ℂ) : ℝ :=
  ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
    eq19Weight d * ∑ χ : PrimitiveCharacter d,
      ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 4

/-- The fourth moment of the actual totalized derivative in the second term
of (17). -/
def chen1973Lemma6Eq19LDerivFourthMoment
    (x L level : ℕ) (s : ℂ) : ℝ :=
  ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
    eq19Weight d * ∑ χ : PrimitiveCharacter d,
      ‖chen1973PrimitiveLDeriv d s χ‖ ^ 4

private lemma eq19Weight_nonneg (d : ℕ) : 0 ≤ eq19Weight d := by
  unfold eq19Weight
  positivity

private lemma sum_norm_mul_le_sqrt
    {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (_hf : ∀ i, 0 ≤ f i) (_hg : ∀ i, 0 ≤ g i) :
    (∑ i, f i * g i) ≤
      Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) := by
  simpa using Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι) f g

/-- The first displayed Cauchy--Schwarz step of (19), before inserting the
paid equation-(14) scalar bound. -/
theorem chen1973Lemma6A_le_moment_product
    (x L level B k m H : ℕ) (s : ℂ) :
    chen1973Lemma6A x L level B k m H s ≤
      Real.sqrt (chen1973Lemma6Eq19PairSecondMoment x L level B k m s) *
      Real.sqrt (chen1973Lemma6Eq19OneSubSecondMoment x L level H s) := by
  unfold chen1973Lemma6A chen1973Lemma6Eq19PairSecondMoment
    chen1973Lemma6Eq19OneSubSecondMoment
  let S := chen1973Lemma6ConductorBlock x L level
  let P : ℕ → ℝ := fun d => Real.sqrt (eq19Weight d) *
    Real.sqrt (∑ χ : PrimitiveCharacter d, ‖eq19PairPolynomial x B k m s χ‖ ^ 2)
  let Q : ℕ → ℝ := fun d => Real.sqrt (eq19Weight d) *
    Real.sqrt (∑ χ : PrimitiveCharacter d, ‖chen1973Lemma6OneSubLS H s χ‖ ^ 2)
  -- First apply Cauchy--Schwarz over the primitive characters at each conductor.
  have hpoint : ∀ d ∈ S,
      eq19Weight d * ∑ χ : PrimitiveCharacter d,
        ‖eq19PairPolynomial x B k m s χ‖ *
          ‖chen1973Lemma6OneSubLS H s χ‖ ≤ P d * Q d := by
    intro d hd
    let AP : ℝ := ∑ χ : PrimitiveCharacter d, ‖eq19PairPolynomial x B k m s χ‖ ^ 2
    let AQ : ℝ := ∑ χ : PrimitiveCharacter d,
      ‖chen1973Lemma6OneSubLS H s χ‖ ^ 2
    have hc := sum_norm_mul_le_sqrt
      (fun χ : PrimitiveCharacter d => ‖eq19PairPolynomial x B k m s χ‖)
      (fun χ : PrimitiveCharacter d => ‖chen1973Lemma6OneSubLS H s χ‖)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    change _ ≤ Real.sqrt AP * Real.sqrt AQ at hc
    calc
      eq19Weight d * _ ≤ eq19Weight d * (Real.sqrt AP * Real.sqrt AQ) :=
        mul_le_mul_of_nonneg_left hc (eq19Weight_nonneg d)
      _ = P d * Q d := by
        dsimp [P, Q]
        change eq19Weight d * (Real.sqrt AP * Real.sqrt AQ) =
          (Real.sqrt (eq19Weight d) * Real.sqrt AP) *
            (Real.sqrt (eq19Weight d) * Real.sqrt AQ)
        rw [show (Real.sqrt (eq19Weight d) * Real.sqrt AP) *
            (Real.sqrt (eq19Weight d) * Real.sqrt AQ) =
            Real.sqrt (eq19Weight d) ^ 2 * (Real.sqrt AP * Real.sqrt AQ) by ring,
          Real.sq_sqrt (eq19Weight_nonneg d)]
  -- Then apply Cauchy--Schwarz over the conductor block.
  calc
    _ ≤ ∑ d ∈ S, P d * Q d := Finset.sum_le_sum hpoint
    _ ≤ Real.sqrt (∑ d ∈ S, P d ^ 2) * Real.sqrt (∑ d ∈ S, Q d ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt S P Q
    _ = _ := by
      congr 1 <;> apply congrArg Real.sqrt <;>
        apply Finset.sum_congr rfl <;> intro d hd <;>
        dsimp [P, Q] <;> rw [mul_pow, Real.sq_sqrt (eq19Weight_nonneg d)] <;>
        rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

end AnalyticNumberTheory.LargeSieve
