

import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVSquareMeanToL1Dyadic
import MathlibNt.AnalyticNumberTheory.LargeSieve.DirectConductorWeight

/-!
 # Direct L¹ Vaughan route at the physical scale

This module deliberately does not pass through a square mean for the complete
von Mangoldt coefficient sequence.  It proves the finite character, conductor,
and Vaughan assembly for the literal prefix maxima.  The main unresolved
analytic interfaces are the Type-I and Type-II *mean values themselves*; the
small/correction terms remain visible, while the reciprocal-totient conductor
weight is discharged by a separate unconditional finite-arithmetic module.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section

/-- Unsquared primitive-character prefix maximum. -/
def primitivePrefixAmplitude (a : ℤ → ℂ) (N q : ℕ)
    (χ : PrimitiveCharacter q) : ℝ :=
  Real.sqrt (primitiveCharacterPrefixMaxSquare a 0 N q χ)

lemma primitivePrefixAmplitude_nonneg (a : ℤ → ℂ) (N q : ℕ)
    (χ : PrimitiveCharacter q) : 0 ≤ primitivePrefixAmplitude a N q χ :=
  Real.sqrt_nonneg _

lemma primitivePrefixAmplitude_sq (a : ℤ → ℂ) (N q : ℕ)
    (χ : PrimitiveCharacter q) :
    primitivePrefixAmplitude a N q χ ^ 2 =
      primitiveCharacterPrefixMaxSquare a 0 N q χ := by
  apply Real.sq_sqrt
  exact primitiveCharacterPrefixMaxSquare_nonneg a 0 N q χ


/-- Direct all-character nonprincipal prefix mean before conductor reduction. -/
def directAllCharacterMean (a : ℤ → ℂ) (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    ∑ χ ∈ nonprincipalCharacters q, nonprincipalPrefixAmplitude a N q χ


/-- Exact conductor regrouping with the direct `1/φ(q)` weight. -/
theorem direct_sum_nonprincipal_by_conductor
    (Q : ℕ) (F : (d : ℕ) → PrimitiveCharacter d → ℝ) :
    (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
      ∑ χ ∈ nonprincipalCharacters q,
        F χ.conductor (conductorPrimitiveCharacter χ)) =
      ∑ d ∈ Finset.Icc 2 Q, directConductorWeight Q d *
        ∑ ψ : PrimitiveCharacter d, F d ψ := by
  calc
    _ = ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
        ∑ d ∈ nonprincipalConductors q, ∑ ψ : PrimitiveCharacter d, F d ψ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [sum_nonprincipal_by_conductor (Finset.mem_Icc.mp hq).1 F]
    _ = ∑ q ∈ Finset.Icc 1 Q, ∑ d ∈ Finset.Icc 2 Q,
        if d ∣ q then ((q.totient : ℝ)⁻¹) *
          ∑ ψ : PrimitiveCharacter d, F d ψ else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum, ← Finset.sum_filter]
      apply Finset.sum_subset
      · intro d hd
        have hd' := Finset.mem_filter.mp hd
        have hddiv : d ∣ q := (Nat.mem_divisors.mp hd'.1).1
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hd'.2, (Nat.le_of_dvd (Finset.mem_Icc.mp hq).1 hddiv).trans
          (Finset.mem_Icc.mp hq).2⟩, hddiv⟩
      · intro d hdQ hdnot
        simp only [Finset.mem_filter] at hdQ
        exfalso
        apply hdnot
        rw [nonprincipalConductors, Finset.mem_filter]
        exact ⟨Nat.mem_divisors.mpr ⟨hdQ.2,
          Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩,
          (Finset.mem_Icc.mp hdQ.1).1⟩
    _ = ∑ d ∈ Finset.Icc 2 Q, ∑ q ∈ Finset.Icc 1 Q,
        if d ∣ q then ((q.totient : ℝ)⁻¹) *
          ∑ ψ : PrimitiveCharacter d, F d ψ else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [directConductorWeight, Finset.sum_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hdq : d ∣ q <;> simp [hdq]

/-- Prefix correction amplitude at change of level. -/
def conductorErrorAmplitude {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℤ → ℂ) (N : ℕ) : ℝ :=
  Real.sqrt (conductorErrorPrefixMaxSquare χ a 0 N)

lemma conductorErrorAmplitude_sq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℤ → ℂ) (N : ℕ) :
    conductorErrorAmplitude χ a N ^ 2 =
      conductorErrorPrefixMaxSquare χ a 0 N := by
  apply Real.sq_sqrt
  unfold conductorErrorPrefixMaxSquare
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨0, by simp, by simp [conductorErrorPrefixSquare]⟩

lemma conductorErrorAmplitude_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℤ → ℂ) (N : ℕ) : 0 ≤ conductorErrorAmplitude χ a N :=
  Real.sqrt_nonneg _

private lemma amplitude_two_piece
    {x a b : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : x ^ 2 ≤ 2 * (a ^ 2 + b ^ 2)) : x ≤ 2 * (a + b) := by
  nlinarith [sq_nonneg (a + b)]

lemma nonprincipalAmplitude_le_conductor
    {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ℤ → ℂ) (N : ℕ) :
    nonprincipalPrefixAmplitude a N q χ ≤
      2 * (primitivePrefixAmplitude a N χ.conductor
        (conductorPrimitiveCharacter χ) + conductorErrorAmplitude χ a N) := by
  apply amplitude_two_piece
  · exact nonprincipalPrefixAmplitude_nonneg _ _ _ _
  · exact primitivePrefixAmplitude_nonneg _ _ _ _
  · exact conductorErrorAmplitude_nonneg _ _ _
  · rw [nonprincipalPrefixAmplitude_sq, primitivePrefixAmplitude_sq,
      conductorErrorAmplitude_sq]
    apply characterPrefixMaxSquare_le_conductor_add_error

/-- Literal correction mean; this is separate from the Type-I/II hybrid input. -/
def directConductorCorrectionMean (a : ℤ → ℂ) (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    ∑ χ ∈ nonprincipalCharacters q, conductorErrorAmplitude χ a N

/-- Finite all-character to primitive-conductor L¹ reduction. -/
theorem directAllCharacterMean_le_conductor
    (a : ℤ → ℂ) (N Q : ℕ) :
    directAllCharacterMean a N Q ≤
      2 * (∑ d ∈ Finset.Icc 2 Q, directConductorWeight Q d *
        ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) +
      2 * directConductorCorrectionMean a N Q := by
  unfold directAllCharacterMean directConductorCorrectionMean
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
        ∑ χ ∈ nonprincipalCharacters q,
          2 * (primitivePrefixAmplitude a N χ.conductor
            (conductorPrimitiveCharacter χ) + conductorErrorAmplitude χ a N) := by
      gcongr with q hq χ hχ
      exact nonprincipalAmplitude_le_conductor χ a N
    _ = 2 * (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
        ∑ χ ∈ nonprincipalCharacters q,
          primitivePrefixAmplitude a N χ.conductor
            (conductorPrimitiveCharacter χ)) +
        2 * (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
          ∑ χ ∈ nonprincipalCharacters q, conductorErrorAmplitude χ a N) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      ring
    _ = _ := by
      rw [direct_sum_nonprincipal_by_conductor]


end

end AnalyticNumberTheory.LargeSieve
