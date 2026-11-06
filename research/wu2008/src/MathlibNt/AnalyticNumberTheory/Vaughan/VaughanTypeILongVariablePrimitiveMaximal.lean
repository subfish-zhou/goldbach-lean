

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeILongVariable
import MathlibNt.AnalyticNumberTheory.LargeSieve.ImprimitiveConductorWeightLinear

/-!
 # Variable-length primitive maximal large sieve for Vaughan Type I

This module does not collect the products `d*m` (or `d*e*m`) back into one
coefficient sequence of length `N`.  Each short row keeps its physical prefix
length, and the Rademacher--Menshov loss is paid separately at that length.
Consequently the large-sieve ledger contains `primitiveLargeSieveConstant (L r) Q`
for each row `r`, rather than one copy of the length-`N` constant multiplying an
already collected length-`N` moment.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The exact row-by-row RHS of the variable-length maximal large sieve.  The
factor `(log₂ L+1)^2` is the explicit Rademacher--Menshov payment for a complete
prefix maximum in that row. -/
def variableLengthPrimitivePrefixBudget
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (c : ι → ℤ → ℂ)
    (L : ι → ℕ) (Q : ℕ) : ℝ :=
  ∑ r ∈ S, (((Nat.log2 (L r) + 1 : ℕ) : ℝ) ^ 2) *
    primitiveLargeSieveConstant (L r) Q *
      ∑ m ∈ Finset.Icc ((0 : ℤ) + 1) ((0 : ℤ) + L r), ‖c r m‖ ^ 2

/-- **Variable-length prefix large sieve.**  Every short row is sent to the
primitive maximal theorem at its own length.  In particular no ambient `N`
occurs in the analytic constant unless it is already one of the row lengths. -/
theorem weighted_primitive_variableLength_prefix_maximal
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (c : ι → ℤ → ℂ)
    (L : ι → ℕ) (Q : ℕ) (hQ : 0 < Q) :
    (∑ r ∈ S, ∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ) ≤
      variableLengthPrimitivePrefixBudget S c L Q := by
  unfold variableLengthPrimitivePrefixBudget
  apply Finset.sum_le_sum
  intro r hr
  exact weighted_primitive_prefix_maximal (c r) 0 (L r) Q hQ

/-- The long row in the first Type-I lane after fixing `d`. -/
def vaughanTypeIFirstRowCoeff (b : ℕ → ℂ) (d : ℕ) (m : ℤ) : ℂ :=
  b (d * m.toNat) * Real.log (m.toNat : ℝ)

/-- The long row in the middle Type-I lane after fixing the product `a=d*e`. -/
def vaughanTypeIMiddleRowCoeff (b : ℕ → ℂ) (a : ℕ) (m : ℤ) : ℂ :=
  b (a * m.toNat)

/-- First-lane physical row length. -/
def vaughanTypeIFirstRowLength (N d : ℕ) : ℕ := N / d

/-- Middle-lane physical row length, indexed by the short product `a=d*e`. -/
def vaughanTypeIMiddleRowLength (N a : ℕ) : ℕ := N / a

/-- The same middle row with the two short shells kept separate. -/
def vaughanTypeIMiddlePairRowCoeff
    (b : ℕ → ℂ) (de : ℕ × ℕ) (m : ℤ) : ℂ :=
  b (de.1 * de.2 * m.toNat)

def vaughanTypeIMiddlePairRowLength (N : ℕ) (de : ℕ × ℕ) : ℕ :=
  N / (de.1 * de.2)

/-- Literal Möbius square-energy on a first-lane shell. -/
def vaughanTypeIFirstShortEnergy (DS : Finset ℕ) : ℝ :=
  ∑ d ∈ DS, ‖(((ArithmeticFunction.moebius d : ℤ) : ℂ))‖ ^ 2

/-- Literal `μ²Λ²` energy on two middle-lane shells. -/
def vaughanTypeIMiddleShortEnergy (DS ES : Finset ℕ) : ℝ :=
  ∑ d ∈ DS, ∑ e ∈ ES,
    ‖(((ArithmeticFunction.moebius d : ℤ) : ℂ) *
      (ArithmeticFunction.vonMangoldt e : ℂ))‖ ^ 2


theorem vaughanTypeIMiddleShortEnergy_le_mangoldt
    (DS ES : Finset ℕ) :
    vaughanTypeIMiddleShortEnergy DS ES ≤
      (DS.card : ℝ) * ∑ e ∈ ES,
        ‖(ArithmeticFunction.vonMangoldt e : ℂ)‖ ^ 2 := by
  unfold vaughanTypeIMiddleShortEnergy
  calc
    _ ≤ ∑ _d ∈ DS, ∑ e ∈ ES,
        ‖(ArithmeticFunction.vonMangoldt e : ℂ)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      rw [norm_mul, mul_pow]
      have hμ : ‖(((ArithmeticFunction.moebius d : ℤ) : ℂ))‖ ^ 2 ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [h]
      exact mul_le_of_le_one_left (sq_nonneg _) (by simpa using hμ)
    _ = _ := by simp





/-- Linear-harmonic transport for an arbitrary nonnegative conductor family.
This local form avoids routing the Type-I module through an all-character
aggregate. -/
theorem imprimitive_conductor_window_family_le_linear_typeI
    (F : (d : ℕ) → PrimitiveCharacter d → ℝ)
    (hF : ∀ d ψ, 0 ≤ F d ψ) (Q C : ℕ) (hC : 0 < C) :
    (∑ d ∈ Finset.Icc C (2 * C),
      imprimitiveConductorWeight Q d * ∑ ψ : PrimitiveCharacter d, F d ψ) ≤
      ((Q / C : ℕ) : ℝ) * conductorHarmonicFactor (Q / C) *
        ∑ d ∈ Finset.Icc 1 (2 * C),
          ((d : ℝ) / (d.totient : ℝ)) * ∑ ψ : PrimitiveCharacter d, F d ψ := by
  exact imprimitive_conductor_window_le_weighted_primitive_linear F hF Q C hC


end

end AnalyticNumberTheory.LargeSieve
