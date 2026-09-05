

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

theorem vaughanTypeIFirstShortEnergy_le_card (DS : Finset ℕ) :
    vaughanTypeIFirstShortEnergy DS ≤ (DS.card : ℝ) := by
  unfold vaughanTypeIFirstShortEnergy
  calc
    _ ≤ ∑ _d ∈ DS, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [h]
    _ = _ := by simp

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

/-- First Type-I dyadic row ledger.  This is the genuine long-variable
primitive estimate: the `d`th row uses length `N/d`. -/
theorem weighted_primitive_vaughanTypeIFirstRows
    (b : ℕ → ℂ) (N Q : ℕ) (DS : Finset ℕ) (hQ : 0 < Q) :
    (∑ d ∈ DS, ∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare
            (vaughanTypeIFirstRowCoeff b d) 0 (N / d) q χ) ≤
      variableLengthPrimitivePrefixBudget DS
        (vaughanTypeIFirstRowCoeff b) (vaughanTypeIFirstRowLength N) Q := by
  simpa [vaughanTypeIFirstRowLength] using
    weighted_primitive_variableLength_prefix_maximal DS
      (vaughanTypeIFirstRowCoeff b) (vaughanTypeIFirstRowLength N) Q hQ

/-- Middle Type-I row ledger after grouping the two short variables by their
product `a=d*e`.  A two-shell implementation can map each `(d,e)` to this same
row interface without changing the physical length `N/(d*e)`. -/
theorem weighted_primitive_vaughanTypeIMiddleRows
    (b : ℕ → ℂ) (N Q : ℕ) (AS : Finset ℕ) (hQ : 0 < Q) :
    (∑ a ∈ AS, ∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare
            (vaughanTypeIMiddleRowCoeff b a) 0 (N / a) q χ) ≤
      variableLengthPrimitivePrefixBudget AS
        (vaughanTypeIMiddleRowCoeff b) (vaughanTypeIMiddleRowLength N) Q := by
  simpa [vaughanTypeIMiddleRowLength] using
    weighted_primitive_variableLength_prefix_maximal AS
      (vaughanTypeIMiddleRowCoeff b) (vaughanTypeIMiddleRowLength N) Q hQ

/-- Two-shell version of the middle lane; the inner maximal large sieve is
still applied at the variable length `N/(d*e)`. -/
theorem weighted_primitive_vaughanTypeIMiddlePairRows
    (b : ℕ → ℂ) (N Q : ℕ) (DS ES : Finset ℕ) (hQ : 0 < Q) :
    (∑ de ∈ DS ×ˢ ES, ∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare
            (vaughanTypeIMiddlePairRowCoeff b de) 0
              (N / (de.1 * de.2)) q χ) ≤
      variableLengthPrimitivePrefixBudget (DS ×ˢ ES)
        (vaughanTypeIMiddlePairRowCoeff b)
        (vaughanTypeIMiddlePairRowLength N) Q := by
  simpa [vaughanTypeIMiddlePairRowLength] using
    weighted_primitive_variableLength_prefix_maximal (DS ×ˢ ES)
      (vaughanTypeIMiddlePairRowCoeff b)
      (vaughanTypeIMiddlePairRowLength N) Q hQ

/-- Abstract physical-scale compression.  If the RM-weighted energy of every
row is at most one, the length contribution is `#S * Lmax`, not `N` times a
collected moment.  The hypothesis `#S * Lmax ≤ N` then gives exactly
`N + #S * K(Q) Q²`. -/
theorem variableLengthPrimitivePrefixBudget_le_physicalScale
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (c : ι → ℤ → ℂ)
    (L : ι → ℕ) (N Lmax Q : ℕ)
    (hL : ∀ r ∈ S, L r ≤ Lmax)
    (hpack : S.card * Lmax ≤ N)
    (henergy : ∀ r ∈ S,
      (((Nat.log2 (L r) + 1 : ℕ) : ℝ) ^ 2) *
        (∑ m ∈ Finset.Icc ((0 : ℤ) + 1) ((0 : ℤ) + L r), ‖c r m‖ ^ 2) ≤ 1) :
    variableLengthPrimitivePrefixBudget S c L Q ≤
      (N : ℝ) + (S.card : ℝ) *
        ((2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
          (Q : ℝ) ^ 2) := by
  unfold variableLengthPrimitivePrefixBudget primitiveLargeSieveConstant
  let K : ℝ :=
    (2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
      (Q : ℝ) ^ 2
  calc
    (∑ r ∈ S, (((Nat.log2 (L r) + 1 : ℕ) : ℝ) ^ 2) *
        ((L r : ℝ) + K) *
          ∑ m ∈ Finset.Icc ((0 : ℤ) + 1) ((0 : ℤ) + L r), ‖c r m‖ ^ 2) =
      ∑ r ∈ S, ((L r : ℝ) + K) *
        ((((Nat.log2 (L r) + 1 : ℕ) : ℝ) ^ 2) *
          ∑ m ∈ Finset.Icc ((0 : ℤ) + 1) ((0 : ℤ) + L r), ‖c r m‖ ^ 2) := by
            apply Finset.sum_congr rfl
            intro r hr
            ring
    _ ≤ ∑ _r ∈ S, ((Lmax : ℝ) + K) := by
      apply Finset.sum_le_sum
      intro r hr
      have hLK : (L r : ℝ) + K ≤ (Lmax : ℝ) + K := by
        gcongr
        exact_mod_cast hL r hr
      have hfactor0 : 0 ≤ (L r : ℝ) + K := by
        dsimp [K]
        positivity
      calc
        ((L r : ℝ) + K) *
            ((((Nat.log2 (L r) + 1 : ℕ) : ℝ) ^ 2) *
              ∑ m ∈ Finset.Icc ((0 : ℤ) + 1) ((0 : ℤ) + L r), ‖c r m‖ ^ 2)
          ≤ ((L r : ℝ) + K) * 1 :=
            mul_le_mul_of_nonneg_left (henergy r hr) hfactor0
        _ ≤ ((Lmax : ℝ) + K) := by simpa using hLK
    _ = (S.card : ℝ) * (Lmax : ℝ) + (S.card : ℝ) * K := by
      simp
    _ ≤ (N : ℝ) + (S.card : ℝ) * K := by
      gcongr
      exact_mod_cast hpack
    _ = _ := by rfl

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
  calc
    _ ≤ ∑ d ∈ Finset.Icc C (2 * C),
        (((d : ℝ) / (d.totient : ℝ)) * ((Q / C : ℕ) : ℝ) *
          conductorHarmonicFactor (Q / C)) * ∑ ψ : PrimitiveCharacter d, F d ψ := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hd : 0 < d := hC.trans_le (Finset.mem_Icc.mp hdmem).1
      have hdiv : Q / d ≤ Q / C :=
        Nat.div_le_div_left (Finset.mem_Icc.mp hdmem).1 hC
      have hharm : conductorHarmonicFactor (Q / d) ≤
          conductorHarmonicFactor (Q / C) := by
        unfold conductorHarmonicFactor
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Icc_subset_Icc_right hdiv
        · intro e he hnot
          positivity
      have hsum : 0 ≤ ∑ ψ : PrimitiveCharacter d, F d ψ :=
        Finset.sum_nonneg fun ψ _ => hF d ψ
      apply mul_le_mul_of_nonneg_right _ hsum
      refine (imprimitiveConductorWeight_le_linear_harmonic Q d hd).trans ?_
      gcongr
      exact conductorHarmonicFactor_nonneg _
    _ ≤ ∑ d ∈ Finset.Icc 1 (2 * C),
        (((d : ℝ) / (d.totient : ℝ)) * ((Q / C : ℕ) : ℝ) *
          conductorHarmonicFactor (Q / C)) * ∑ ψ : PrimitiveCharacter d, F d ψ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr
          ⟨hC.trans_le (Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2⟩
      · intro d hd hnot
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (div_nonneg (by positivity) (by positivity))
            (by positivity)) (conductorHarmonicFactor_nonneg _))
          (Finset.sum_nonneg fun ψ _ => hF d ψ)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring

/-- Linear-harmonic imprimitive conductor transport applied *before* the
variable row lengths are forgotten.  This is the connector used on every
dyadic conductor window. -/
theorem imprimitive_conductor_window_variableLength_prefix_le_linear
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (c : ι → ℤ → ℂ)
    (L : ι → ℕ) (Q C : ℕ) (hC : 0 < C) :
    (∑ d ∈ Finset.Icc C (2 * C), imprimitiveConductorWeight Q d *
      ∑ ψ : PrimitiveCharacter d,
        ∑ r ∈ S, primitiveCharacterPrefixMaxSquare (c r) 0 (L r) d ψ) ≤
      ((Q / C : ℕ) : ℝ) * conductorHarmonicFactor (Q / C) *
        variableLengthPrimitivePrefixBudget S c L (2 * C) := by
  let F : (d : ℕ) → PrimitiveCharacter d → ℝ := fun d ψ =>
    ∑ r ∈ S, primitiveCharacterPrefixMaxSquare (c r) 0 (L r) d ψ
  have htransport := imprimitive_conductor_window_family_le_linear_typeI
    F (fun d ψ => Finset.sum_nonneg fun r _ =>
      primitiveCharacterPrefixMaxSquare_nonneg (c r) 0 (L r) d ψ) Q C hC
  refine htransport.trans ?_
  apply mul_le_mul_of_nonneg_left
  · calc
      (∑ d ∈ Finset.Icc 1 (2 * C), ((d : ℝ) / (d.totient : ℝ)) *
          ∑ ψ : PrimitiveCharacter d, F d ψ) =
        ∑ r ∈ S, ∑ d ∈ Finset.Icc 1 (2 * C),
          ((d : ℝ) / (d.totient : ℝ)) *
            ∑ ψ : PrimitiveCharacter d,
              primitiveCharacterPrefixMaxSquare (c r) 0 (L r) d ψ := by
        change (∑ d ∈ Finset.Icc 1 (2 * C), ((d : ℝ) / (d.totient : ℝ)) *
            ∑ ψ : PrimitiveCharacter d,
              ∑ r ∈ S, primitiveCharacterPrefixMaxSquare (c r) 0 (L r) d ψ) = _
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.sum_comm]
      _ ≤ variableLengthPrimitivePrefixBudget S c L (2 * C) :=
        weighted_primitive_variableLength_prefix_maximal S c L (2 * C)
          (Nat.mul_pos (by decide) hC)
  · exact mul_nonneg (by positivity) (conductorHarmonicFactor_nonneg _)

end

end AnalyticNumberTheory.LargeSieve
