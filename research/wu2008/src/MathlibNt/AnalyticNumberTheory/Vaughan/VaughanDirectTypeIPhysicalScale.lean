

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanDirectL1Physical
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeILongVariablePrimitiveMaximal

/-!
 # Direct Vaughan Type-I: the AP-normalized physical scale

The unsquared mean arising from character orthogonality has weight `1 / φ(q)`.
This module keeps that weight through row Cauchy and only then invokes the
existing variable-length primitive maximal large sieve.  It also records why
putting the square-large-sieve weight `q / φ(q)` on the unsquared mean inserts
an extra factor `q` before any analytic estimate is used.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The primitive unsquared mean with the weight produced by AP character
orthogonality.  This is deliberately distinct from the square-large-sieve
weight `q / φ(q)`. -/
def apNormalizedPrimitiveMean (a : ℤ → ℂ) (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q, primitivePrefixAmplitude a N q χ

/-- The corrected direct Type-I mean.  The Vaughan input itself is not frozen:
this is the literal producer quantity. -/
def apNormalizedVaughanTypeIMean (N Q u v : ℕ) : ℝ :=
  apNormalizedPrimitiveMean
    (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N Q

/-- The old unsquared weight is exactly `q` times the AP-normalized summand. -/
theorem directPrimitiveMean_summand_eq_q_mul
    (a : ℤ → ℂ) (N q : ℕ) (_hq : 0 < q) :
    ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q, primitivePrefixAmplitude a N q χ =
      (q : ℝ) * (((q.totient : ℝ)⁻¹) *
        ∑ χ : PrimitiveCharacter q, primitivePrefixAmplitude a N q χ) := by
  rw [div_eq_mul_inv, mul_assoc]

/-- Strict one-level scale counterexample: as soon as the primitive amplitude
mass is positive and `q>1`, replacing `1/φ(q)` by `q/φ(q)` strictly enlarges
that level.  Thus `q/φ(q)` cannot be called the direct AP-normalized L¹ mean;
it is the square-large-sieve weight. -/
theorem directPrimitiveMean_summand_strictly_inflates
    (a : ℤ → ℂ) (N q : ℕ) (hq : 1 < q)
    (hA : 0 < ∑ χ : PrimitiveCharacter q,
      primitivePrefixAmplitude a N q χ) :
    ((q.totient : ℝ)⁻¹) *
        ∑ χ : PrimitiveCharacter q, primitivePrefixAmplitude a N q χ <
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q, primitivePrefixAmplitude a N q χ := by
  rw [directPrimitiveMean_summand_eq_q_mul a N q (by omega)]
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hbase : 0 < ((q.totient : ℝ)⁻¹) *
      ∑ χ : PrimitiveCharacter q, primitivePrefixAmplitude a N q χ :=
    mul_pos (inv_pos.mpr hφ) hA
  simpa only [one_mul] using
    mul_lt_mul_of_pos_right (show (1 : ℝ) < q by exact_mod_cast hq) hbase

/-- Rowwise AP-normalized L¹ majorant.  For Vaughan's first lane, `S` is a
`d`-shell; for the middle lane it is a `(d,e)` shell. -/
def apNormalizedVariableLengthRowMean
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (c : ι → ℤ → ℂ)
    (L : ι → ℕ) (Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q, ∑ r ∈ S,
      Real.sqrt (primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ)

/-- Cauchy with the correct normalization.  The exact number of rows and
moduli is visible; no analytic hypothesis is hidden here. -/
theorem apNormalizedVariableLengthRowMean_sq_le
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (c : ι → ℤ → ℂ)
    (L : ι → ℕ) (Q : ℕ)
    (hcard : ∀ q ∈ Finset.Icc 1 Q,
      Fintype.card (PrimitiveCharacter q) ≤ q.totient) :
    apNormalizedVariableLengthRowMean S c L Q ^ 2 ≤
      ((Finset.Icc 1 Q).card : ℝ) * (S.card : ℝ) *
        (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
          ∑ χ : PrimitiveCharacter q, ∑ r ∈ S,
            primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ) := by
  let B : ℕ → ℝ := fun q => ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q, ∑ r ∈ S,
      Real.sqrt (primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ)
  have houter := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 Q) (f := B)
  have hinner : (∑ i ∈ Finset.Icc 1 Q, B i ^ 2) ≤
      (S.card : ℝ) *
        (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
          ∑ χ : PrimitiveCharacter q, ∑ r ∈ S,
            primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
    have hφ : (0 : ℝ) < q.totient := by
      exact_mod_cast Nat.totient_pos.mpr hq0
    let A : PrimitiveCharacter q → ℝ := fun χ => ∑ r ∈ S,
      Real.sqrt (primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ)
    have hchars := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (PrimitiveCharacter q))) (f := A)
    have hrows (χ : PrimitiveCharacter q) : A χ ^ 2 ≤
        (S.card : ℝ) * ∑ r ∈ S,
          primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ := by
      have hr := sq_sum_le_card_mul_sum_sq (s := S)
        (f := fun r => Real.sqrt
          (primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ))
      refine hr.trans ?_
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro r hr
        rw [Real.sq_sqrt]
        exact primitiveCharacterPrefixMaxSquare_nonneg (c r) 0 (L r) q χ
      · positivity
    dsimp [B]
    calc
      (((q.totient : ℝ)⁻¹) * ∑ χ : PrimitiveCharacter q, A χ) ^ 2
          = ((q.totient : ℝ)⁻¹) ^ 2 * (∑ χ : PrimitiveCharacter q, A χ) ^ 2 := by ring
      _ ≤ ((q.totient : ℝ)⁻¹) ^ 2 *
          ((Fintype.card (PrimitiveCharacter q) : ℝ) * ∑ χ, A χ ^ 2) := by
        gcongr
        exact hchars
      _ ≤ ((q.totient : ℝ)⁻¹) ^ 2 *
          ((q.totient : ℝ) * ∑ χ, A χ ^ 2) := by
        gcongr
        exact_mod_cast hcard q hq
      _ ≤ ((q.totient : ℝ)⁻¹) ^ 2 *
          ((q.totient : ℝ) * ∑ χ, ((S.card : ℝ) *
            ∑ r ∈ S, primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ)) := by
        gcongr with χ
        exact hrows χ
      _ = (S.card : ℝ) * (((q.totient : ℝ)⁻¹) *
          ∑ χ : PrimitiveCharacter q, ∑ r ∈ S,
            primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ) := by
        field_simp
        simp_rw [Finset.mul_sum]
  exact houter.trans (by
    calc
      ((Finset.Icc 1 Q).card : ℝ) * ∑ i ∈ Finset.Icc 1 Q, B i ^ 2 ≤
          ((Finset.Icc 1 Q).card : ℝ) * ((S.card : ℝ) *
            (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
              ∑ χ : PrimitiveCharacter q, ∑ r ∈ S,
                primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ)) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = _ := by ring)

/-- The AP-normalized square ledger is bounded by the existing variable-length
large sieve.  This is the precise point where the proved LS theorem is called. -/
theorem apNormalized_variableLength_square_le_budget
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (c : ι → ℤ → ℂ)
    (L : ι → ℕ) (Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
      ∑ χ : PrimitiveCharacter q, ∑ r ∈ S,
        primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ) ≤
      variableLengthPrimitivePrefixBudget S c L Q := by
  calc
    _ = ∑ r ∈ S, ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_comm]
    _ ≤ ∑ r ∈ S, ∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro q hq
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
      have hφ : (0 : ℝ) < q.totient := by
        exact_mod_cast Nat.totient_pos.mpr (Finset.mem_Icc.mp hq).1
      have hs : 0 ≤ ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ :=
        Finset.sum_nonneg fun χ _ =>
          primitiveCharacterPrefixMaxSquare_nonneg (c r) 0 (L r) q χ
      have hw : (q.totient : ℝ)⁻¹ ≤
          (q : ℝ) / (q.totient : ℝ) := by
        rw [div_eq_mul_inv]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hq1 (inv_nonneg.mpr hφ.le)
      exact mul_le_mul_of_nonneg_right hw hs
    _ ≤ variableLengthPrimitivePrefixBudget S c L Q :=
      weighted_primitive_variableLength_prefix_maximal S c L Q hQ

/-- Combined corrected-weight Cauchy + variable-length LS producer. -/
theorem apNormalizedVariableLengthRowMean_sq_le_budget
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (c : ι → ℤ → ℂ)
    (L : ι → ℕ) (Q : ℕ) (hQ : 0 < Q)
    (hcard : ∀ q ∈ Finset.Icc 1 Q,
      Fintype.card (PrimitiveCharacter q) ≤ q.totient) :
    apNormalizedVariableLengthRowMean S c L Q ^ 2 ≤
      ((Finset.Icc 1 Q).card : ℝ) * (S.card : ℝ) *
        variableLengthPrimitivePrefixBudget S c L Q := by
  refine (apNormalizedVariableLengthRowMean_sq_le S c L Q hcard).trans ?_
  gcongr
  exact apNormalized_variableLength_square_le_budget S c L Q hQ

/-- The middle `μ*Λ` lane retains the literal Λ square energy; it is not
silently replaced by a row count. -/
theorem vaughanTypeIMiddleShortEnergy_explicitLambda
    (DS ES : Finset ℕ) :
    vaughanTypeIMiddleShortEnergy DS ES ≤
      (DS.card : ℝ) * ∑ e ∈ ES,
        ‖(ArithmeticFunction.vonMangoldt e : ℂ)‖ ^ 2 :=
  vaughanTypeIMiddleShortEnergy_le_mangoldt DS ES

/-- Scalar shell optimization.  If a corrected-weight shell has a square bound
`P²`, then it has the physical unsquared bound `P`; choosing
`P = logPay * (N + Q² sqrt N)` is the exact producer shape. -/
theorem corrected_typeI_shell_physical_of_square
    (shellMean logPay N Q : ℝ)
    (hmean : 0 ≤ shellMean) (hlog : 0 ≤ logPay) (hN : 0 ≤ N) (_hQ : 0 ≤ Q)
    (hsq : shellMean ^ 2 ≤
      (logPay * (N + Q ^ 2 * Real.sqrt N)) ^ 2) :
    shellMean ≤ logPay * (N + Q ^ 2 * Real.sqrt N) := by
  have htarget : 0 ≤ logPay * (N + Q ^ 2 * Real.sqrt N) := by positivity
  exact (sq_le_sq₀ hmean htarget).mp hsq

end

end AnalyticNumberTheory.LargeSieve
