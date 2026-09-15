import MathlibNt.AnalyticNumberTheory.LargeSieve.PrefixMaximal
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# High-conductor dyadic primitive means

This file keeps the AP weight `1 / φ(d)` until the unsquared primitive mean has
been converted, by two honest Cauchy--Schwarz steps, to the square-large-sieve
weight `d / φ(d)`.  In particular the restriction `R < d ≤ Q` is never erased.

The resulting ledger is deliberately exact: the lower conductor cutoff enters
through the harmonic tail `∑_{R<d≤Q} 1/d`, not through a fictitious `1/R`.
Consequently an `N/√R` (or `Q√N`) conclusion is produced only from the stated
square-ledger strengthening.  This module is only a connector and narrow saving
consumer: it does not construct, inhabit, or certify any high-source input.
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

noncomputable section

/-- Literal AP-normalized primitive `L¹` mean on the retained conductor block
`R < d ≤ Q`.  The amplitudes are nonnegative row maxima in applications. -/
def highConductorPrimitiveMean
    (R Q : ℕ) (A : (d : ℕ) → PrimitiveCharacter d → ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioc R Q,
    (1 / (d.totient : ℝ)) * ∑ χ : PrimitiveCharacter d, A d χ

/-- Literal primitive square-large-sieve ledger on the same conductor block. -/
def highConductorPrimitiveSquareLedger
    (R Q : ℕ) (A : (d : ℕ) → PrimitiveCharacter d → ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioc R Q,
    ((d : ℝ) / (d.totient : ℝ)) * ∑ χ : PrimitiveCharacter d, (A d χ) ^ 2

/-- The exact modulus-Cauchy factor left by the high-conductor restriction. -/
def highConductorHarmonicTail (R Q : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc R Q, (1 : ℝ) / d

private theorem primitiveCharacter_card_le_totient (d : ℕ) (hd : 0 < d) :
    Fintype.card (PrimitiveCharacter d) ≤ d.totient := by
  exact primitiveCharacter_card_le_totient_basic d hd

/-- At one positive conductor, character Cauchy converts the square of the
AP-normalized `L¹` row to the primitive large-sieve weight. -/
theorem primitiveMeanAt_sq_le_squareLedgerAt
    {d : ℕ} (hd : 0 < d)
    (A : PrimitiveCharacter d → ℝ) :
    ((Real.sqrt d / (d.totient : ℝ)) * ∑ χ, A χ) ^ 2 ≤
      ((d : ℝ) / (d.totient : ℝ)) * ∑ χ, (A χ) ^ 2 := by
  have hφnat : 0 < d.totient := Nat.totient_pos.mpr hd
  have hφ : 0 < (d.totient : ℝ) := by exact_mod_cast hφnat
  have hdR : 0 ≤ (d : ℝ) := by positivity
  have hcs : (∑ χ : PrimitiveCharacter d, A χ) ^ 2 ≤
      (Fintype.card (PrimitiveCharacter d) : ℝ) * ∑ χ, (A χ) ^ 2 := by
    simpa [mul_comm] using Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (PrimitiveCharacter d)) A (fun _ => (1 : ℝ))
  have hcard : (Fintype.card (PrimitiveCharacter d) : ℝ) ≤ d.totient := by
    exact_mod_cast primitiveCharacter_card_le_totient d hd
  have hsum : 0 ≤ ∑ χ : PrimitiveCharacter d, (A χ) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs' : (∑ χ : PrimitiveCharacter d, A χ) ^ 2 ≤
      (d.totient : ℝ) * ∑ χ, (A χ) ^ 2 :=
    hcs.trans (mul_le_mul_of_nonneg_right hcard hsum)
  rw [mul_pow, div_pow, Real.sq_sqrt hdR]
  calc
    (d : ℝ) / (d.totient : ℝ) ^ 2 * (∑ χ, A χ) ^ 2 ≤
        (d : ℝ) / (d.totient : ℝ) ^ 2 *
          ((d.totient : ℝ) * ∑ χ, (A χ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hcs' (by positivity)
    _ = ((d : ℝ) / (d.totient : ℝ)) * ∑ χ, (A χ) ^ 2 := by
      field_simp

/-- **Exact high-conductor primitive Cauchy ledger.**  This is the finite
connector used by both Type-I and Type-II rows.  It preserves `R < d ≤ Q`, the
unsquared `1/φ(d)` weight, and the `d/φ(d)` square ledger. -/
theorem highConductorPrimitiveMean_sq_le_harmonic_mul_squareLedger
    (R Q : ℕ) (A : (d : ℕ) → PrimitiveCharacter d → ℝ) :
    (highConductorPrimitiveMean R Q A) ^ 2 ≤
      highConductorHarmonicTail R Q *
        highConductorPrimitiveSquareLedger R Q A := by
  let s := Finset.Ioc R Q
  let f : ℕ → ℝ := fun d => 1 / Real.sqrt d
  let g : ℕ → ℝ := fun d =>
    Real.sqrt d / (d.totient : ℝ) * ∑ χ : PrimitiveCharacter d, A d χ
  have hrewrite : highConductorPrimitiveMean R Q A =
      ∑ d ∈ s, f d * g d := by
    unfold highConductorPrimitiveMean
    apply Finset.sum_congr rfl
    intro d hdmem
    have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le R) (Finset.mem_Ioc.mp hdmem).1
    have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    dsimp [f, g, s]
    field_simp
  rw [hrewrite]
  calc
    (∑ d ∈ s, f d * g d) ^ 2 ≤
        (∑ d ∈ s, (f d) ^ 2) * ∑ d ∈ s, (g d) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s f g
    _ ≤ (∑ d ∈ s, (1 : ℝ) / d) *
        ∑ d ∈ s, ((d : ℝ) / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d, (A d χ) ^ 2 := by
      have hf : (∑ d ∈ s, (f d) ^ 2) = ∑ d ∈ s, (1 : ℝ) / d := by
        apply Finset.sum_congr rfl
        intro d _
        simp only [f, div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
      rw [hf]
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro d hdmem
        exact primitiveMeanAt_sq_le_squareLedgerAt
          (lt_of_le_of_lt (Nat.zero_le R) (Finset.mem_Ioc.mp hdmem).1) (A d)
      · exact Finset.sum_nonneg fun d hd => by positivity
    _ = highConductorHarmonicTail R Q *
        highConductorPrimitiveSquareLedger R Q A := rfl

/-- If the high block is nonempty, its genuine Cauchy factor contains the top
term `1/Q`.  This records that the lower cutoff does not turn the harmonic
factor into `1/R`. -/
theorem one_div_top_le_highConductorHarmonicTail
    {R Q : ℕ} (hRQ : R < Q) :
    (1 : ℝ) / Q ≤ highConductorHarmonicTail R Q := by
  unfold highConductorHarmonicTail
  apply Finset.single_le_sum (s := Finset.Ioc R Q)
    (f := fun d : ℕ => (1 : ℝ) / d)
  · intro d hd
    positivity
  · exact Finset.mem_Ioc.mpr ⟨hRQ, le_rfl⟩

/-- Schematic square majorant delivered by both physical row arguments after
inserting the true coefficient energy: the large-sieve length term times the
row/tensor energy is the diagonal `N²`; the modulus term is kept separately. -/
def highConductorPhysicalSquareMajorant
    (H C N Q D : ℝ) : ℝ :=
  H * (N ^ 2 + C * Q ^ 2 * N * D)

/-- The genuine coefficient-energy diagonal survives every nonnegative physical
square majorant.  Restricting conductors after this row estimate cannot remove
it. -/
theorem diagonal_le_highConductorPhysicalSquareMajorant
    {H C N Q D : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hN : 0 ≤ N) (hD : 0 ≤ D) :
    H * N ^ 2 ≤ highConductorPhysicalSquareMajorant H C N Q D := by
  unfold highConductorPhysicalSquareMajorant
  apply mul_le_mul_of_nonneg_left _ hH
  exact le_add_of_nonneg_right
    (mul_nonneg (mul_nonneg (mul_nonneg hC (sq_nonneg Q)) hN) hD)

/-- Formal non-payment certificate: whenever a desired squared budget lies
strictly below the surviving `H N²` diagonal, the available physical majorant
cannot imply that budget, regardless of the modulus-dependent row. -/
theorem highConductorPhysicalSquareMajorant_not_le_of_target_lt_diagonal
    {H C N Q D target : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hN : 0 ≤ N) (hD : 0 ≤ D) (htarget : target < H * N ^ 2) :
    ¬ highConductorPhysicalSquareMajorant H C N Q D ≤ target := by
  exact not_le_of_gt (htarget.trans_le
    (diagonal_le_highConductorPhysicalSquareMajorant hH hC hN hD))

/-- The narrow square-ledger strengthening that really yields an `N/√R`
Type-I scale.  It is intentionally a statement about coefficient energy after
large sieve, not a renamed bound on the unsquared high mean. -/
def HighConductorTypeISquareSaving
    (R Q N : ℕ) (K : ℝ)
    (A : (d : ℕ) → PrimitiveCharacter d → ℝ) : Prop :=
  highConductorHarmonicTail R Q *
      highConductorPrimitiveSquareLedger R Q A ≤
    (K * N / Real.sqrt R) ^ 2

/-- The parallel strengthening giving a `Q√N` Type-II scale. -/
def HighConductorTypeIISquareSaving
    (R Q N : ℕ) (K : ℝ)
    (A : (d : ℕ) → PrimitiveCharacter d → ℝ) : Prop :=
  highConductorHarmonicTail R Q *
      highConductorPrimitiveSquareLedger R Q A ≤
    (K * Q * Real.sqrt N) ^ 2

private theorem highConductorPrimitiveMean_nonneg
    (R Q : ℕ) (A : (d : ℕ) → PrimitiveCharacter d → ℝ)
    (hA : ∀ d χ, 0 ≤ A d χ) :
    0 ≤ highConductorPrimitiveMean R Q A := by
  unfold highConductorPrimitiveMean
  exact Finset.sum_nonneg fun d hd => mul_nonneg (by positivity)
    (Finset.sum_nonneg fun χ hχ => hA d χ)

/-- Actual Type-I row maxima reach the `N/√R` scale once their retained
high-conductor square ledger has the preceding saving. -/
theorem highConductorTypeI_le
    {R Q N : ℕ} {K : ℝ}
    (A : (d : ℕ) → PrimitiveCharacter d → ℝ)
    (hA : ∀ d χ, 0 ≤ A d χ) (hK : 0 ≤ K)
    (h : HighConductorTypeISquareSaving R Q N K A) :
    highConductorPrimitiveMean R Q A ≤ K * N / Real.sqrt R := by
  have hs := (highConductorPrimitiveMean_sq_le_harmonic_mul_squareLedger R Q A).trans h
  have hm := highConductorPrimitiveMean_nonneg R Q A hA
  have ht : 0 ≤ K * N / Real.sqrt R := by positivity
  exact (sq_le_sq₀ hm ht).1 hs

/-- Actual Type-II row maxima reach the `Q√N` scale once their retained
high-conductor square ledger has the parallel saving. -/
theorem highConductorTypeII_le
    {R Q N : ℕ} {K : ℝ}
    (A : (d : ℕ) → PrimitiveCharacter d → ℝ)
    (hA : ∀ d χ, 0 ≤ A d χ) (hK : 0 ≤ K)
    (h : HighConductorTypeIISquareSaving R Q N K A) :
    highConductorPrimitiveMean R Q A ≤ K * Q * Real.sqrt N := by
  have hs := (highConductorPrimitiveMean_sq_le_harmonic_mul_squareLedger R Q A).trans h
  have hm := highConductorPrimitiveMean_nonneg R Q A hA
  have ht : 0 ≤ K * Q * Real.sqrt N := by positivity
  exact (sq_le_sq₀ hm ht).1 hs

/-- A narrow conditional consumer combining two nonnegative rows.  It assumes
the two retained square-ledger savings explicitly; in particular it does not
construct or inhabit a high-source input. -/
theorem highConductorHybrid_of_typeI_typeII_squareLedgers
    {R Q N : ℕ} {KI KII : ℝ}
    (typeIRow typeIIRow : (d : ℕ) → PrimitiveCharacter d → ℝ)
    (hI0 : ∀ d χ, 0 ≤ typeIRow d χ)
    (hII0 : ∀ d χ, 0 ≤ typeIIRow d χ)
    (hKI : 0 ≤ KI) (hKII : 0 ≤ KII)
    (hI : HighConductorTypeISquareSaving R Q N KI typeIRow)
    (hII : HighConductorTypeIISquareSaving R Q N KII typeIIRow) :
    highConductorPrimitiveMean R Q (fun d χ => typeIRow d χ + typeIIRow d χ) ≤
      KI * N / Real.sqrt R + KII * Q * Real.sqrt N := by
  have hsplit :
      highConductorPrimitiveMean R Q (fun d χ => typeIRow d χ + typeIIRow d χ) =
        highConductorPrimitiveMean R Q typeIRow +
          highConductorPrimitiveMean R Q typeIIRow := by
    unfold highConductorPrimitiveMean
    simp_rw [Finset.sum_add_distrib, mul_add]
    rw [Finset.sum_add_distrib]
  rw [hsplit]
  exact add_le_add
    (highConductorTypeI_le typeIRow hI0 hKI hI)
    (highConductorTypeII_le typeIIRow hII0 hKII hII)

end

end AnalyticNumberTheory.LargeSieve
