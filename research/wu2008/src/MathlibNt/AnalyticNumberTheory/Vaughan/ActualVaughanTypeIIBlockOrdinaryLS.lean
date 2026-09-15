

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanDirectAPNormalizedTypeIIActualDecomposition
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIICanonicalShortLength

/-!
 # Ordinary-LS block-L¹ producer for the exact Vaughan Type-II coefficient

This file gives the unconditional ordinary primitive-large-sieve baseline on an
arbitrary finite conductor block.  It first uses the exact production
`vaughanTypeIICoeff vaughanUnitIntegerCoeff u v` hyperbolic decomposition, then
applies conductor/character Cauchy and the prefix-maximal tensor large sieve.
Every active `(k,l)` shell keeps its own short length and Möbius outer energy.

The final split is diagnostic.  The modulus part has the desired
`R² * sqrt N` character, while the diagonal part retains an extra conductor
factor.  The latter is named `...CrossRowExcess`: it is the only term not paid
by ordinary LS and is precisely where cross-row cancellation/dispersion must
enter.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- Block-local `d / φ(d)` first moment.  The Type-II-specific name keeps this
leaf independent of the later Standard-BV consumer stack. -/
def typeIIBlockWeightedPrimitiveMean
    (a : ℤ → ℂ) (N : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ d ∈ S, ((d : ℝ) / (d.totient : ℝ)) *
    ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ

lemma typeIIBlockWeightedPrimitiveMean_nonneg
    (a : ℤ → ℂ) (N : ℕ) (S : Finset ℕ) :
    0 ≤ typeIIBlockWeightedPrimitiveMean a N S := by
  unfold typeIIBlockWeightedPrimitiveMean
  exact Finset.sum_nonneg fun d hd =>
    mul_nonneg (by positivity)
      (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _)

/-- Square ledger on an arbitrary finite conductor block. -/
def blockWeightedPrimitiveSquareLedger
    (F : (q : ℕ) → PrimitiveCharacter q → ℝ) (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter q, F q χ ^ 2

lemma blockWeightedPrimitiveSquareLedger_nonneg
    (F : (q : ℕ) → PrimitiveCharacter q → ℝ) (S : Finset ℕ) :
    0 ≤ blockWeightedPrimitiveSquareLedger F S := by
  unfold blockWeightedPrimitiveSquareLedger
  exact Finset.sum_nonneg fun q hq =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun χ hχ => sq_nonneg _)

private theorem primitiveCharacter_card_le_totient_typeIIBlock
    (q : ℕ) (hq : 0 < q) :
    Fintype.card (PrimitiveCharacter q) ≤ q.totient := by
  exact primitiveCharacter_card_le_totient_basic q hq

/-- The two finite Cauchy steps depend only on the conductor/character
mass, so the same square ledger serves prefix amplitudes and collected shells. -/
private theorem blockWeightedPrimitiveMean_sq_le_cap_sq_mul_squareLedger
    (F : (q : ℕ) → PrimitiveCharacter q → ℝ) (Q : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 Q) :
    (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q, F q χ) ^ 2 ≤
      (Q : ℝ) ^ 2 * blockWeightedPrimitiveSquareLedger F S := by
  let X : ℕ → ℝ := fun q =>
    ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q, F q χ
  have houter : (∑ q ∈ S, X q) ^ 2 ≤
      (S.card : ℝ) * ∑ q ∈ S, X q ^ 2 := by
    simpa [mul_comm] using Finset.sum_mul_sq_le_sq_mul_sq
      S X (fun _ => (1 : ℝ))
  have hcardS : (S.card : ℝ) ≤ Q := by
    exact_mod_cast (Finset.card_le_card hS).trans (by simp)
  have hpoint : ∀ q ∈ S, X q ^ 2 ≤
      (Q : ℝ) * (((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          F q χ ^ 2) := by
    intro q hqmem
    have hqfull := hS hqmem
    have hq : 0 < q := (Finset.mem_Icc.mp hqfull).1
    have hqQ : q ≤ Q := (Finset.mem_Icc.mp hqfull).2
    have hφnat : 0 < q.totient := Nat.totient_pos.mpr hq
    have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast hφnat
    have hcs : (∑ χ : PrimitiveCharacter q,
        F q χ) ^ 2 ≤
        (Fintype.card (PrimitiveCharacter q) : ℝ) *
          ∑ χ : PrimitiveCharacter q,
            F q χ ^ 2 := by
      simpa [mul_comm] using Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ : Finset (PrimitiveCharacter q))
        (fun χ => F q χ) (fun _ => (1 : ℝ))
    have hcard : (Fintype.card (PrimitiveCharacter q) : ℝ) ≤ q.totient := by
      exact_mod_cast primitiveCharacter_card_le_totient_typeIIBlock q hq
    have hsum : 0 ≤ ∑ χ : PrimitiveCharacter q,
        F q χ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hcs' : (∑ χ : PrimitiveCharacter q,
        F q χ) ^ 2 ≤
        (q.totient : ℝ) * ∑ χ : PrimitiveCharacter q,
          F q χ ^ 2 :=
      hcs.trans (mul_le_mul_of_nonneg_right hcard hsum)
    dsimp [X]
    rw [mul_pow]
    calc
      ((q : ℝ) / (q.totient : ℝ)) ^ 2 *
          (∑ χ : PrimitiveCharacter q, F q χ) ^ 2 ≤
        ((q : ℝ) / (q.totient : ℝ)) ^ 2 *
          ((q.totient : ℝ) * ∑ χ : PrimitiveCharacter q,
            F q χ ^ 2) :=
        mul_le_mul_of_nonneg_left hcs' (sq_nonneg _)
      _ = (q : ℝ) * (((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            F q χ ^ 2) := by field_simp
      _ ≤ (Q : ℝ) * (((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            F q χ ^ 2) := by gcongr
  change (∑ q ∈ S, X q) ^ 2 ≤ _
  calc
    (∑ q ∈ S, X q) ^ 2 ≤ (S.card : ℝ) * ∑ q ∈ S, X q ^ 2 := houter
    _ ≤ (Q : ℝ) * ∑ q ∈ S, X q ^ 2 := by gcongr
    _ ≤ (Q : ℝ) * ∑ q ∈ S,
        (Q : ℝ) * (((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            F q χ ^ 2) := by
      gcongr with q hq
      exact hpoint q hq
    _ = (Q : ℝ) ^ 2 * blockWeightedPrimitiveSquareLedger
        (fun q χ => F q χ) S := by
      unfold blockWeightedPrimitiveSquareLedger
      calc
        _ = ∑ q ∈ S, (Q : ℝ) ^ 2 *
            (((q : ℝ) / (q.totient : ℝ)) *
              ∑ χ : PrimitiveCharacter q,
                F q χ ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring
        _ = _ := by rw [Finset.mul_sum]

private theorem blockWeightedPrimitiveMean_le_cap_mul_sqrt_squareLedger
    (F : (q : ℕ) → PrimitiveCharacter q → ℝ) (Q : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 Q) :
    (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q, F q χ) ≤
      (Q : ℝ) * Real.sqrt (blockWeightedPrimitiveSquareLedger F S) := by
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, Real.sq_sqrt (blockWeightedPrimitiveSquareLedger_nonneg F S)]
  exact blockWeightedPrimitiveMean_sq_le_cap_sq_mul_squareLedger F Q S hS

/-- Honest block Cauchy.  The `Q²` is conductor/character mass; there is no
conductor-local diagonal saving in this statement. -/
theorem typeIIBlockWeightedPrimitiveMean_sq_le_cap_sq_mul_squareLedger
    (a : ℤ → ℂ) (N Q : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 Q) :
    typeIIBlockWeightedPrimitiveMean a N S ^ 2 ≤
      (Q : ℝ) ^ 2 * blockWeightedPrimitiveSquareLedger
        (fun q χ => primitivePrefixAmplitude a N q χ) S := by
  exact blockWeightedPrimitiveMean_sq_le_cap_sq_mul_squareLedger
    (fun q χ => primitivePrefixAmplitude a N q χ) Q S hS

/-- Unsquared form of block Cauchy. -/
theorem typeIIBlockWeightedPrimitiveMean_le_cap_mul_sqrt_squareLedger
    (a : ℤ → ℂ) (N Q : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 Q) :
    typeIIBlockWeightedPrimitiveMean a N S ≤
      (Q : ℝ) * Real.sqrt (blockWeightedPrimitiveSquareLedger
        (fun q χ => primitivePrefixAmplitude a N q χ) S) := by
  exact blockWeightedPrimitiveMean_le_cap_mul_sqrt_squareLedger
    (fun q χ => primitivePrefixAmplitude a N q χ) Q S hS

/-- Exact production collected-shell weighted first moment on a finite conductor
block. -/
def blockWeightedVaughanActualCollectedShellMean
    (N u v k l : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter q,
      Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ)

/-- The exact Type-II production coefficient decomposes into the actual active
hyperbolic shells before any analytic estimate is made. -/
theorem blockWeightedExactVaughanTypeII_le_active_collected_shells
    (N u v : ℕ) (S : Finset ℕ) :
    typeIIBlockWeightedPrimitiveMean
        (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N S ≤
      ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
        blockWeightedVaughanActualCollectedShellMean
          N u v kl.1 kl.2 S := by
  unfold typeIIBlockWeightedPrimitiveMean blockWeightedVaughanActualCollectedShellMean
  calc
    _ ≤ ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
            Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare
              N u v kl.1 kl.2 q χ) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun χ _ =>
          primitivePrefixAmplitude_vaughanTypeII_le_active_collected_shells
            N u v q χ
      · positivity
    _ = _ := by
      calc
        _ = ∑ q ∈ S,
            ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
              ((q : ℝ) / (q.totient : ℝ)) *
                ∑ χ : PrimitiveCharacter q,
                  Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare
                    N u v kl.1 kl.2 q χ) := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [Finset.sum_comm, Finset.mul_sum]
        _ = _ := by rw [Finset.sum_comm]

/-- Per-shell ordinary-LS square payment.  Both the physical short length and
actual Möbius outer energy remain visible. -/
def vaughanTypeIIOrdinaryShellSquareBound
    (N u v k l R : ℕ) : ℝ :=
  (((Nat.log2 (vaughanCanonicalTensorLength N k) + 1 : ℕ) : ℝ) ^ 2) *
    vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
      (vaughanCanonicalDyadicBlock N u k) *
    primitiveLargeSieveConstant (vaughanCanonicalTensorLength N k) (2 * R) *
    vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff (fun _ => 1)
      N N u v k l

lemma vaughanTypeIIOrdinaryShellSquareBound_nonneg
    (N u v k l R : ℕ) :
    0 ≤ vaughanTypeIIOrdinaryShellSquareBound N u v k l R := by
  unfold vaughanTypeIIOrdinaryShellSquareBound primitiveLargeSieveConstant
    vaughanBilinearCoeffEnergy vaughanCanonicalShortTensorEnergy
  positivity

/-- Restriction of the prefix-maximal tensor LS to any finite conductor block
inside `(R,2R]`. -/
theorem blockWeightedVaughanActualCollectedShell_squareLedger_le
    (N u v k l R : ℕ) (hR : 0 < R) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc R (2 * R)) :
    (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ) ≤
      vaughanTypeIIOrdinaryShellSquareBound N u v k l R := by
  let A := vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
    (vaughanCanonicalDyadicBlock N u k)
  let F : (q : ℕ) → PrimitiveCharacter q → ℝ := fun q χ =>
    A * vaughanCanonicalTensorPrefixMaxEnergy
      (fun _ => 1) N N u v k l q χ
  have hsub : S ⊆ Finset.Icc 1 (2 * R) := by
    intro q hq
    have h := Finset.mem_Ioc.mp (hS hq)
    exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
  calc
    _ ≤ ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q, F q χ := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro χ hχ
        exact vaughanCanonicalCollectedPrefixMaxSquare_le_rowPrefixMax
          N u v k l q χ
      · positivity
    _ ≤ ∑ q ∈ Finset.Icc 1 (2 * R), ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q, F q χ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro q hq hnot
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun χ hχ => by
        dsimp [F, A]
        apply mul_nonneg
        · unfold vaughanBilinearCoeffEnergy
          positivity
        · unfold vaughanCanonicalTensorPrefixMaxEnergy
          exact Finset.sum_nonneg fun d hd =>
            primitiveCharacterPrefixMaxSquare_nonneg _ _ _ _ _)
    _ ≤ vaughanTypeIIOrdinaryShellSquareBound N u v k l R := by
      have h := weighted_primitive_vaughanCanonicalTensorPrefix
        (fun _ => 1) N N u v k l (2 * R) (Nat.mul_pos (by decide) hR)
      dsimp [F, A]
      exact h.trans_eq (by
        unfold vaughanTypeIIOrdinaryShellSquareBound
        ring)

/-- Per-shell first-moment consequence of conductor Cauchy plus prefix-maximal
tensor LS. -/
theorem blockWeightedVaughanActualCollectedShellMean_le_ordinaryLS
    (N u v k l R : ℕ) (hR : 0 < R) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc R (2 * R)) :
    blockWeightedVaughanActualCollectedShellMean N u v k l S ≤
      (2 * R : ℕ) * Real.sqrt
        (vaughanTypeIIOrdinaryShellSquareBound N u v k l R) := by
  have hcap : S ⊆ Finset.Icc 1 (2 * R) := by
    intro q hq
    have h := Finset.mem_Ioc.mp (hS hq)
    exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
  have hsquare := blockWeightedVaughanActualCollectedShell_squareLedger_le
    N u v k l R hR S hS
  have hmean := blockWeightedPrimitiveMean_le_cap_mul_sqrt_squareLedger
    (fun q χ => Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ))
    (2 * R) S hcap
  -- The common Cauchy ledger retains the actual collected square at each (q, χ).
  simp only [blockWeightedPrimitiveSquareLedger,
    Real.sq_sqrt (vaughanCanonicalCollectedPrefixMaxSquare_nonneg N u v k l _ _)] at hmean
  exact hmean.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsquare)
    (Nat.cast_nonneg (2 * R)))

/-- Fully explicit ordinary-LS block bound, shell by shell. -/
def vaughanTypeIIBlockOrdinaryLSBound (N u v R : ℕ) : ℝ :=
  ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
    ((2 * R : ℕ) : ℝ) * Real.sqrt
      (vaughanTypeIIOrdinaryShellSquareBound N u v kl.1 kl.2 R)

/-- **Exact production Type-II block-L¹ ordinary-LS producer.** -/
theorem exactVaughanTypeII_blockWeighted_mean_le_ordinaryLS
    (N u v R : ℕ) (hR : 0 < R) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc R (2 * R)) :
    typeIIBlockWeightedPrimitiveMean
        (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N S ≤
      vaughanTypeIIBlockOrdinaryLSBound N u v R := by
  refine (blockWeightedExactVaughanTypeII_le_active_collected_shells N u v S).trans ?_
  unfold vaughanTypeIIBlockOrdinaryLSBound
  exact Finset.sum_le_sum fun kl hkl =>
    blockWeightedVaughanActualCollectedShellMean_le_ordinaryLS
      N u v kl.1 kl.2 R hR S hS

/-- Diagonal part of the ordinary-LS payment.  This is the unique term carrying
an unwanted extra factor `R`; dispersion/cross-row cancellation must replace it
by the target `N` scale. -/
def vaughanTypeIIBlockCrossRowExcess (N u v R : ℕ) : ℝ :=
  ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
    ((2 * R : ℕ) : ℝ) * Real.sqrt
      (((((Nat.log2 (vaughanCanonicalTensorLength N kl.1) + 1 : ℕ) : ℝ) ^ 2) *
        vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
          (vaughanCanonicalDyadicBlock N u kl.1) *
        (vaughanCanonicalTensorLength N kl.1 : ℝ) *
        vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff (fun _ => 1)
          N N u v kl.1 kl.2))

/-- Modulus/off-diagonal part.  Its displayed conductor scale is
`(2R) * sqrt((2R)^2 * ...)`, i.e. the payable `R² * sqrt N` side. -/
def vaughanTypeIIBlockPayableModulusPart (N u v R : ℕ) : ℝ :=
  ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
    ((2 * R : ℕ) : ℝ) * Real.sqrt
      (((((Nat.log2 (vaughanCanonicalTensorLength N kl.1) + 1 : ℕ) : ℝ) ^ 2) *
        vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
          (vaughanCanonicalDyadicBlock N u kl.1) *
        (primitiveBilinearQFactor (2 * R) * (((2 * R : ℕ) : ℝ) ^ 2)) *
        vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff (fun _ => 1)
          N N u v kl.1 kl.2))

/-- Ordinary LS splits into a payable modulus term and exactly one residual
cross-row/dispersion term. -/
theorem vaughanTypeIIBlockOrdinaryLSBound_le_crossRowExcess_add_payable
    (N u v R : ℕ) :
    vaughanTypeIIBlockOrdinaryLSBound N u v R ≤
      vaughanTypeIIBlockCrossRowExcess N u v R +
        vaughanTypeIIBlockPayableModulusPart N u v R := by
  unfold vaughanTypeIIBlockOrdinaryLSBound vaughanTypeIIBlockCrossRowExcess
    vaughanTypeIIBlockPayableModulusPart vaughanTypeIIOrdinaryShellSquareBound
    primitiveLargeSieveConstant
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro kl hkl
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left
  · let X : ℝ :=
      (((Nat.log2 (vaughanCanonicalTensorLength N kl.1) + 1 : ℕ) : ℝ) ^ 2) *
        vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
          (vaughanCanonicalDyadicBlock N u kl.1)
    let E : ℝ := vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff
      (fun _ => 1) N N u v kl.1 kl.2
    have hX : 0 ≤ X := by dsimp [X, vaughanBilinearCoeffEnergy]; positivity
    have hE : 0 ≤ E := by dsimp [E, vaughanCanonicalShortTensorEnergy]; positivity
    have hL : 0 ≤ (vaughanCanonicalTensorLength N kl.1 : ℝ) := by positivity
    have hM : 0 ≤ primitiveBilinearQFactor (2 * R) * (((2 * R : ℕ) : ℝ) ^ 2) :=
      mul_nonneg (primitiveBilinearQFactor_nonneg _) (sq_nonneg _)
    change Real.sqrt (X * ((vaughanCanonicalTensorLength N kl.1 : ℝ) +
        primitiveBilinearQFactor (2 * R) * (((2 * R : ℕ) : ℝ) ^ 2)) * E) ≤
      Real.sqrt (X * (vaughanCanonicalTensorLength N kl.1 : ℝ) * E) +
        Real.sqrt (X * (primitiveBilinearQFactor (2 * R) *
          (((2 * R : ℕ) : ℝ) ^ 2)) * E)
    rw [show X * ((vaughanCanonicalTensorLength N kl.1 : ℝ) +
        primitiveBilinearQFactor (2 * R) * (((2 * R : ℕ) : ℝ) ^ 2)) * E =
      X * (vaughanCanonicalTensorLength N kl.1 : ℝ) * E +
        X * (primitiveBilinearQFactor (2 * R) *
          (((2 * R : ℕ) : ℝ) ^ 2)) * E by ring]
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · rw [add_pow_two, Real.sq_sqrt (mul_nonneg (mul_nonneg hX hL) hE),
        Real.sq_sqrt (mul_nonneg (mul_nonneg hX hM) hE)]
      nlinarith [mul_nonneg
        (Real.sqrt_nonneg (X * (vaughanCanonicalTensorLength N kl.1 : ℝ) * E))
        (Real.sqrt_nonneg (X * (primitiveBilinearQFactor (2 * R) *
          (((2 * R : ℕ) : ℝ) ^ 2)) * E))]
  · positivity

/-- Target comparison in its sharp logical form: once dispersion pays the sole
cross-row residual by `N`, the already-separated modulus term gives the desired
`N + R²√N` shape (up to the explicit shell/log/energy factor `K`). -/
theorem exactVaughanTypeII_blockWeighted_mean_le_target_of_dispersion
    (N u v R : ℕ) (hR : 0 < R) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc R (2 * R)) (K : ℝ)
    (hdisp : vaughanTypeIIBlockCrossRowExcess N u v R ≤ K * N)
    (hmod : vaughanTypeIIBlockPayableModulusPart N u v R ≤
      K * (R : ℝ) ^ 2 * Real.sqrt N) :
    typeIIBlockWeightedPrimitiveMean
        (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N S ≤
      K * ((N : ℝ) + (R : ℝ) ^ 2 * Real.sqrt N) := by
  calc
    _ ≤ vaughanTypeIIBlockOrdinaryLSBound N u v R :=
      exactVaughanTypeII_blockWeighted_mean_le_ordinaryLS N u v R hR S hS
    _ ≤ vaughanTypeIIBlockCrossRowExcess N u v R +
        vaughanTypeIIBlockPayableModulusPart N u v R :=
      vaughanTypeIIBlockOrdinaryLSBound_le_crossRowExcess_add_payable N u v R
    _ ≤ K * N + K * (R : ℝ) ^ 2 * Real.sqrt N := add_le_add hdisp hmod
    _ = K * ((N : ℝ) + (R : ℝ) ^ 2 * Real.sqrt N) := by ring

end
end AnalyticNumberTheory.LargeSieve
