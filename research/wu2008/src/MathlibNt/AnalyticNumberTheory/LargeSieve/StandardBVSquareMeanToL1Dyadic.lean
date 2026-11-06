

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanAllCharacterAnalyticLedger
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeILongCoeffMomentExplicit
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIICanonicalShortLength

/-!
 # Standard BV: exact dyadic square-mean to L¹ conversion

This module isolates the finite conversion which is needed *before* any
Bombieri--Vinogradov conclusion may be claimed.  The AP prefix error is supplied
pointwise through the character expansion, not as a final BV premise.  Every
factor `1/φ(q)`, `q/φ(q)`, the number of moduli in a block, and the number of
conductor cells is retained.

The character quantity is a genuine prefix maximum.  Nothing in this file
replaces it by the endpoint `y = N`.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section

/-- The square ledger on a chosen set of levels, with the exact
`q / φ(q)` weight used by the primitive large sieve. -/
def weightedNonprincipalPrefixSquare
    (b : ℤ → ℂ) (N : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ ∈ nonprincipalCharacters q, characterPrefixMaxSquare χ b 0 N

/-- The nonnegative amplitude whose square is the full character prefix
maximum. -/
def nonprincipalPrefixAmplitude
    (b : ℤ → ℂ) (N q : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  Real.sqrt (characterPrefixMaxSquare χ b 0 N)

lemma nonprincipalPrefixAmplitude_nonneg
    (b : ℤ → ℂ) (N q : ℕ) (χ : DirichletCharacter ℂ q) :
    0 ≤ nonprincipalPrefixAmplitude b N q χ := Real.sqrt_nonneg _

lemma nonprincipalPrefixAmplitude_sq
    (b : ℤ → ℂ) (N q : ℕ) (χ : DirichletCharacter ℂ q) :
    nonprincipalPrefixAmplitude b N q χ ^ 2 =
      characterPrefixMaxSquare χ b 0 N := by
  apply Real.sq_sqrt
  unfold characterPrefixMaxSquare
  let V := (Finset.range (N + 1)).image
    (fun y => characterPrefixSquare χ b 0 y)
  have hm : V.max' (Finset.image_nonempty.mpr ⟨0, by simp⟩) ∈ V :=
    Finset.max'_mem V _
  rcases Finset.mem_image.mp hm with ⟨y, hy, heq⟩
  rw [← heq]
  unfold characterPrefixSquare
  positivity

/-- There are at most `φ(q)` nonprincipal characters.  This is kept as a
separate public bookkeeping lemma because it is exactly what turns
`1/φ(q)^2` after Cauchy into `1/φ(q)`. -/
lemma card_nonprincipalCharacters_le_totient {q : ℕ} (hq : 0 < q) :
    (nonprincipalCharacters q).card ≤ q.totient := by
  let : NeZero q := ⟨hq.ne'⟩
  have hchars : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    have horth := charOrthSum hq (1 : ZMod q) 1
    have hc : ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℂ) =
        (q.totient : ℂ) := by simpa using horth
    exact_mod_cast hc
  exact (Finset.card_le_card (Finset.erase_subset _ _)).trans_eq (by
    simpa [nonprincipalCharacters] using hchars)

/-- Character Cauchy at one level.  Starting from the literal AP majorant
`E(q) ≤ φ(q)⁻¹ ∑_{χ≠χ₀} M(q,χ)`, the result is written with the large-sieve
weight `q/φ(q)`: no totient weight is discarded. -/
theorem one_modulus_character_cauchy
    (b : ℤ → ℂ) (N q : ℕ) (E : ℝ) (hq : 0 < q) (hE0 : 0 ≤ E)
    (hchar : E ≤ ((q.totient : ℝ)⁻¹) *
      ∑ χ ∈ nonprincipalCharacters q,
        nonprincipalPrefixAmplitude b N q χ) :
    (q : ℝ) * E ^ 2 ≤
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ nonprincipalCharacters q, characterPrefixMaxSquare χ b 0 N := by
  have hφnat : 0 < q.totient := Nat.totient_pos.mpr hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast hφnat
  let A : ℝ := ∑ χ ∈ nonprincipalCharacters q,
    nonprincipalPrefixAmplitude b N q χ
  have hsqE : E ^ 2 ≤ (((q.totient : ℝ)⁻¹) * A) ^ 2 :=
    pow_le_pow_left₀ hE0 hchar 2
  have hcauchy : A ^ 2 ≤ ((nonprincipalCharacters q).card : ℝ) *
      ∑ χ ∈ nonprincipalCharacters q,
        nonprincipalPrefixAmplitude b N q χ ^ 2 := by
    dsimp [A]
    exact sq_sum_le_card_mul_sum_sq
  have hcard : ((nonprincipalCharacters q).card : ℝ) ≤ q.totient := by
    exact_mod_cast card_nonprincipalCharacters_le_totient hq
  calc
    (q : ℝ) * E ^ 2
        ≤ (q : ℝ) * ((((q.totient : ℝ)⁻¹) * A) ^ 2) := by gcongr
    _ ≤ (q : ℝ) * (((q.totient : ℝ)⁻¹) ^ 2 *
        (((nonprincipalCharacters q).card : ℝ) *
          ∑ χ ∈ nonprincipalCharacters q,
            nonprincipalPrefixAmplitude b N q χ ^ 2)) := by
      rw [mul_pow]
      gcongr
    _ ≤ (q : ℝ) * (((q.totient : ℝ)⁻¹) ^ 2 *
        ((q.totient : ℝ) *
          ∑ χ ∈ nonprincipalCharacters q,
            nonprincipalPrefixAmplitude b N q χ ^ 2)) := by
      gcongr
    _ = ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ nonprincipalCharacters q,
          nonprincipalPrefixAmplitude b N q χ ^ 2 := by
      field_simp
    _ = _ := by simp_rw [nonprincipalPrefixAmplitude_sq]

/-- Exact Cauchy conversion on an arbitrary modulus block.  If every modulus
in `S` is at least `R`, then

`R (∑ E_q)^2 ≤ #S · ∑ (q/φ(q))∑χ M(q,χ)^2`.

Thus the cardinality is not silently replaced by `R`; that optional estimate
is a later, separate step. -/
theorem modulus_block_square_to_L1
    (b : ℤ → ℂ) (N R : ℕ) (S : Finset ℕ) (E : ℕ → ℝ)
    (hR : 0 < R) (hlevels : ∀ q ∈ S, R ≤ q)
    (hE0 : ∀ q ∈ S, 0 ≤ E q)
    (hchar : ∀ q ∈ S, E q ≤ ((q.totient : ℝ)⁻¹) *
      ∑ χ ∈ nonprincipalCharacters q,
        nonprincipalPrefixAmplitude b N q χ) :
    (R : ℝ) * (∑ q ∈ S, E q) ^ 2 ≤
      (S.card : ℝ) * weightedNonprincipalPrefixSquare b N S := by
  have hq (q : ℕ) (hqS : q ∈ S) : 0 < q := hR.trans_le (hlevels q hqS)
  have hone (q : ℕ) (hqS : q ∈ S) :
      (R : ℝ) * E q ^ 2 ≤
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ nonprincipalCharacters q,
            characterPrefixMaxSquare χ b 0 N := by
    have hbase := one_modulus_character_cauchy b N q (E q)
      (hq q hqS) (hE0 q hqS) (hchar q hqS)
    have hRq : (R : ℝ) ≤ q := by exact_mod_cast hlevels q hqS
    calc
      (R : ℝ) * E q ^ 2 ≤ (q : ℝ) * E q ^ 2 := by gcongr
      _ ≤ _ := hbase
  have houter := sq_sum_le_card_mul_sum_sq
    (s := S) (f := E)
  calc
    (R : ℝ) * (∑ q ∈ S, E q) ^ 2
        ≤ (R : ℝ) * ((S.card : ℝ) * ∑ q ∈ S, E q ^ 2) := by gcongr
    _ = (S.card : ℝ) * ((R : ℝ) * ∑ q ∈ S, E q ^ 2) := by ring
    _ = (S.card : ℝ) * ∑ q ∈ S, ((R : ℝ) * E q ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ (S.card : ℝ) * ∑ q ∈ S,
        (((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ nonprincipalCharacters q,
            characterPrefixMaxSquare χ b 0 N) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun q hqS => hone q hqS
      · positivity
    _ = _ := by rfl




/-- Exact equal-allocation square threshold.  `L` is the number of dyadic
modulus blocks, `m` the number of actual moduli in the present block, and `R`
its lower endpoint. -/
def standardBVBlockSquareThreshold
    (N logN A R m L : ℝ) : ℝ :=
  (R / m) * (N / (L * logN ^ A)) ^ 2


/-! ## Substitution ledger for the currently proved producers

These are transparent scale expressions, not hypotheses asserting BV.  Their
factorizations identify exactly which payments must be compared with the
preceding threshold. -/

/-- Current unconditional collected Type-I prefix scale on conductor window
`C ≤ d ≤ 2C`.  It pays the linear conductor transport `(Q/C) H(Q/C)`, RM
`log₂(N)^2`, the full `(N+C² log C)` large-sieve factor, and the proved
`108 B² N log(N)^5` coefficient moment. -/
def existingTypeIPrefixWindowScale (N Q C B : ℕ) : ℝ :=
  ((Q / C : ℕ) : ℝ) * conductorHarmonicFactor (Q / C) *
    (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
    primitiveLargeSieveConstant N (2 * C) *
      (108 * (B : ℝ) ^ 2 * (N : ℝ) * Real.log (N + 1 : ℕ) ^ 5)

/-- Current short-length Type-II *prefix* scale on conductor window `C` and
outer shell `2^k`.  Unlike the obsolete endpoint route, this retains the
prefix maximum and cancels `2^k · (N/2^k)` in the length charge.  The currently
proved tensor moment still contributes `27 B² N log(N)^5`. -/
def existingTypeIIShortPrefixWindowScale (N Q C k B : ℕ) : ℝ :=
  ((Q / C : ℕ) : ℝ) * conductorHarmonicFactor (Q / C) *
    (((Nat.log2 (vaughanCanonicalTensorLength N k) + 1 : ℕ) : ℝ) ^ 2) *
    ((N : ℝ) + ((2 ^ k : ℕ) : ℝ) *
      ((2 * (Nat.ceil
        (Real.log (((2 * C : ℕ) : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
        ((2 * C : ℕ) : ℝ) ^ 2)) *
    (27 * (B : ℝ) ^ 2 * (N : ℝ) * Real.log (N + 1 : ℕ) ^ 5)

/-- Ratio to the exact one-block threshold.  A ratio at most one is sufficient;
a ratio larger than one measures the missing factor without suppressing any
`Q/C`, harmonic, RM, or block-cardinality payment. -/
def squareThresholdDeficitRatio
    (scale N logN A R qCard blockCount : ℝ) : ℝ :=
  qCard * scale /
    (R * (N / (blockCount * logN ^ A)) ^ 2)

/-- The Λ change-level correction ratio, with its proved `Q² polylog²` scale
inserted literally. -/
def lambdaCorrectionThresholdRatio
    (N Q A R qCard blockCount : ℕ) : ℝ :=
  squareThresholdDeficitRatio
    (vaughanLambdaConductorCorrectionScale N Q) N (Real.log (N + 1 : ℕ)) A
      R qCard blockCount

/-- Type-I ratio after literal substitution of the existing producer. -/
def typeIThresholdRatio
    (N Q C B A R qCard blockCount : ℕ) : ℝ :=
  squareThresholdDeficitRatio
    (existingTypeIPrefixWindowScale N Q C B) N (Real.log (N + 1 : ℕ)) A
      R qCard blockCount

/-- Type-II ratio after literal substitution of the genuine short-prefix
producer. -/
def typeIIThresholdRatio
    (N Q C k B A R qCard blockCount : ℕ) : ℝ :=
  squareThresholdDeficitRatio
    (existingTypeIIShortPrefixWindowScale N Q C k B) N
      (Real.log (N + 1 : ℕ)) A R qCard blockCount



end

end AnalyticNumberTheory.LargeSieve
