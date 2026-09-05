import MathlibNt.AnalyticNumberTheory.Vaughan.HighConductorVaughanTypeIRow

/-!
# The narrow conductor-local primitive large-sieve input

The full-cutoff primitive large sieve bounds a retained conductor block by the
same `L + Q²` constant as the full block.  That statement cannot create the
`R⁻¹` diagonal needed after deleting conductors `d ≤ R`.  This file therefore
freezes the missing analytic input at the square-ledger level, before any
unsquared high mean is formed.
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

noncomputable section

/-- Coefficient energy of one primitive prefix row. -/
def conductorLocalRowEnergy (b : ℤ → ℂ) (M : ℤ) (L : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (M + 1) (M + L), ‖b n‖ ^ 2

/-- The precise missing analytic strengthening of the primitive prefix-maximal
large sieve.  It is a square-ledger statement for an arbitrary coefficient
row.  In particular it neither mentions nor assumes a Vaughan high mean.

The `L/R` diagonal is the only new information relative to the existing
full-cutoff theorem; the `Q²` lane is unchanged. -/
def ConductorLocalPrimitiveLargeSieve (K : ℝ) : Prop :=
  ∀ (R Q L : ℕ) (b : ℤ → ℂ) (M : ℤ), 0 < R → 0 < Q →
    highConductorHarmonicTail R Q *
        highConductorPrimitiveSquareLedger R Q
          (fun d χ => Real.sqrt
            (primitiveCharacterPrefixMaxSquare b M L d χ)) ≤
      K ^ 2 * (((Nat.log2 L + 1 : ℕ) : ℝ) ^ 2) *
        (((L : ℝ) * conductorLocalRowEnergy b M L) / R +
          (Q : ℝ) ^ 2 * conductorLocalRowEnergy b M L)

private lemma localRowAmplitude_nonneg
    (b : ℤ → ℂ) (M : ℤ) (L d : ℕ) (χ : PrimitiveCharacter d) :
    0 ≤ Real.sqrt (primitiveCharacterPrefixMaxSquare b M L d χ) :=
  Real.sqrt_nonneg _

/-- Square-ledger extraction.  Once the actual row geometry supplies
`L * energy ≤ N²` and `energy ≤ N`, the local primitive large sieve gives the
required `N/√R + Q√N` scale. -/
theorem highConductorPrimitiveRowMean_le_of_conductorLocal
    {K : ℝ} (hK : 0 ≤ K) (hLS : ConductorLocalPrimitiveLargeSieve K)
    (R Q L N : ℕ) (b : ℤ → ℂ) (M : ℤ)
    (hR : 0 < R) (hQ : 0 < Q)
    (hdiag : (L : ℝ) * conductorLocalRowEnergy b M L ≤ (N : ℝ) ^ 2)
    (henergy : conductorLocalRowEnergy b M L ≤ (N : ℝ)) :
    highConductorPrimitiveMean R Q
        (fun d χ => Real.sqrt
          (primitiveCharacterPrefixMaxSquare b M L d χ)) ≤
      K * ((Nat.log2 L + 1 : ℕ) : ℝ) *
        ((N : ℝ) / Real.sqrt R + (Q : ℝ) * Real.sqrt N) := by
  let E := conductorLocalRowEnergy b M L
  let J : ℝ := ((Nat.log2 L + 1 : ℕ) : ℝ)
  let X : ℝ := (N : ℝ) / Real.sqrt R
  let Y : ℝ := (Q : ℝ) * Real.sqrt N
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hsR : 0 < Real.sqrt (R : ℝ) := Real.sqrt_pos.2 hRR
  have hNN : (0 : ℝ) ≤ N := by positivity
  have hE0 : 0 ≤ E := by
    dsimp [E, conductorLocalRowEnergy]
    positivity
  have hJ0 : 0 ≤ J := by dsimp [J]; positivity
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hY0 : 0 ≤ Y := by dsimp [Y]; positivity
  have hmean0 : 0 ≤ highConductorPrimitiveMean R Q
      (fun d χ => Real.sqrt
        (primitiveCharacterPrefixMaxSquare b M L d χ)) := by
    unfold highConductorPrimitiveMean
    positivity
  have hsquare := highConductorPrimitiveMean_sq_le_harmonic_mul_squareLedger
    R Q (fun d χ => Real.sqrt
      (primitiveCharacterPrefixMaxSquare b M L d χ))
  have hlocal := hLS R Q L b M hR hQ
  have hXR : X ^ 2 = (N : ℝ) ^ 2 / R := by
    dsimp [X]
    rw [div_pow, Real.sq_sqrt hRR.le]
  have hYQ : Y ^ 2 = (Q : ℝ) ^ 2 * N := by
    dsimp [Y]
    rw [mul_pow, Real.sq_sqrt hNN]
  have hparts : ((L : ℝ) * E) / R + (Q : ℝ) ^ 2 * E ≤ X ^ 2 + Y ^ 2 := by
    rw [hXR, hYQ]
    exact add_le_add (div_le_div_of_nonneg_right hdiag hRR.le)
      (mul_le_mul_of_nonneg_left henergy (sq_nonneg (Q : ℝ)))
  have htarget :
      K ^ 2 * J ^ 2 * (((L : ℝ) * E) / R + (Q : ℝ) ^ 2 * E) ≤
        (K * J * (X + Y)) ^ 2 := by
    calc
      _ ≤ K ^ 2 * J ^ 2 * (X ^ 2 + Y ^ 2) := by
        gcongr
      _ ≤ K ^ 2 * J ^ 2 * (X + Y) ^ 2 := by
        gcongr
        nlinarith
      _ = _ := by ring
  have hsq :
      (highConductorPrimitiveMean R Q
        (fun d χ => Real.sqrt
          (primitiveCharacterPrefixMaxSquare b M L d χ))) ^ 2 ≤
        (K * J * (X + Y)) ^ 2 := by
    exact hsquare.trans (hlocal.trans (by simpa [E, J] using htarget))
  have ht0 : 0 ≤ K * J * (X + Y) := by positivity
  have := (sq_le_sq₀ hmean0 ht0).mp hsq
  simpa [J, X, Y] using this

end
end AnalyticNumberTheory.LargeSieve
