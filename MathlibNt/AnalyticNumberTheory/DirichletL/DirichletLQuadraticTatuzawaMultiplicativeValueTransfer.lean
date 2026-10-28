import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticSiegelConvolution
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticTatuzawaExceptionalUniqueness

open Complex Finset
open ArithmeticFunction hiding log
open scoped LSeries.notation BigOperators ComplexOrder Real

namespace AnalyticNumberTheory.LargeSieve

noncomputable section

namespace TatuzawaMultiplicativeTransfer

/-- The common-level product of two characters of possibly different primitive
levels.  Its natural-number values are the pointwise products of the original
characters; the common level is used only to package that product as a
Dirichlet character. -/
noncomputable def pairCharacter {q₁ q₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    DirichletCharacter ℂ (q₁ * q₂) :=
  DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁ *
    DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂


/-- If the common-level product of two primitive quadratic characters is
principal, then the two primitive data are identical.  This is the dependent
bookkeeping needed before applying a distinct-character value-product bound:
the proof first recovers both divisibilities of the primitive levels from
`factorsThrough_gcd`, and only then transports the character equality across
the resulting equality of levels. -/
theorem datum_eq_of_pairCharacter_eq_one
    (x y : PrimitiveQuadraticDatum)
    (hpair : pairCharacter x.character y.character = 1) : x = y := by
  let χx := DirichletCharacter.changeLevel
    (dvd_mul_right x.modulus y.modulus) x.character
  let χy := DirichletCharacter.changeLevel
    (dvd_mul_left y.modulus x.modulus) y.character
  have hχy_sq : χy ^ 2 = 1 := by
    dsimp [χy]
    rw [← map_pow, y.square_eq_one, map_one]
  have hlift : χx = χy := by
    calc
      χx = χx * 1 := by simp
      _ = χx * (χy ^ 2) := by rw [hχy_sq]
      _ = (χx * χy) * χy := by simp [pow_two, mul_assoc]
      _ = 1 * χy := by simpa [χx, χy, pairCharacter] using congrArg (fun χ => χ * χy) hpair
      _ = χy := by simp
  have : NeZero x.modulus := ⟨x.modulus_ne⟩
  have : NeZero y.modulus := ⟨y.modulus_ne⟩
  have hxFactors : x.character.FactorsThrough (Nat.gcd x.modulus y.modulus) :=
    DirichletCharacter.factorsThrough_gcd x.character y.character hlift
  have hyFactors : y.character.FactorsThrough (Nat.gcd x.modulus y.modulus) := by
    rcases hxFactors with ⟨hxgcd, χgcd, hxeq⟩
    let hygcd := Nat.gcd_dvd_right x.modulus y.modulus
    refine ⟨hygcd, χgcd, ?_⟩
    apply DirichletCharacter.changeLevel_injective (dvd_mul_left y.modulus x.modulus)
    -- Compare both factorizations at the same product level, then compose lifts.
    change χy = _
    rw [← hlift]
    dsimp only [χx]
    rw [hxeq]
    simp only [← DirichletCharacter.changeLevel_trans]

  have hxy : x.modulus ∣ y.modulus := by
    have hxgcd : x.modulus ∣ Nat.gcd x.modulus y.modulus := by
      have hcdiv :=
        DirichletCharacter.conductor_dvd_of_mem_conductorSet x.character hxFactors
      rw [x.isPrimitive] at hcdiv
      exact hcdiv
    exact hxgcd.trans (Nat.gcd_dvd_right x.modulus y.modulus)
  have hyx : y.modulus ∣ x.modulus := by
    have hygcd : y.modulus ∣ Nat.gcd x.modulus y.modulus := by
      have hcdiv :=
        DirichletCharacter.conductor_dvd_of_mem_conductorSet y.character hyFactors
      rw [y.isPrimitive] at hcdiv
      exact hcdiv
    exact hygcd.trans (Nat.gcd_dvd_left x.modulus y.modulus)
  have hmod : x.modulus = y.modulus := Nat.dvd_antisymm hxy hyx
  cases x with
  | mk q hq χ hprimitive hsquare hne =>
      cases y with
      | mk r hr ψ jprimitive jsquare jne =>
          dsimp at hmod
          subst r
          have hχψ : χ = ψ := by
            apply DirichletCharacter.changeLevel_injective (dvd_mul_right q q)
            simpa [χx, χy] using hlift
          subst ψ
          rfl

/-- Distinct primitive quadratic data have a nonprincipal common-level product. -/
theorem pairCharacter_ne_one_of_datum_ne
    (x y : PrimitiveQuadraticDatum) (hxy : x ≠ y) :
    pairCharacter x.character y.character ≠ 1 := by
  intro hprincipal
  exact hxy (datum_eq_of_pairCharacter_eq_one x y hprincipal)


end TatuzawaMultiplicativeTransfer
end
end AnalyticNumberTheory.LargeSieve
