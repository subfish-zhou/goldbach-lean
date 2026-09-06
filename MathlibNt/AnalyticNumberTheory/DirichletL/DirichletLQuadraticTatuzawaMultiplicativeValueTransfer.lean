import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticTatuzawaPairRankin
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticTatuzawaExceptionalUniqueness
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLGlobalConductorLogValueBound
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLGlobalConductorLogDerivativeBound

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

lemma pairCharacter_apply {q₁ q₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) (n : ℕ) :
    pairCharacter χ₁ χ₂ n = χ₁ n * χ₂ n := by
  by_cases hcop : IsCoprime (n : ℤ) ((q₁ : ℤ) * (q₂ : ℤ))
  · have hcop' : IsCoprime (n : ℤ) (q₁ * q₂ : ℕ) := by simpa using hcop
    have h₁ := DirichletCharacter.changeLevel_eq_cast_of_dvd'
      χ₁ (dvd_mul_right q₁ q₂) hcop'
    have h₂ := DirichletCharacter.changeLevel_eq_cast_of_dvd'
      χ₂ (dvd_mul_left q₂ q₁) hcop'
    rw [pairCharacter, MulChar.mul_apply, ← Int.cast_natCast]
    rw [h₁, h₂]
    simp
  · have hcop' : ¬ IsCoprime (n : ℤ) (q₁ * q₂ : ℕ) := by simpa using hcop
    have hzero : pairCharacter χ₁ χ₂ (n : ℤ) = 0 :=
      (DirichletCharacter.apply_eq_zero_iff (pairCharacter χ₁ χ₂) (n : ℤ)).2 hcop'
    have hzeroNat : pairCharacter χ₁ χ₂ n = 0 := by simpa using hzero
    have hsplit : ¬ IsCoprime (n : ℤ) q₁ ∨ ¬ IsCoprime (n : ℤ) q₂ := by
      exact not_and_or.mp (mt IsCoprime.mul_right_iff.mpr hcop)
    rcases hsplit with h₁ | h₂
    · have hz := (DirichletCharacter.apply_eq_zero_iff χ₁ (n : ℤ)).2 h₁
      have hzNat : χ₁ n = 0 := by simpa using hz
      rw [hzNat, zero_mul]
      exact hzeroNat
    · have hz := (DirichletCharacter.apply_eq_zero_iff χ₂ (n : ℤ)).2 h₂
      have hzNat : χ₂ n = 0 := by simpa using hz
      rw [hzNat, mul_zero]
      exact hzeroNat

lemma pairCharacter_square_eq_one {q₁ q₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) :
    pairCharacter χ₁ χ₂ ^ 2 = 1 := by
  rw [pairCharacter, mul_pow]
  rw [← map_pow, ← map_pow, h₁, h₂, map_one, map_one, one_mul]

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
  haveI : NeZero x.modulus := ⟨x.modulus_ne⟩
  haveI : NeZero y.modulus := ⟨y.modulus_ne⟩
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

/-- The real value at one of the common-level product character. -/
def pairValue (x y : PrimitiveQuadraticDatum) : ℝ :=
  letI : NeZero (x.modulus * y.modulus) :=
    ⟨Nat.mul_ne_zero x.modulus_ne y.modulus_ne⟩
  ((pairCharacter x.character y.character).LFunction 1).re

/-- The product character of distinct primitive quadratic data has a strictly
positive value at one.  This is the first value-at-one input supplied by the
four-factor Euler product, rather than by an exception predicate. -/
theorem pairValue_pos_of_datum_ne
    (x y : PrimitiveQuadraticDatum) (hxy : x ≠ y) :
    0 < pairValue x y := by
  haveI : NeZero (x.modulus * y.modulus) :=
    ⟨Nat.mul_ne_zero x.modulus_ne y.modulus_ne⟩
  simpa [pairValue] using
    (DirichletCharacter.LFunction_apply_one_re_pos_of_sq_eq_one
      (pairCharacter_square_eq_one x.character y.character
        x.square_eq_one y.square_eq_one)
      (pairCharacter_ne_one_of_datum_ne x y hxy))

/-- All three non-zeta values in the four-factor product are positive at one
for distinct primitive quadratic data. -/
theorem fourFactor_nonZetaValueProductAtOne_pos
    (x y : PrimitiveQuadraticDatum) (hxy : x ≠ y) :
    0 < x.value * y.value * pairValue x y :=
  mul_pos (mul_pos x.value_pos y.value_pos)
    (pairValue_pos_of_datum_ne x y hxy)

/-- The local Euler coefficient for
`ζ(s)L(s,χ₁)L(s,χ₂)L(s,χ₁χ₂)` is nonnegative.  At every natural number each
quadratic value is `0`, `1`, or `-1`, and the coefficient is the product
`(1 + χ₁(n))(1 + χ₂(n))`. -/
theorem fourFactorEulerCoefficient_nonneg {q₁ q₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) (n : ℕ) :
    0 ≤ (1 + χ₁ n + χ₂ n + pairCharacter χ₁ χ₂ n : ℂ) := by
  rw [pairCharacter_apply]
  rcases (MulChar.isQuadratic_iff_sq_eq_one.mpr h₁ n) with hχ₁ | hχ₁ | hχ₁ <;>
    rcases (MulChar.isQuadratic_iff_sq_eq_one.mpr h₂ n) with hχ₂ | hχ₂ | hχ₂ <;>
    simp [hχ₁, hχ₂] <;> norm_num

/-- Termwise von-Mangoldt positivity for the logarithmic derivative of the
four-factor Euler product. -/
theorem fourFactor_logDerivativeTerm_nonneg {q₁ q₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) (σ : ℝ) (n : ℕ) :
    0 ≤ (LSeries.term ((fun n : ℕ ↦ (1 : DirichletCharacter ℂ 1) n) *
        fun n ↦ (Λ n : ℂ)) (σ : ℂ) n).re +
      (LSeries.term ((fun n : ℕ ↦ χ₁ n) * fun n ↦ (Λ n : ℂ)) (σ : ℂ) n).re +
      (LSeries.term ((fun n : ℕ ↦ χ₂ n) * fun n ↦ (Λ n : ℂ)) (σ : ℂ) n).re +
      (LSeries.term ((fun n : ℕ ↦ pairCharacter χ₁ χ₂ n) *
        fun n ↦ (Λ n : ℂ)) (σ : ℂ) n).re := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [LSeries.term]
  have ha : (((Λ n : ℝ) / (n : ℝ) ^ σ : ℝ) : ℂ) =
      (Λ n : ℂ) / (n : ℂ) ^ (σ : ℂ) := by
    rw [ofReal_div, ofReal_cpow (Nat.cast_nonneg n), ofReal_natCast]
  have hweight : 0 ≤ (Λ n : ℝ) / (n : ℝ) ^ σ :=
    div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  have hterm (z : ℂ) :
      z * (Λ n : ℂ) / (n : ℂ) ^ (σ : ℂ) =
        z * ((Λ n : ℝ) / (n : ℝ) ^ σ : ℝ) := by
    rw [ha]
    ring
  simp only [LSeries.term, if_neg hn.ne', Pi.mul_apply,
    DirichletCharacter.modOne_eq_one, Pi.one_apply, one_mul]
  rw [← ha, hterm, hterm, hterm]
  -- The same Euler coefficient controls each term after multiplying by its
  -- nonnegative von-Mangoldt weight; no new quadratic-value case split is needed.
  have hcoefficient : 0 ≤ (1 + χ₁ n + χ₂ n + pairCharacter χ₁ χ₂ n : ℂ).re :=
    (RCLike.le_iff_re_im.mp (fourFactorEulerCoefficient_nonneg χ₁ χ₂ h₁ h₂ n)).1
  simpa only [Complex.add_re, Complex.one_re, Complex.zero_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    add_mul, one_mul] using mul_nonneg hcoefficient hweight

/-- The negative logarithmic derivative of
`ζ(s)L(s,χ₁)L(s,χ₂)L(s,χ₁χ₂)` is nonnegative on the real half-line `σ > 1`.
This is the source-free Euler-product positivity bearing for the subsequent
Deuring--Heilbronn zero-repulsion argument. -/
theorem fourFactor_negLogDerivative_nonneg {q₁ q₂ : ℕ}
    [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) (σ : ℝ) (hσ : 1 < σ) :
    0 ≤ (-deriv (L fun _ : ℕ ↦ (1 : ℂ)) (σ : ℂ) /
          L (fun _ : ℕ ↦ (1 : ℂ)) (σ : ℂ)).re +
      (-deriv (L fun n : ℕ ↦ χ₁ n) (σ : ℂ) /
          L (fun n : ℕ ↦ χ₁ n) (σ : ℂ)).re +
      (-deriv (L fun n : ℕ ↦ χ₂ n) (σ : ℂ) /
          L (fun n : ℕ ↦ χ₂ n) (σ : ℂ)).re +
      (-deriv (L fun n : ℕ ↦ pairCharacter χ₁ χ₂ n) (σ : ℂ) /
          L (fun n : ℕ ↦ pairCharacter χ₁ χ₂ n) (σ : ℂ)).re := by
  have h0 := (1 : DirichletCharacter ℂ 1).LSeriesSummable_twist_vonMangoldt
    (s := (σ : ℂ)) (by simpa using hσ)
  have h1s := χ₁.LSeriesSummable_twist_vonMangoldt
    (s := (σ : ℂ)) (by simpa using hσ)
  have h2s := χ₂.LSeriesSummable_twist_vonMangoldt
    (s := (σ : ℂ)) (by simpa using hσ)
  have hps := (pairCharacter χ₁ χ₂).LSeriesSummable_twist_vonMangoldt
    (s := (σ : ℂ)) (by simpa using hσ)
  have hone : (fun n : ℕ ↦ (1 : DirichletCharacter ℂ 1) n) =
      (fun _ : ℕ ↦ (1 : ℂ)) := DirichletCharacter.modOne_eq_one
  rw [← hone]
  rw [← DirichletCharacter.LSeries_twist_vonMangoldt_eq
      (1 : DirichletCharacter ℂ 1) (by simpa using hσ),
    ← χ₁.LSeries_twist_vonMangoldt_eq (by simpa using hσ),
    ← χ₂.LSeries_twist_vonMangoldt_eq (by simpa using hσ),
    ← (pairCharacter χ₁ χ₂).LSeries_twist_vonMangoldt_eq (by simpa using hσ)]
  have hs0 := (hasSum_re h0.hasSum).summable
  have hs1 := (hasSum_re h1s.hasSum).summable
  have hs2 := (hasSum_re h2s.hasSum).summable
  have hsp := (hasSum_re hps.hasSum).summable
  simp only [LSeries]
  rw [Complex.re_tsum h0, Complex.re_tsum h1s, Complex.re_tsum h2s,
    Complex.re_tsum hps, ← hs0.tsum_add hs1,
    ← (hs0.add hs1).tsum_add hs2,
    ← ((hs0.add hs1).add hs2).tsum_add hsp]
  exact tsum_nonneg (fourFactor_logDerivativeTerm_nonneg χ₁ χ₂ h₁ h₂ σ)

/-- Integrated monotonicity of the four-factor negative logarithmic derivative
on every compact real interval to the right of one.  This is the exact
calculus consequence of Euler-coefficient positivity: no zero-repulsion or
value-product hypothesis is inserted. -/
theorem integral_fourFactor_negLogDerivative_nonneg {q₁ q₂ : ℕ}
    [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    0 ≤ ∫ σ in a..b,
      ((-deriv (L fun _ : ℕ ↦ (1 : ℂ)) (σ : ℂ) /
            L (fun _ : ℕ ↦ (1 : ℂ)) (σ : ℂ)).re +
        (-deriv (L fun n : ℕ ↦ χ₁ n) (σ : ℂ) /
            L (fun n : ℕ ↦ χ₁ n) (σ : ℂ)).re +
        (-deriv (L fun n : ℕ ↦ χ₂ n) (σ : ℂ) /
            L (fun n : ℕ ↦ χ₂ n) (σ : ℂ)).re +
        (-deriv (L fun n : ℕ ↦ pairCharacter χ₁ χ₂ n) (σ : ℂ) /
            L (fun n : ℕ ↦ pairCharacter χ₁ χ₂ n) (σ : ℂ)).re) := by
  apply intervalIntegral.integral_nonneg hab
  intro σ hσ
  exact fourFactor_negLogDerivative_nonneg χ₁ χ₂ h₁ h₂ σ (ha.trans_le hσ.1)

end TatuzawaMultiplicativeTransfer
end
end AnalyticNumberTheory.LargeSieve
