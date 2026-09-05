import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterInduction
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLPrincipalEulerCorrectionLogBound
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticTatuzawaMultiplicativeValueTransfer

open Complex Finset
open scoped ComplexOrder

namespace DirichletCharacter

/-- The actual finite induction correction costs only one logarithm.
No primitivity or divisibility hypothesis is needed for this stronger bound. -/
theorem FourFactorLogInduction_euler_one_le {q Q : ℕ}
    (χ : DirichletCharacter ℂ q) (hQ : 0 < Q) :
    ‖inductionEulerProduct χ Q 1‖ ≤ 1 + Real.log Q := by
  have h := norm_inductionEulerProduct_le χ Q (1 : ℝ)
  simp only [Complex.ofReal_one, Real.rpow_neg_one] at h
  exact h.trans (prod_one_add_inv_primeFactors_le_one_add_log Q hQ)

/-- The full-modulus third L-value, not its primitive replacement, pays one log. -/
theorem FourFactorLogInduction_LFunction_one_le {Q : ℕ} [NeZero Q]
    (χ : DirichletCharacter ℂ Q) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ 32 * (1 + Real.log Q) := by
  have hlog : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg (by
    exact_mod_cast (NeZero.pos Q))
  have h := DirichletLGlobalConductorLogValueBound.norm_LFunction_le_thirtytwo_mul_one_add_log_conductorHeightCutoff
    χ hχ (σ := 1) (t := 0) (by norm_num) (by norm_num) (by
      simp only [DirichletLGlobalConductorLogValueBound.dirichletLConductorHeightCutoff,
        DirichletLGlobalConductorLogValueBound.dirichletLHeightBlock, abs_zero,
        Nat.floor_zero, zero_add, mul_one]
      linarith [one_div_nonneg.mpr hlog])
  simpa [DirichletLGlobalConductorLogValueBound.dirichletLConductorHeightCutoff,
    DirichletLGlobalConductorLogValueBound.dirichletLHeightBlock] using h

theorem FourFactorLogInduction_norm_LFunction_one_eq_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ = (χ.LFunction 1).re := by
  have him := LFunction_apply_one_im_eq_zero_of_sq_eq_one hquad hχ
  have hpos := LFunction_apply_one_re_pos_of_sq_eq_one hquad hχ
  rw [← Complex.re_add_im (χ.LFunction 1), him]
  simp [abs_of_pos hpos]

/-- Literal induction formula at one plus the finite Euler bound. -/
theorem FourFactorLogInduction_changeLevel_one_le {q Q : ℕ}
    [NeZero q] [NeZero Q] (hq : q ∣ Q)
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    ‖(changeLevel hq χ).LFunction 1‖ ≤
      (χ.LFunction 1).re * (1 + Real.log Q) := by
  rw [LFunction_changeLevel hq χ (Or.inl hχ), norm_mul]
  change ‖χ.LFunction 1‖ * ‖inductionEulerProduct χ Q 1‖ ≤ _
  rw [FourFactorLogInduction_norm_LFunction_one_eq_re χ hquad hχ]
  exact mul_le_mul_of_nonneg_left (FourFactorLogInduction_euler_one_le χ (NeZero.pos Q))
    (LFunction_apply_one_re_pos_of_sq_eq_one hquad hχ).le

/-- Two genuine lifts pay two logs and their nonprincipal product pays one.
The constant is exactly 32; there is no polynomial modulus loss. -/
theorem FourFactorLogInduction_residue_norm_le {q r Q : ℕ}
    [NeZero q] [NeZero r] [NeZero Q] (hq : q ∣ Q) (hr : r ∣ Q)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχquad : χ ^ 2 = 1) (hψquad : ψ ^ 2 = 1)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hprod : changeLevel hq χ * changeLevel hr ψ ≠ 1) :
    ‖twoCharacterResidue (changeLevel hq χ) (changeLevel hr ψ)‖ ≤
      32 * (1 + Real.log Q)^3 * (χ.LFunction 1).re * (ψ.LFunction 1).re := by
  have hlog : 0 ≤ 1 + Real.log (Q : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ Q by exact_mod_cast (NeZero.pos Q))
    linarith
  have hχpos := (LFunction_apply_one_re_pos_of_sq_eq_one hχquad hχ).le
  have hψpos := (LFunction_apply_one_re_pos_of_sq_eq_one hψquad hψ).le
  rw [twoCharacterResidue, norm_mul, norm_mul]
  calc
    _ ≤ ((χ.LFunction 1).re * (1 + Real.log Q)) *
        ((ψ.LFunction 1).re * (1 + Real.log Q)) * (32 * (1 + Real.log Q)) := by
      apply mul_le_mul
      · exact mul_le_mul (FourFactorLogInduction_changeLevel_one_le hq χ hχquad hχ)
          (FourFactorLogInduction_changeLevel_one_le hr ψ hψquad hψ)
          (norm_nonneg _) (mul_nonneg hχpos hlog)
      · exact FourFactorLogInduction_LFunction_one_le _ hprod
      · exact norm_nonneg _
      · exact mul_nonneg (mul_nonneg hχpos hlog) (mul_nonneg hψpos hlog)
    _ = _ := by ring

end DirichletCharacter

namespace AnalyticNumberTheory.LargeSieve

open DirichletCharacter TatuzawaMultiplicativeTransfer

/-- The residue of the actual four-factor function after lifting both original
primitive characters to the product level. -/
noncomputable def FourFactorLogInduction_residue (x y : PrimitiveQuadraticDatum) : ℂ :=
  letI : NeZero (x.modulus * y.modulus) :=
    ⟨Nat.mul_ne_zero x.modulus_ne y.modulus_ne⟩
  twoCharacterResidue
    (changeLevel (dvd_mul_right x.modulus y.modulus) x.character)
    (changeLevel (dvd_mul_left y.modulus x.modulus) y.character)

/-- Distinct primitive data supply the nonprincipal product internally. -/
theorem FourFactorLogInduction_residue_pos_and_le
    (x y : PrimitiveQuadraticDatum) (hxy : x ≠ y) :
    0 < FourFactorLogInduction_residue x y ∧
    (FourFactorLogInduction_residue x y).re ≤
      32 * (1 + Real.log (x.modulus * y.modulus : ℕ))^3 * x.value * y.value := by
  let : NeZero x.modulus := ⟨x.modulus_ne⟩
  let : NeZero y.modulus := ⟨y.modulus_ne⟩
  let : NeZero (x.modulus * y.modulus) :=
    ⟨Nat.mul_ne_zero x.modulus_ne y.modulus_ne⟩
  let a := changeLevel (dvd_mul_right x.modulus y.modulus) x.character
  let b := changeLevel (dvd_mul_left y.modulus x.modulus) y.character
  have haquad : a ^ 2 = 1 := sq_changeLevel_eq_one _ x.square_eq_one
  have hbquad : b ^ 2 = 1 := sq_changeLevel_eq_one _ y.square_eq_one
  have ha : a ≠ 1 := by
    intro h
    apply x.ne_one
    exact changeLevel_injective (dvd_mul_right x.modulus y.modulus) (by simpa [a] using h)
  have hb : b ≠ 1 := by
    intro h
    apply y.ne_one
    exact changeLevel_injective (dvd_mul_left y.modulus x.modulus) (by simpa [b] using h)
  have hp : a * b ≠ 1 := pairCharacter_ne_one_of_datum_ne x y hxy
  have hab : a ≠ b := by
    intro heq
    apply hp
    rw [heq, ← pow_two, hbquad]
  constructor
  · exact twoCharacterResidue_pos haquad hbquad ha hb hab
  · exact (Complex.re_le_norm _).trans (FourFactorLogInduction_residue_norm_le
      (dvd_mul_right x.modulus y.modulus) (dvd_mul_left y.modulus x.modulus)
      x.character y.character x.square_eq_one y.square_eq_one x.ne_one y.ne_one hp)

/-- Real-valued consumer form of the actual residue estimate. -/
theorem FourFactorLogInduction_residue_re_pos_and_le
    (x y : PrimitiveQuadraticDatum) (hxy : x ≠ y) :
    0 < (FourFactorLogInduction_residue x y).re ∧
    (FourFactorLogInduction_residue x y).im = 0 ∧
    (FourFactorLogInduction_residue x y).re ≤
      32 * (1 + Real.log (x.modulus * y.modulus : ℕ))^3 * x.value * y.value := by
  obtain ⟨hp, hu⟩ := FourFactorLogInduction_residue_pos_and_le x y hxy
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hp
  exact ⟨hre, him.symm, hu⟩

end AnalyticNumberTheory.LargeSieve
