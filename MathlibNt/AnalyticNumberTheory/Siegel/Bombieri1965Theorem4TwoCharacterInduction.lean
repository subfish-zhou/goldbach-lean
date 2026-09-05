import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterConvolution
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticValueAtOnePositive

/-!
# Two-character induction with the missing Euler factors retained

This modern reduction uses a common multiple of the two levels, not a
coprimality assumption. The product character need not be primitive.
All three finite Euler products remain in the analytic identity.
-/

open Complex Finset

namespace DirichletCharacter

variable {q r Q : ℕ}

local instance (χ : DirichletCharacter ℂ Q) [NeZero Q] : NeZero χ.conductor :=
  ⟨χ.conductor_ne_zero⟩

/-- The exact Euler correction when a character is induced to level `Q`. -/
noncomputable def inductionEulerProduct
    (χ : DirichletCharacter ℂ q) (Q : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ Q.primeFactors, (1 - χ p * (p : ℂ) ^ (-s))

theorem sq_changeLevel_eq_one {q Q : ℕ} (h : q ∣ Q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) :
    (changeLevel h χ) ^ 2 = 1 := by
  rw [← map_pow, hχ, map_one]

theorem sq_mul_eq_one {χ ψ : DirichletCharacter ℂ Q}
    (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1) :
    (χ * ψ) ^ 2 = 1 := by
  rw [mul_pow, hχ, hψ, one_mul]

/-- Distinct quadratic characters have nonprincipal product. -/
theorem mul_ne_one_of_quadratic_ne {χ ψ : DirichletCharacter ℂ Q}
    (hψ : ψ ^ 2 = 1) (hne : χ ≠ ψ) : χ * ψ ≠ 1 := by
  intro h
  apply hne
  calc
    χ = χ * (ψ * ψ) := by rw [← pow_two, hψ, mul_one]
    _ = ψ := by rw [← mul_assoc, h, one_mul]

/-- Distinct primitive characters remain distinct at any common multiple.
Distinctness is stated by their actual values, even when the levels differ. -/
theorem changeLevel_ne_of_primitive_values [NeZero Q]
    (hq : q ∣ Q) (hr : r ∣ Q) (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (hne : ∃ n : ℕ, χ n ≠ ψ n) :
    changeLevel hq χ ≠ changeLevel hr ψ := by
  intro heq
  have hqr : q = r := by
    have hc := congrArg conductor heq
    change χ.conductor = q at hχ
    change ψ.conductor = r at hψ
    simpa only [conductor_changeLevel, hχ, hψ] using hc
  subst r
  have hchars : χ = ψ := changeLevel_injective hq heq
  obtain ⟨n, hn⟩ := hne
  exact hn (congrArg (fun η : DirichletCharacter ℂ q => η n) hchars)

theorem primitiveCharacter_sq_eq_one [NeZero Q]
    {χ : DirichletCharacter ℂ Q} (hχ : χ ^ 2 = 1) :
    χ.primitiveCharacter ^ 2 = 1 := by
  apply changeLevel_injective χ.conductor_dvd_level
  rw [map_pow, changeLevel_primitiveCharacter, hχ, map_one]

theorem primitiveCharacter_ne_one_of_ne_one
    {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  intro h
  apply hχ
  rw [← changeLevel_primitiveCharacter χ, h, map_one]

/-- The conductor reduction is an equality for the actual continued L-function,
including at one when the character is nonprincipal. -/
theorem LFunction_eq_primitive_mul_inductionEulerProduct [NeZero Q]
    (χ : DirichletCharacter ℂ Q) {s : ℂ} (hs : χ ≠ 1 ∨ s ≠ 1) :
    χ.LFunction s =
      χ.primitiveCharacter.LFunction s *
        inductionEulerProduct χ.primitiveCharacter Q s := by
  simpa only [changeLevel_primitiveCharacter, inductionEulerProduct] using
    LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
      (hs.imp primitiveCharacter_ne_one_of_ne_one id)

/-- Full induction identity for the actual four-factor product. Neither the
levels nor the conductor of their product are assumed coprime. -/
theorem twoCharacter_LFunction_product_induction
    [NeZero q] [NeZero r] [NeZero Q]
    (hq : q ∣ Q) (hr : r ∣ Q)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    {s : ℂ} (hχ : χ ≠ 1 ∨ s ≠ 1) (hψ : ψ ≠ 1 ∨ s ≠ 1)
    (hprod : changeLevel hq χ * changeLevel hr ψ ≠ 1 ∨ s ≠ 1) :
    riemannZeta s * (changeLevel hq χ).LFunction s *
        (changeLevel hr ψ).LFunction s *
        (changeLevel hq χ * changeLevel hr ψ).LFunction s =
      (riemannZeta s * χ.LFunction s * ψ.LFunction s *
        (changeLevel hq χ * changeLevel hr ψ).primitiveCharacter.LFunction s) *
      (inductionEulerProduct χ Q s * inductionEulerProduct ψ Q s *
        inductionEulerProduct
          (changeLevel hq χ * changeLevel hr ψ).primitiveCharacter Q s) := by
  rw [LFunction_changeLevel hq χ hχ, LFunction_changeLevel hr ψ hψ,
    LFunction_eq_primitive_mul_inductionEulerProduct _ hprod]
  unfold inductionEulerProduct
  ring

private theorem norm_character_prime_cpow_le
    (χ : DirichletCharacter ℂ q) (p : ℕ) (β : ℝ) :
    ‖χ p * (p : ℂ) ^ (-(β : ℂ))‖ ≤ (p : ℝ) ^ (-β) := by
  rw [norm_mul, ← ofReal_neg, norm_cpow_real, Complex.norm_natCast]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    (norm_le_one χ p)

/-- Explicit upper Euler loss at every real argument. -/
theorem norm_inductionEulerProduct_le
    (χ : DirichletCharacter ℂ q) (Q : ℕ) (β : ℝ) :
    ‖inductionEulerProduct χ Q (β : ℂ)‖ ≤
      ∏ p ∈ Q.primeFactors, (1 + (p : ℝ) ^ (-β)) := by
  rw [inductionEulerProduct, norm_prod]
  apply prod_le_prod (fun _ _ => norm_nonneg _)
  intro p _
  exact (norm_sub_le _ _).trans (by
    simpa using add_le_add_left (norm_character_prime_cpow_le χ p β) 1)

private theorem prime_rpow_neg_lt_one {p : ℕ} (hp : p.Prime)
    {β : ℝ} (hβ : 0 < β) : (p : ℝ) ^ (-β) < 1 :=
  (Real.rpow_lt_one_iff_of_pos (by exact_mod_cast hp.pos)).mpr
    (Or.inl ⟨by exact_mod_cast hp.one_lt, neg_neg_of_pos hβ⟩)

/-- The full lower Euler loss is retained, rather than silently identifying an
imprimitive L-value with its primitive L-value. -/
theorem prod_one_sub_rpow_le_norm_inductionEulerProduct
    (χ : DirichletCharacter ℂ q) (Q : ℕ) {β : ℝ} (hβ : 0 < β) :
    (∏ p ∈ Q.primeFactors, (1 - (p : ℝ) ^ (-β))) ≤
      ‖inductionEulerProduct χ Q (β : ℂ)‖ := by
  rw [inductionEulerProduct, norm_prod]
  apply prod_le_prod
    (fun p hp => sub_nonneg.mpr
      (prime_rpow_neg_lt_one (Nat.prime_of_mem_primeFactors hp) hβ).le)
  intro p _
  have h := norm_add_le (1 - χ p * (p : ℂ) ^ (-(β : ℂ)))
    (χ p * (p : ℂ) ^ (-(β : ℂ)))
  rw [sub_add_cancel, norm_one] at h
  linarith [norm_character_prime_cpow_le χ p β]

/-- Euler induction creates no positive-real zero, even for nonquadratic
characters or overlapping levels. -/
theorem inductionEulerProduct_ne_zero
    (χ : DirichletCharacter ℂ q) (Q : ℕ) {β : ℝ} (hβ : 0 < β) :
    inductionEulerProduct χ Q (β : ℂ) ≠ 0 := by
  apply norm_pos_iff.mp
  refine lt_of_lt_of_le ?_
    (prod_one_sub_rpow_le_norm_inductionEulerProduct χ Q hβ)
  exact prod_pos fun p hp => sub_pos.mpr
    (prime_rpow_neg_lt_one (Nat.prime_of_mem_primeFactors hp) hβ)

/-- In particular, a produced real zero persists under induction and reflects
back to the original character; the bad-prime factors cannot create it. -/
theorem LFunction_changeLevel_real_eq_zero_iff
    [NeZero q] [NeZero Q] (hq : q ∣ Q) (χ : DirichletCharacter ℂ q)
    {β : ℝ} (hβ : 0 < β) (hχ : χ ≠ 1 ∨ β ≠ 1) :
    (changeLevel hq χ).LFunction (β : ℂ) = 0 ↔ χ.LFunction (β : ℂ) = 0 := by
  rw [LFunction_changeLevel hq χ
    (hχ.imp id (fun h => by exact_mod_cast h))]
  exact mul_eq_zero_iff_right (inductionEulerProduct_ne_zero χ Q hβ)

/-- Exact primitive reduction of a positive-real zero of an imprimitive
character, including a nonprincipal character at one. -/
theorem LFunction_real_eq_zero_iff_primitive
    [NeZero Q] (χ : DirichletCharacter ℂ Q)
    {β : ℝ} (hβ : 0 < β) (hχ : χ ≠ 1 ∨ β ≠ 1) :
    χ.LFunction (β : ℂ) = 0 ↔ χ.primitiveCharacter.LFunction (β : ℂ) = 0 := by
  rw [LFunction_eq_primitive_mul_inductionEulerProduct χ
    (hχ.imp id (fun h => by exact_mod_cast h))]
  exact mul_eq_zero_iff_right (inductionEulerProduct_ne_zero χ.primitiveCharacter Q hβ)

/-- The actual residue coefficient, not an independently chosen main term. -/
noncomputable def twoCharacterResidue [NeZero Q]
    (χ ψ : DirichletCharacter ℂ Q) : ℂ :=
  χ.LFunction 1 * ψ.LFunction 1 * (χ * ψ).LFunction 1

open Filter
open scoped Topology ComplexOrder

/-- The four-factor function has this actual residue at one whenever all
three character factors are nonprincipal. -/
theorem twoCharacter_product_residue_one [NeZero Q]
    (χ ψ : DirichletCharacter ℂ Q)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) :
    Tendsto (fun s : ℂ => (s - 1) *
      (riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ * ψ).LFunction s))
      (𝓝[≠] 1) (𝓝 (twoCharacterResidue χ ψ)) := by
  have hc (η : DirichletCharacter ℂ Q) (hη : η ≠ 1) :
      Tendsto η.LFunction (𝓝[≠] (1 : ℂ)) (𝓝 (η.LFunction 1)) :=
    (η.differentiableAt_LFunction 1 (Or.inr hη)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  convert ((riemannZeta_residue_one.mul (hc χ hχ)).mul (hc ψ hψ)).mul
    (hc (χ * ψ) hprod) using 1
  · funext s
    ring
  · simp [twoCharacterResidue]

/-- Distinct nonprincipal quadratic characters give a strictly positive
real residue. Distinctness is essential: the diagonal has another pole. -/
theorem twoCharacterResidue_pos [NeZero Q]
    {χ ψ : DirichletCharacter ℂ Q}
    (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (hχ1 : χ ≠ 1) (hψ1 : ψ ≠ 1) (hne : χ ≠ ψ) :
    0 < twoCharacterResidue χ ψ := by
  have hp (η : DirichletCharacter ℂ Q) (hη : η ^ 2 = 1) (hη1 : η ≠ 1) :
      0 < η.LFunction 1 := by
    exact Complex.pos_iff.mpr
      ⟨LFunction_apply_one_re_pos_of_sq_eq_one hη hη1,
        (LFunction_apply_one_im_eq_zero_of_sq_eq_one hη hη1).symm⟩
  exact mul_pos (mul_pos (hp χ hχ hχ1) (hp ψ hψ hψ1))
    (hp (χ * ψ) (sq_mul_eq_one hχ hψ) (mul_ne_one_of_quadratic_ne hψ hne))

/-- The main-term coefficient after arbitrary common-level induction,
with all three missing Euler products explicit. -/
theorem twoCharacterResidue_induction
    [NeZero q] [NeZero r] [NeZero Q]
    (hq : q ∣ Q) (hr : r ∣ Q)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hprod : changeLevel hq χ * changeLevel hr ψ ≠ 1) :
    twoCharacterResidue (changeLevel hq χ) (changeLevel hr ψ) =
      (χ.LFunction 1 * ψ.LFunction 1 *
        (changeLevel hq χ * changeLevel hr ψ).primitiveCharacter.LFunction 1) *
      (inductionEulerProduct χ Q 1 * inductionEulerProduct ψ Q 1 *
        inductionEulerProduct
          (changeLevel hq χ * changeLevel hr ψ).primitiveCharacter Q 1) := by
  rw [twoCharacterResidue, LFunction_changeLevel hq χ (Or.inl hχ),
    LFunction_changeLevel hr ψ (Or.inl hψ),
    LFunction_eq_primitive_mul_inductionEulerProduct _ (Or.inl hprod)]
  unfold inductionEulerProduct
  ring

end DirichletCharacter
