import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLLocalFiniteDiskExplicitFormula
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticTatuzawaMultiplicativeValueTransfer

/-!
# The actual four-factor local zero-repulsion identity

This file combines three finite-disk factorizations, for `χ₁`, `χ₂`, and
`χ₁χ₂`, with the actual conductor/gamma bridge and the Euler-product positivity
of `ζ L(χ₁) L(χ₂) L(χ₁χ₂)`.  The only remainder is the sum of the three local
nonvanishing factors' logarithmic derivatives.
-/

open Complex Metric Finset
open ArithmeticFunction hiding log
open scoped LSeries.notation BigOperators

namespace AnalyticNumberTheory.LargeSieve
namespace TatuzawaZeroContribution

noncomputable section

open TatuzawaMultiplicativeTransfer

/-- An actual choice of the finite zero divisor and nonvanishing local factor
for one symmetrically completed Dirichlet L-function. -/
structure CharacterLocalDiskData {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (c : ℂ) (R : ℝ) where
  D : ℂ → ℤ
  S : Finset ℂ
  g : ℂ → ℂ
  D_nonneg : ∀ z, 0 ≤ D z
  mem_iff : ∀ z, z ∈ S ↔ z ∈ ball c R ∧ symmetricCompletedLFunction χ z = 0
  g_analytic : AnalyticOnNhd ℂ g (ball c R)
  g_ne_zero : ∀ z ∈ ball c R, g z ≠ 0
  formula : ∀ s ∈ ball c R, symmetricCompletedLFunction χ s ≠ 0 →
    logDeriv (symmetricCompletedLFunction χ) s =
      ∑ ρ ∈ S, ((D ρ).toNat : ℂ) / (s - ρ) + logDeriv g s

/-- The local factorization theorem makes an actual disk datum; no formula is
passed in abstractly. -/
theorem CharacterLocalDiskData.exists {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    Nonempty (CharacterLocalDiskData χ c R) := by
  obtain ⟨D, S, g, hD, hS, hg, hg0, hformula⟩ :=
    symmetricCompletedLFunction_localFiniteDisk_explicitFormula χ hχ c hR
  exact ⟨⟨D, S, g, hD, hS, hg, hg0, hformula⟩⟩

/-- The real part of the finite zero sum, with its actual multiplicities. -/
def CharacterLocalDiskData.zeroSum {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} {c : ℂ} {R : ℝ}
    (d : CharacterLocalDiskData χ c R) (σ : ℝ) : ℝ :=
  ∑ ρ ∈ d.S, (d.D ρ).toNat * zeroKernel σ ρ

private lemma re_weighted_reciprocal (n : ℕ) (σ : ℝ) (ρ : ℂ) :
    (((n : ℂ) / ((σ : ℂ) - ρ))).re = n * zeroKernel σ ρ := by
  rw [div_eq_mul_inv, zeroKernel]
  simp

private lemma CharacterLocalDiskData.re_zeroSum {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} {c : ℂ} {R : ℝ}
    (d : CharacterLocalDiskData χ c R) (σ : ℝ) :
    (∑ ρ ∈ d.S, ((d.D ρ).toNat : ℂ) / ((σ : ℂ) - ρ)).re = d.zeroSum σ := by
  simp only [CharacterLocalDiskData.zeroSum, Complex.re_sum, re_weighted_reciprocal]

lemma CharacterLocalDiskData.zeroSum_nonneg {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} {c : ℂ} {R : ℝ}
    (d : CharacterLocalDiskData χ c R) {σ : ℝ}
    (hstrip : ∀ ρ ∈ d.S, ρ.re ≤ σ) : 0 ≤ d.zeroSum σ := by
  apply sum_nonneg
  intro ρ hρ
  exact mul_nonneg (Nat.cast_nonneg _) (zeroKernel_nonneg (hstrip ρ hρ))

lemma CharacterLocalDiskData.zeroKernel_le_zeroSum {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} {c : ℂ} {R : ℝ}
    (d : CharacterLocalDiskData χ c R) {σ : ℝ} {β : ℂ}
    (hβ : β ∈ d.S) (hmult : 1 ≤ (d.D β).toNat)
    (hstrip : ∀ ρ ∈ d.S, ρ.re ≤ σ) :
    zeroKernel σ β ≤ d.zeroSum σ := by
  have hk : 0 ≤ zeroKernel σ β := zeroKernel_nonneg (hstrip β hβ)
  have hm : (1 : ℝ) ≤ (d.D β).toNat := by exact_mod_cast hmult
  calc
    zeroKernel σ β ≤ (d.D β).toNat * zeroKernel σ β := by
      simpa using mul_le_mul_of_nonneg_right hm hk
    _ ≤ d.zeroSum σ := by
      rw [CharacterLocalDiskData.zeroSum]
      exact single_le_sum (f := fun ρ ↦ ((d.D ρ).toNat : ℝ) * zeroKernel σ ρ)
        (fun ρ hρ ↦ mul_nonneg (Nat.cast_nonneg _) (zeroKernel_nonneg (hstrip ρ hρ))) hβ

private lemma symmetricCompletedLFunction_ne_zero_of_one_lt
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {σ : ℝ} (hσ : 1 < σ) : symmetricCompletedLFunction χ σ ≠ 0 := by
  have hL : χ.LFunction (σ : ℂ) ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by simpa using hσ.le)
  have hcompleted : χ.completedLFunction (σ : ℂ) ≠ 0 := by
    intro hz
    apply hL
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ σ
      (Or.inl (by exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hσ))))]
    simp [hz]
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  exact mul_ne_zero (by simp [hq]) hcompleted

/-- Combine one character's archimedean bridge with its actual local zero sum. -/
private lemma CharacterLocalDiskData.negLogDerivative_re_eq
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {c : ℂ} {R : ℝ} (d : CharacterLocalDiskData χ c R)
    {σ : ℝ} (hσ : 1 < σ) (hσdisk : (σ : ℂ) ∈ ball c R) :
    (-deriv χ.LFunction σ / χ.LFunction σ).re =
      (conductorGammaTerm χ σ).re - (d.zeroSum σ + (logDeriv d.g σ).re) := by
  have hL : χ.LFunction (σ : ℂ) ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by simpa using hσ.le)
  have hbridge := negLogDerivative_re_eq_conductorGamma_sub_completed χ hχ
    (lt_trans zero_lt_one hσ) hL
  rw [← logDeriv_apply, d.formula σ hσdisk
    (symmetricCompletedLFunction_ne_zero_of_one_lt χ hχ hσ),
    add_re, d.re_zeroSum] at hbridge
  exact hbridge

/-- The actual four-factor negative logarithmic derivative, retaining the zeta
factor in its standard L-series form. -/
def actualFourFactorLogDerivative {q₁ q₂ : ℕ}
    [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) (σ : ℝ) : ℝ :=
  (-deriv (L fun _ : ℕ ↦ (1 : ℂ)) (σ : ℂ) /
      L (fun _ : ℕ ↦ (1 : ℂ)) (σ : ℂ)).re +
    (-deriv χ₁.LFunction (σ : ℂ) / χ₁.LFunction (σ : ℂ)).re +
    (-deriv χ₂.LFunction (σ : ℂ) / χ₂.LFunction (σ : ℂ)).re +
    (-deriv (pairCharacter χ₁ χ₂).LFunction (σ : ℂ) /
      (pairCharacter χ₁ χ₂).LFunction (σ : ℂ)).re

/-- The exact identity obtained by putting all three actual local
factorizations on one disk.  Zeros outside the disk occur only through the
three concrete `g'/g` terms. -/
theorem actualFourFactor_localZeroIdentity
    {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hpair : pairCharacter χ₁ χ₂ ≠ 1)
    {c : ℂ} {R : ℝ}
    (d₁ : CharacterLocalDiskData χ₁ c R)
    (d₂ : CharacterLocalDiskData χ₂ c R)
    (dp : CharacterLocalDiskData (pairCharacter χ₁ χ₂) c R)
    {σ : ℝ} (hσ : 1 < σ) (hσdisk : (σ : ℂ) ∈ ball c R) :
    actualFourFactorLogDerivative χ₁ χ₂ σ =
      (-deriv (L fun _ : ℕ ↦ (1 : ℂ)) (σ : ℂ) /
        L (fun _ : ℕ ↦ (1 : ℂ)) (σ : ℂ)).re +
      (conductorGammaTerm χ₁ σ).re + (conductorGammaTerm χ₂ σ).re +
      (conductorGammaTerm (pairCharacter χ₁ χ₂) σ).re -
      d₁.zeroSum σ - d₂.zeroSum σ - dp.zeroSum σ -
      ((logDeriv d₁.g σ).re + (logDeriv d₂.g σ).re + (logDeriv dp.g σ).re) := by
  rw [actualFourFactorLogDerivative,
    d₁.negLogDerivative_re_eq hχ₁ hσ hσdisk,
    d₂.negLogDerivative_re_eq hχ₂ hσ hσdisk,
    dp.negLogDerivative_re_eq hpair hσ hσdisk]
  ring



end
end TatuzawaZeroContribution
end AnalyticNumberTheory.LargeSieve
