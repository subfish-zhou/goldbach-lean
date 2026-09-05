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
  rw [CharacterLocalDiskData.zeroSum]
  induction d.S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [sum_insert ha, sum_insert ha, add_re, ih, re_weighted_reciprocal]

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
  rw [CharacterLocalDiskData.zeroSum, ← sum_erase_add _ _ hβ]
  have hk : 0 ≤ zeroKernel σ β := zeroKernel_nonneg (hstrip β hβ)
  have hterm : zeroKernel σ β ≤ (d.D β).toNat * zeroKernel σ β := by
    have hm : (1 : ℝ) ≤ (d.D β).toNat := by exact_mod_cast hmult
    simpa using mul_le_mul_of_nonneg_right hm hk
  have herase : 0 ≤ ∑ ρ ∈ d.S.erase β, (d.D ρ).toNat * zeroKernel σ ρ := by
    apply sum_nonneg
    intro ρ hρ
    exact mul_nonneg (Nat.cast_nonneg _)
      (zeroKernel_nonneg (hstrip ρ (mem_of_mem_erase hρ)))
  linarith

private lemma symmetricCompletedLFunction_ne_zero_of_one_lt
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {σ : ℝ} (hσ : 1 < σ) : symmetricCompletedLFunction χ σ ≠ 0 := by
  have hL : χ.LFunction (σ : ℂ) ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by simpa using hσ.le)
  have hγ : χ.gammaFactor (σ : ℂ) ≠ 0 := gammaFactor_ne_zero_of_pos χ (lt_trans zero_lt_one hσ)
  have hcompleted : χ.completedLFunction (σ : ℂ) ≠ 0 := by
    intro hz
    apply hL
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ σ
      (Or.inl (by exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hσ))))]
    simp [hz]
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  exact mul_ne_zero (by simp [hq]) hcompleted

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
  have hL₁ : χ₁.LFunction (σ : ℂ) ≠ 0 :=
    χ₁.LFunction_ne_zero_of_one_le_re (Or.inl hχ₁) (by simpa using hσ.le)
  have hL₂ : χ₂.LFunction (σ : ℂ) ≠ 0 :=
    χ₂.LFunction_ne_zero_of_one_le_re (Or.inl hχ₂) (by simpa using hσ.le)
  have hLp : (pairCharacter χ₁ χ₂).LFunction (σ : ℂ) ≠ 0 :=
    (pairCharacter χ₁ χ₂).LFunction_ne_zero_of_one_le_re
      (Or.inl hpair) (by simpa using hσ.le)
  have hf₁ := d₁.formula σ hσdisk
    (symmetricCompletedLFunction_ne_zero_of_one_lt χ₁ hχ₁ hσ)
  have hf₂ := d₂.formula σ hσdisk
    (symmetricCompletedLFunction_ne_zero_of_one_lt χ₂ hχ₂ hσ)
  have hfp := dp.formula σ hσdisk
    (symmetricCompletedLFunction_ne_zero_of_one_lt (pairCharacter χ₁ χ₂) hpair hσ)
  have hb₁ := negLogDerivative_re_eq_conductorGamma_sub_completed χ₁ hχ₁
    (lt_trans zero_lt_one hσ) hL₁
  have hb₂ := negLogDerivative_re_eq_conductorGamma_sub_completed χ₂ hχ₂
    (lt_trans zero_lt_one hσ) hL₂
  have hbp := negLogDerivative_re_eq_conductorGamma_sub_completed
    (pairCharacter χ₁ χ₂) hpair (lt_trans zero_lt_one hσ) hLp
  rw [← logDeriv_apply] at hb₁ hb₂ hbp
  have hre₁ := congrArg Complex.re hf₁
  have hre₂ := congrArg Complex.re hf₂
  have hrep := congrArg Complex.re hfp
  simp only [add_re] at hre₁ hre₂ hrep
  rw [d₁.re_zeroSum] at hre₁
  rw [d₂.re_zeroSum] at hre₂
  rw [dp.re_zeroSum] at hrep
  rw [actualFourFactorLogDerivative, hb₁, hb₂, hbp, hre₁, hre₂, hrep]
  ring

/-- The existing Cauchy bound pays the complete three-factor remainder
from circle upper bounds and center lower bounds for the actual local factors. -/
theorem threeLocalRemainder_le_of_circleBounds
    (g₁ g₂ gp : ℂ → ℂ) (σ : ℂ)
    {r M₁ M₂ Mp m₁ m₂ mp : ℝ}
    (hr : 0 < r) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hMp : 0 ≤ Mp)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hmp : 0 < mp)
    (hg₁ : DiffContOnCl ℂ g₁ (ball σ r))
    (hg₂ : DiffContOnCl ℂ g₂ (ball σ r))
    (hgp : DiffContOnCl ℂ gp (ball σ r))
    (hcircle₁ : ∀ z ∈ sphere σ r, ‖g₁ z‖ ≤ M₁)
    (hcircle₂ : ∀ z ∈ sphere σ r, ‖g₂ z‖ ≤ M₂)
    (hcirclep : ∀ z ∈ sphere σ r, ‖gp z‖ ≤ Mp)
    (hlower₁ : m₁ ≤ ‖g₁ σ‖) (hlower₂ : m₂ ≤ ‖g₂ σ‖)
    (hlowerp : mp ≤ ‖gp σ‖) :
    -((logDeriv g₁ σ).re + (logDeriv g₂ σ).re + (logDeriv gp σ).re) ≤
      (M₁ / r) / m₁ + (M₂ / r) / m₂ + (Mp / r) / mp := by
  have h₁ := norm_logDeriv_le_of_circleBounds g₁ σ hr hM₁ hm₁ hg₁ hcircle₁ hlower₁
  have h₂ := norm_logDeriv_le_of_circleBounds g₂ σ hr hM₂ hm₂ hg₂ hcircle₂ hlower₂
  have hp := norm_logDeriv_le_of_circleBounds gp σ hr hMp hmp hgp hcirclep hlowerp
  have hre₁ : -(logDeriv g₁ σ).re ≤ ‖logDeriv g₁ σ‖ :=
    (neg_le_abs _).trans (abs_re_le_norm _)
  have hre₂ : -(logDeriv g₂ σ).re ≤ ‖logDeriv g₂ σ‖ :=
    (neg_le_abs _).trans (abs_re_le_norm _)
  have hrep : -(logDeriv gp σ).re ≤ ‖logDeriv gp σ‖ :=
    (neg_le_abs _).trans (abs_re_le_norm _)
  linarith

/-- Character-specific two-real-zero repulsion.  Its hypotheses are only actual
local disk data, the two selected disk zeros with multiplicity, the elementary
right-of-zero strip condition, and a directly checkable bound for the three
`g'/g` remainders; there is no abstract explicit-formula hypothesis. -/
theorem two_real_zeros_repel
    {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hpair : pairCharacter χ₁ χ₂ ≠ 1)
    (hsq₁ : χ₁ ^ 2 = 1) (hsq₂ : χ₂ ^ 2 = 1)
    {c : ℂ} {R : ℝ}
    (d₁ : CharacterLocalDiskData χ₁ c R)
    (d₂ : CharacterLocalDiskData χ₂ c R)
    (dp : CharacterLocalDiskData (pairCharacter χ₁ χ₂) c R)
    {σ β₁ β₂ E : ℝ}
    (hσ : 1 < σ) (hσdisk : (σ : ℂ) ∈ ball c R)
    (hβ₁ : (β₁ : ℂ) ∈ d₁.S) (hβ₂ : (β₂ : ℂ) ∈ d₂.S)
    (hmult₁ : 1 ≤ (d₁.D β₁).toNat) (hmult₂ : 1 ≤ (d₂.D β₂).toNat)
    (hβ₁σ : β₁ < σ) (hβ₂σ : β₂ < σ)
    (hstrip₁ : ∀ ρ ∈ d₁.S, ρ.re ≤ σ)
    (hstrip₂ : ∀ ρ ∈ d₂.S, ρ.re ≤ σ)
    (hstripp : ∀ ρ ∈ dp.S, ρ.re ≤ σ)
    (hremainder :
      -((logDeriv d₁.g σ).re + (logDeriv d₂.g σ).re +
        (logDeriv dp.g σ).re) ≤ E) :
    1 / (σ - β₁) + 1 / (σ - β₂) ≤
      (-deriv (L fun _ : ℕ ↦ (1 : ℂ)) (σ : ℂ) /
        L (fun _ : ℕ ↦ (1 : ℂ)) (σ : ℂ)).re +
      (conductorGammaTerm χ₁ σ).re + (conductorGammaTerm χ₂ σ).re +
      (conductorGammaTerm (pairCharacter χ₁ χ₂) σ).re + E := by
  have hid := actualFourFactor_localZeroIdentity χ₁ χ₂ hχ₁ hχ₂ hpair
    d₁ d₂ dp hσ hσdisk
  have hpos : 0 ≤ actualFourFactorLogDerivative χ₁ χ₂ σ := by
    rw [actualFourFactorLogDerivative,
      χ₁.deriv_LFunction_eq_deriv_LSeries (by simpa using hσ),
      χ₂.deriv_LFunction_eq_deriv_LSeries (by simpa using hσ),
      (pairCharacter χ₁ χ₂).deriv_LFunction_eq_deriv_LSeries (by simpa using hσ),
      χ₁.LFunction_eq_LSeries (by simpa using hσ),
      χ₂.LFunction_eq_LSeries (by simpa using hσ),
      (pairCharacter χ₁ χ₂).LFunction_eq_LSeries (by simpa using hσ)]
    exact fourFactor_negLogDerivative_nonneg χ₁ χ₂ hsq₁ hsq₂ σ hσ
  have h₁ := d₁.zeroKernel_le_zeroSum hβ₁ hmult₁ hstrip₁
  have h₂ := d₂.zeroKernel_le_zeroSum hβ₂ hmult₂ hstrip₂
  have hp := dp.zeroSum_nonneg hstripp
  rw [zeroKernel_ofReal hβ₁σ] at h₁
  rw [zeroKernel_ofReal hβ₂σ] at h₂
  rw [hid] at hpos
  linarith

end
end TatuzawaZeroContribution
end AnalyticNumberTheory.LargeSieve
