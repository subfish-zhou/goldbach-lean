import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticValueAtOnePositive
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Data.Fintype.Order

/-!
# Removing finitely many conductors from a quadratic Siegel lower bound

This module isolates a quantifier bridge needed by a genuine Landau--Siegel
lower bound.  Strict positivity at each nonprincipal quadratic character makes
all conductors below a fixed threshold harmless: finiteness of the character
groups supplies one positive constant for those conductors.  Consequently it
is enough to prove the power lower bound uniformly for all sufficiently large
conductors.

No characters or conductors are enumerated in this argument.
-/

open Complex

namespace DirichletCharacter

/-- At one fixed nonzero conductor, positivity of quadratic nonprincipal
`L(1, χ)` can be made uniform over all characters. -/
theorem exists_fixed_conductor_quadratic_LFunction_one_lower
    (q : ℕ) [NeZero q] (η : ℝ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
          c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re := by
  classical
  let ratio : DirichletCharacter ℂ q → ℝ := fun χ =>
    if χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 then
      (q : ℝ) ^ (-η) / (χ.LFunction 1).re
    else 0
  obtain ⟨M, hM⟩ := Finite.exists_le ratio
  let B : ℝ := max 0 M
  let c : ℝ := 1 / (B + 1)
  have hB0 : 0 ≤ B := le_max_left 0 M
  have hden : 0 < B + 1 := by linarith
  refine ⟨c, one_div_pos.mpr hden, ?_⟩
  intro χ hprimitive hquad hnonprincipal
  have hL : 0 < (χ.LFunction 1).re :=
    LFunction_apply_one_re_pos_of_sq_eq_one hquad hnonprincipal
  have hratio : (q : ℝ) ^ (-η) / (χ.LFunction 1).re ≤ B := by
    calc
      (q : ℝ) ^ (-η) / (χ.LFunction 1).re = ratio χ := by
        simp [ratio, hprimitive, hquad, hnonprincipal]
      _ ≤ M := hM χ
      _ ≤ B := le_max_right 0 M
  have hpow_le : (q : ℝ) ^ (-η) ≤ B * (χ.LFunction 1).re :=
    (div_le_iff₀ hL).mp hratio
  have hpow_le' : (q : ℝ) ^ (-η) ≤ (B + 1) * (χ.LFunction 1).re := by
    nlinarith
  change (1 / (B + 1)) * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re
  rw [one_div, inv_mul_eq_div]
  exact (div_le_iff₀ hden).mpr (by simpa [mul_comm] using hpow_le')

/-- All nonzero conductors below a fixed threshold have one uniform positive
quadratic `L(1, χ)` power lower constant. -/
theorem exists_below_conductor_quadratic_LFunction_one_lower
    (Q : ℕ) (η : ℝ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        q < Q → χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
          c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re := by
  induction Q with
  | zero =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro q _ χ hq
      exact (Nat.not_lt_zero q hq).elim
  | succ Q ih =>
      obtain ⟨c₀, hc₀, h₀⟩ := ih
      by_cases hQ : Q = 0
      · subst Q
        refine ⟨c₀, hc₀, ?_⟩
        intro q _ χ hq
        have : q = 0 := Nat.lt_one_iff.mp hq
        exact (NeZero.ne q this).elim
      · let _ : NeZero Q := ⟨hQ⟩
        obtain ⟨c₁, hc₁, h₁⟩ :=
          exists_fixed_conductor_quadratic_LFunction_one_lower Q η
        refine ⟨min c₀ c₁, lt_min hc₀ hc₁, ?_⟩
        intro q _ χ hq hprimitive hquad hnonprincipal
        rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hlt | rfl
        · exact (mul_le_mul_of_nonneg_right (min_le_left c₀ c₁)
              (Real.rpow_nonneg (Nat.cast_nonneg q) (-η))).trans
            (h₀ q χ hlt hprimitive hquad hnonprincipal)
        · exact (mul_le_mul_of_nonneg_right (min_le_right c₀ c₁)
              (Real.rpow_nonneg (Nat.cast_nonneg q) (-η))).trans
            (h₁ χ hprimitive hquad hnonprincipal)

/-- **Finite-exception bridge for the quadratic Landau--Siegel lower bound.**
A uniform power lower bound beyond an arbitrary fixed conductor threshold
extends to every conductor.  The small-conductor constant is obtained from the
actual finite character groups and strict positivity, rather than from a
finite scan or a supplied small-conductor predicate. -/
theorem exists_quadratic_LFunction_one_lower_of_eventual
    (η : ℝ) (_hη : 0 < η)
    (hlarge : ∃ (Q : ℕ) (c : ℝ), 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        Q ≤ q → χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
          c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
          c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re := by
  obtain ⟨Q, cLarge, hcLarge, hLarge⟩ := hlarge
  obtain ⟨c₀, hc₀, h₀⟩ :=
    exists_below_conductor_quadratic_LFunction_one_lower Q η
  refine ⟨min c₀ cLarge, lt_min hc₀ hcLarge, ?_⟩
  intro q _ χ hprimitive hquad hnonprincipal
  by_cases hq : q < Q
  · exact (mul_le_mul_of_nonneg_right (min_le_left c₀ cLarge)
        (Real.rpow_nonneg (Nat.cast_nonneg q) (-η))).trans
      (h₀ q χ hq hprimitive hquad hnonprincipal)
  · exact (mul_le_mul_of_nonneg_right (min_le_right c₀ cLarge)
        (Real.rpow_nonneg (Nat.cast_nonneg q) (-η))).trans
      (hLarge q χ (Nat.le_of_not_gt hq) hprimitive hquad hnonprincipal)

/-- Quantifier-level reduction of the full Landau--Siegel lower bound: it is
enough to establish each exponent uniformly beyond some conductor threshold.
All finite exceptions are discharged unconditionally by the preceding theorem. -/
theorem quadratic_LFunction_one_lower_of_eventual_forall_exponents
    (hlarge : ∀ η : ℝ, 0 < η →
      ∃ (Q : ℕ) (c : ℝ), 0 < c ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          Q ≤ q → χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
            c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re) :
    ∀ η : ℝ, 0 < η →
      ∃ c : ℝ, 0 < c ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
            c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re := by
  intro η hη
  exact exists_quadratic_LFunction_one_lower_of_eventual η hη (hlarge η hη)

end DirichletCharacter
