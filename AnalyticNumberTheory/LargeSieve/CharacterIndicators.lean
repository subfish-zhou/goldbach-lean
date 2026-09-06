import AnalyticNumberTheory.LargeSieve.Multiplicative
import Mathlib.Tactic

/-! # AnalyticNumberTheory.LargeSieve.CharacterIndicators

## Dirichlet-character expansion of an arithmetic-progression indicator

For units `n, l` modulo `q`, the indicator `1_{n ≡ l [MOD q]}` has the
Dirichlet-character expansion

  Σ_{χ mod q} χ(n)·conj(χ(l)) = φ(q)·1_{n ≡ l [MOD q]}.

This is the standard step in Pan's proof that converts congruence counts to
means of character sums (Liu 2022 §II; Halberstam--Richert Ch. 10).
It connects the Parseval/orthogonality arguments for Type I/II bounds to
arithmetic-progression counts. This module assembles
the pointwise character orthogonality `charOrthSum` from `Multiplicative.lean`
and translates equality in `ZMod` into congruence of natural numbers using
`ZMod.natCast_eq_natCast_iff`.

Main results:
  * `charOrthSum_unit`: the orthogonality sum on units `a b : ZMod q` is
    `if a = b then φ(q) else 0`;
  * `charIndicator_zmod`: the indicator form on `ZMod`,
    `Σ_χ χ(a)·star(χ(b)) = φ(q)·1_{a=b}`;
  * `charIndicator`: the natural-number congruence form,
    `Σ_χ χ(n)·star(χ(l)) = if n ≡ l [MOD q] then φ(q) else 0`;
  * `charIndicator_mul`: the multiplicative indicator form `φ(q)·1_{n≡l}`;
  * `charIndicator_ap`: the normalized pointwise expansion
    `1_{n≡l} = φ(q)⁻¹·Σ_χ χ(n)·star(χ(l))`;
  * `charSum_ap`: arithmetic-progression sums as character sums, the
    Parseval interface for Type I/II estimates:
    `Σ_{n≤N, n≡l [MOD q]} a_n = φ(q)⁻¹·Σ_χ star(χ(l))·Σ_{n≤N} a_n·χ(n)`.

References: Liu, "On the weighted Pan theorem" (2022) §II--§III;
Halberstam--Richert, "Sieve Methods" (1974) Ch. 10; Montgomery (1971) Ch. 1.
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

noncomputable section

/-! ## 1. Orthogonality sums on units of ZMod: indicator form -/

/-- The character orthogonality sum on units is `if a = b then φ(q) else 0`
(ZMod form). Under `ha hb`, the three conditions in `charOrthSum`
(unit, unit, and equality) reduce to `a = b`. -/
theorem charOrthSum_unit {q : ℕ} (hq : 0 < q) {a b : ZMod q} (ha : IsUnit a) (hb : IsUnit b) :
    (∑ χ : DirichletCharacter ℂ q, χ a * star (χ b)) =
      if a = b then (Nat.totient q : ℂ) else 0 := by
  simpa only [ha, hb, true_and] using charOrthSum hq a b

/-- **Indicator form (ZMod)**: for units `a b`,
  `Σ_χ χ(a)·star(χ(b)) = φ(q)·1_{a=b}`. -/
theorem charIndicator_zmod {q : ℕ} (hq : 0 < q) {a b : ZMod q} (ha : IsUnit a) (hb : IsUnit b) :
    (∑ χ : DirichletCharacter ℂ q, χ a * star (χ b)) =
      (Nat.totient q : ℂ) * (if a = b then 1 else 0) := by
  rw [charOrthSum_unit hq ha hb]
  by_cases hab : a = b <;> simp [hab]

/-! ## 2. Natural-number congruence form -/

/-- **Character expansion of an arithmetic-progression indicator
(natural-number form)**: for units `n, l`,
  `Σ_χ χ(n)·star(χ(l)) = if n ≡ l [MOD q] then φ(q) else 0`.
Equality in `ZMod` is equivalent to congruence modulo `q`
(`ZMod.natCast_eq_natCast_iff`). -/
theorem charIndicator {q : ℕ} (hq : 0 < q) {n l : ℕ} (hn : IsUnit (n : ZMod q)) (hl : IsUnit (l : ZMod q)) :
    (∑ χ : DirichletCharacter ℂ q, χ (n : ZMod q) * star (χ (l : ZMod q))) =
      if n ≡ l [MOD q] then (Nat.totient q : ℂ) else 0 := by
  simpa only [ZMod.natCast_eq_natCast_iff] using charOrthSum_unit hq hn hl

/-- Multiplicative indicator form:
`Σ_χ χ(n)·star(χ(l)) = φ(q)·1_{n≡l}`. -/
theorem charIndicator_mul {q : ℕ} (hq : 0 < q) {n l : ℕ} (hn : IsUnit (n : ZMod q)) (hl : IsUnit (l : ZMod q)) :
    (∑ χ : DirichletCharacter ℂ q, χ (n : ZMod q) * star (χ (l : ZMod q))) =
      (Nat.totient q : ℂ) * (if n ≡ l [MOD q] then 1 else 0) := by
  rw [charIndicator hq hn hl]
  by_cases hmod : n ≡ l [MOD q] <;> simp [hmod]

/-! ## 3. Normalized pointwise expansion and arithmetic-progression sums -/

/-- **Normalized pointwise expansion**: for a unit `l` and any `n : ℕ`,
  `1_{n≡l} = φ(q)⁻¹·Σ_χ χ(n)·star(χ(l))`.
If `n` is not a unit, `χ(n) = 0` makes the right-hand side zero; if
`n ≡ l`, then `n` is automatically a unit. -/
theorem charIndicator_ap {q : ℕ} (hq : 0 < q) {l : ℕ} (hl : IsUnit (l : ZMod q)) (n : ℕ) :
    (if n ≡ l [MOD q] then (1 : ℂ) else 0) =
      (Nat.totient q : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        χ (n : ZMod q) * star (χ (l : ZMod q)) := by
  rw [charOrthSum hq]
  by_cases hmod : n ≡ l [MOD q]
  · have heq : (n : ZMod q) = (l : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff n l q).mpr hmod
    -- Congruence to the unit l supplies the remaining unit condition.
    have hn : IsUnit (n : ZMod q) := by simpa [heq] using hl
    have hφ : (Nat.totient q : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr hq).ne'
    rw [if_pos hmod, if_pos ⟨hn, hl, heq⟩]
    exact (inv_mul_cancel₀ hφ).symm
  · -- Away from the progression, orthogonality vanishes whether n is a unit or not.
    have hne : (n : ZMod q) ≠ (l : ZMod q) :=
      fun heq => hmod ((ZMod.natCast_eq_natCast_iff n l q).mp heq)
    simp [hmod, hne]

/-- **Arithmetic-progression sums as character sums** (the Parseval
interface for Type I/II estimates): for a unit `l`,
  `Σ_{n≤N, n≡l [MOD q]} a_n = φ(q)⁻¹·Σ_χ star(χ(l))·Σ_{n≤N} a_n·χ(n)`. -/
theorem charSum_ap {q : ℕ} (hq : 0 < q) {l : ℕ} (hl : IsUnit (l : ZMod q)) (a : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), a n * if n ≡ l [MOD q] then 1 else 0) =
      (Nat.totient q : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        star (χ (l : ZMod q)) * ∑ n ∈ Finset.range (N + 1), a n * χ (n : ZMod q) := by
  calc
    (∑ n ∈ Finset.range (N + 1), a n * if n ≡ l [MOD q] then 1 else 0)
        = ∑ n ∈ Finset.range (N + 1),
            a n * ((Nat.totient q : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
              χ (n : ZMod q) * star (χ (l : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [charIndicator_ap hq hl n]
    _ = (Nat.totient q : ℂ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
          a n * ∑ χ : DirichletCharacter ℂ q, χ (n : ZMod q) * star (χ (l : ZMod q)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = (Nat.totient q : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          star (χ (l : ZMod q)) * ∑ n ∈ Finset.range (N + 1), a n * χ (n : ZMod q) := by
      congr 1
      calc
        ∑ n ∈ Finset.range (N + 1),
            a n * ∑ χ : DirichletCharacter ℂ q, χ (n : ZMod q) * star (χ (l : ZMod q))
            = ∑ n ∈ Finset.range (N + 1), ∑ χ : DirichletCharacter ℂ q,
                a n * (χ (n : ZMod q) * star (χ (l : ZMod q))) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.mul_sum]
        _ = ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.range (N + 1),
              a n * (χ (n : ZMod q) * star (χ (l : ZMod q))) := by
          rw [Finset.sum_comm]
        _ = ∑ χ : DirichletCharacter ℂ q,
              star (χ (l : ZMod q)) * ∑ n ∈ Finset.range (N + 1), a n * χ (n : ZMod q) := by
          apply Finset.sum_congr rfl
          intro χ hχ
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          ring

end

end AnalyticNumberTheory.LargeSieve
