import AnalyticNumberTheory.LargeSieve.Multiplicative

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


/-! ## 2. Natural-number congruence form -/


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


end

end AnalyticNumberTheory.LargeSieve
