import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimePowerCharacters

open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace MathlibNt.SieveTheory

open Finset
open _root_.AnalyticNumberTheory.LargeSieve


/-- An induced character is its primitive character times the exact
coprimality indicator for the quotient of its level by its conductor. -/
theorem dirichletCharacter_eq_primitive_mul_coprimeIndicator {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    χ (n : ZMod q) =
      χ.primitiveCharacter (n : ZMod χ.conductor) *
        (if n.Coprime (q / χ.conductor) then 1 else 0) := by
  have hq : χ.conductor * (q / χ.conductor) = q :=
    Nat.mul_div_cancel' χ.conductor_dvd_level
  by_cases hd : n.Coprime χ.conductor
  · by_cases hr : n.Coprime (q / χ.conductor)
    · have hnq : n.Coprime q := by
        rw [← hq, Nat.coprime_mul_iff_right]
        exact ⟨hd, hr⟩
      rw [if_pos hr]
      simp only [mul_one]
      simpa using
        (χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ))
          (Nat.isCoprime_iff_coprime.mpr hnq)).symm
    · have hnq : ¬n.Coprime q := by
        rw [← hq, Nat.coprime_mul_iff_right]
        exact fun h => hr h.2
      rw [if_neg hr]
      simp only [mul_zero]
      exact MulChar.map_nonunit χ ((ZMod.isUnit_iff_coprime n q).not.mpr hnq)
  · have hnq : ¬n.Coprime q := by
      rw [← hq, Nat.coprime_mul_iff_right]
      exact fun h => hd h.1
    rw [MulChar.map_nonunit χ ((ZMod.isUnit_iff_coprime n q).not.mpr hnq)]
    rw [MulChar.map_nonunit χ.primitiveCharacter
      ((ZMod.isUnit_iff_coprime n χ.conductor).not.mpr hd)]
    simp


/-- A Dirichlet-character value has norm at most one, including at nonunits. -/
theorem dirichletCharacter_norm_le_one (q : ℕ)
    (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    ‖χ a‖ ≤ 1 := by
  exact AnalyticNumberTheory.LargeSieve.dirichletChar_norm_le_one q χ a


namespace LiuWeight

open AnalyticNumberTheory.Sieve


/-- For nonnegative logarithmic cutoff exponent, the Pan conductor range lies
inside the square-root range. -/
theorem panModulusCutoff_sq_le
    (N : ℕ) (B : ℝ) (hN : 3 ≤ N) (hB : 0 ≤ B) :
    panModulusCutoff N B ^ 2 ≤ N := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hlog : (1 : ℝ) ≤ Real.log N := by
    apply (Real.le_log_iff_exp_le hNpos).2
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hN)
  have hden : 1 ≤ Real.log N ^ B := Real.one_le_rpow hlog hB
  have hquot : (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B ≤
      (N : ℝ) ^ (1 / 2 : ℝ) :=
    div_le_self (Real.rpow_nonneg hNpos.le _) hden
  have hcut : (panModulusCutoff N B : ℝ) ≤
      (N : ℝ) ^ (1 / 2 : ℝ) :=
    (Nat.floor_le (by positivity)).trans hquot
  have hsqR : (panModulusCutoff N B : ℝ) ^ 2 ≤ (N : ℝ) := by
    calc
      (panModulusCutoff N B : ℝ) ^ 2 ≤
          ((N : ℝ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hcut 2
      _ = (N : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
        norm_num
  exact_mod_cast hsqR


end LiuWeight

end MathlibNt.SieveTheory
