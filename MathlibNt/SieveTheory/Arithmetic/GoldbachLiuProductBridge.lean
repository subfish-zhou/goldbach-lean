import MathlibNt.SieveTheory.LiuSingularSeries
import MathlibNt.SieveTheory.MertensTheorem

/-!
# Exact Goldbach product bridge in Liu's normalization

The finite identity in `MertensTheorem.sieveProduct_identity` keeps the strict
prime cutoff and cancels precisely the factors at primes dividing `N`.  For
even `N`, removing the local factor at `2` gives twice Liu's odd-prime
truncation (Liu, `main.tex`, lines 98--102; see `LiuSingularSeries`).

We use this identity before estimating the prime product.  Multiplication by
the positive logarithm pays one denominator once, and the resulting two-sided
bound is shared by the `S1` lower and `B10` upper estimates.  No infinite-series
approximation is made here: each consumer separately controls the difference
between the actual finite truncation and the full Liu singular series.
-/

namespace MathlibNt.SieveTheory.GoldbachLiuProductBridge

/-- Exact finite product, including the factor at `2` and the strict cutoff. -/
theorem product_eq_two_mul_liuTruncated (N Z : ℕ) (hZ : 3 ≤ Z) (hEven : Even N) :
    MertensTheorem.goldbachSieveProduct N Z =
      2 * SingularSeries.liuSingularSeriesTruncated N (Z - 1) *
        MertensTheorem.primeProduct (Z - 1) := by
  rw [MertensTheorem.sieveProduct_identity N Z (by omega) hEven,
    SingularSeries.singularSeriesTruncated_eq_two_mul_liuSingularSeriesTruncated
      N (Z - 1) hEven (by omega)]
  ring

/-- Nonnegativity also holds below the analytic cutoff; evenness excludes `2`
from the nondivisor product. -/
theorem product_nonneg {N Z : ℕ} (hEven : Even N) :
    0 ≤ MertensTheorem.goldbachSieveProduct N Z := by
  unfold MertensTheorem.goldbachSieveProduct
  apply Finset.prod_nonneg
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨_, hpPrime, hpNotDvd⟩
  have hpNeTwo : p ≠ 2 := by
    intro hp2
    exact hpNotDvd (hp2 ▸ even_iff_two_dvd.mp hEven)
  have hp3 : 3 ≤ p := by
    have := hpPrime.two_le
    omega
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hden : 0 < (p : ℝ) - 1 := by linarith
  have hfrac : 1 / ((p : ℝ) - 1) ≤ 1 :=
    (div_le_iff₀ hden).2 (by linarith)
  exact sub_nonneg.mpr hfrac

/-- Mertens' frozen prime-product estimate, transferred through the exact
finite identity.  The same constant and both signs serve the two consumers;
the old quantitative domain `N ≥ 4`, even `N`, `Z ≥ 3` is retained. -/
theorem exists_log_bounds :
    ∃ C : ℝ, ∀ N Z : ℕ, 3 ≤ Z → Even N → 4 ≤ N →
      2 * SingularSeries.liuSingularSeriesTruncated N (Z - 1) *
          (Real.exp (-Real.eulerMascheroniConstant) -
            |C| / Real.log ((Z - 1 : ℕ) : ℝ)) ≤
        MertensTheorem.goldbachSieveProduct N Z * Real.log ((Z - 1 : ℕ) : ℝ) ∧
      MertensTheorem.goldbachSieveProduct N Z * Real.log ((Z - 1 : ℕ) : ℝ) ≤
        2 * SingularSeries.liuSingularSeriesTruncated N (Z - 1) *
          (Real.exp (-Real.eulerMascheroniConstant) +
            |C| / Real.log ((Z - 1 : ℕ) : ℝ)) := by
  obtain ⟨C, hC⟩ := MertensTheorem.mertens_product_formula
  refine ⟨C, fun N Z hZ hEven _hN4 => ?_⟩
  have hL : 0 < Real.log ((Z - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Z - 1 by omega))
  have hP := hC (Z - 1) (by omega)
  have hscaled := mul_le_mul_of_nonneg_right hP hL.le
  have hnormalized :
      |MertensTheorem.primeProduct (Z - 1) * Real.log ((Z - 1 : ℕ) : ℝ) -
          Real.exp (-Real.eulerMascheroniConstant)| ≤
        |C| / Real.log ((Z - 1 : ℕ) : ℝ) := by
    calc
      _ = |MertensTheorem.primeProduct (Z - 1) -
            Real.exp (-Real.eulerMascheroniConstant) / Real.log ((Z - 1 : ℕ) : ℝ)| *
          Real.log ((Z - 1 : ℕ) : ℝ) := by
        rw [show MertensTheorem.primeProduct (Z - 1) * Real.log ((Z - 1 : ℕ) : ℝ) -
            Real.exp (-Real.eulerMascheroniConstant) =
            (MertensTheorem.primeProduct (Z - 1) -
              Real.exp (-Real.eulerMascheroniConstant) / Real.log ((Z - 1 : ℕ) : ℝ)) *
                Real.log ((Z - 1 : ℕ) : ℝ) by field_simp]
        rw [abs_mul, abs_of_pos hL]
      _ ≤ C / Real.log ((Z - 1 : ℕ) : ℝ) ^ 2 *
          Real.log ((Z - 1 : ℕ) : ℝ) := hscaled
      _ = C / Real.log ((Z - 1 : ℕ) : ℝ) := by field_simp
      _ ≤ |C| / Real.log ((Z - 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right (le_abs_self C) hL.le
  have hS : 0 ≤ 2 * SingularSeries.liuSingularSeriesTruncated N (Z - 1) :=
    mul_nonneg (by norm_num) (SingularSeries.liuSingularSeriesTruncated_pos _ _).le
  have hlo := mul_le_mul_of_nonneg_left (abs_le.mp hnormalized).1 hS
  have hhi := mul_le_mul_of_nonneg_left (abs_le.mp hnormalized).2 hS
  rw [product_eq_two_mul_liuTruncated N Z hZ hEven]
  constructor <;> nlinarith only [hlo, hhi]

end MathlibNt.SieveTheory.GoldbachLiuProductBridge
