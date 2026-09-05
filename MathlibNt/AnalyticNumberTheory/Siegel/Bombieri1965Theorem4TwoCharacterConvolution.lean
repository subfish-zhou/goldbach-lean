import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The genuine two-character convolution

This is a modern arithmetic proof of positivity for the coefficients of
`ζ(s) L(s, χ) L(s, ψ) L(s, χψ)`.  Both characters have a common arbitrary
modulus.  No primitivity or coprimality of conductors is used.

The local argument regroups the four actual factors using a character twist
of `χ.zetaMul`.  The exceptional local case, where both character values are
`-1`, is controlled by the alternating geometric sum.  These are identities
of the actual coefficients, not estimates by a positive majorant.
-/

open Complex Finset
open ArithmeticFunction hiding log
open scoped BigOperators ComplexOrder

namespace DirichletCharacter

variable {q : ℕ}

/-- The actual arithmetic convolution with Dirichlet series
`ζ(s) L(s, χ) L(s, ψ) L(s, χψ)`. -/
noncomputable def twoCharacterConvolution
    (χ ψ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  χ.zetaMul * toArithmeticFunction (ψ ·) * toArithmeticFunction ((χ * ψ) ·)

/-- Multiplicativity is inherited from the four genuine factors. -/
theorem isMultiplicative_twoCharacterConvolution
    (χ ψ : DirichletCharacter ℂ q) :
    (twoCharacterConvolution χ ψ).IsMultiplicative :=
  (χ.isMultiplicative_zetaMul.mul (isMultiplicative_toArithmeticFunction ψ)).mul
    (isMultiplicative_toArithmeticFunction (χ * ψ))

/-- Normalization of the fourfold convolution. -/
theorem twoCharacterConvolution_one (χ ψ : DirichletCharacter ℂ q) :
    twoCharacterConvolution χ ψ 1 = 1 :=
  (isMultiplicative_twoCharacterConvolution χ ψ).map_one

/-- Exchanging the two characters leaves the actual convolution unchanged. -/
theorem twoCharacterConvolution_comm (χ ψ : DirichletCharacter ℂ q) :
    twoCharacterConvolution χ ψ = twoCharacterConvolution ψ χ := by
  unfold twoCharacterConvolution zetaMul
  rw [mul_comm ψ χ]
  ac_rfl

/-- The convolution of `ψ` and `χψ` is the pointwise `ψ`-twist of `ζ * χ`. -/
theorem character_mul_product_apply
    (χ ψ : DirichletCharacter ℂ q) (n : ℕ) :
    (toArithmeticFunction (ψ ·) * toArithmeticFunction ((χ * ψ) ·)) n =
      ψ n * χ.zetaMul n := by
  rw [zetaMul, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hxprod := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hn := (Nat.mem_divisorsAntidiagonal.mp hx).2
  have hx1 : x.1 ≠ 0 := by
    intro h
    simp [h] at hxprod
    exact hn hxprod.symm
  have hx2 : x.2 ≠ 0 := by
    intro h
    simp [h] at hxprod
    exact hn hxprod.symm
  simp only [toArithmeticFunction, coe_mk, hx1, hx2, ↓reduceIte,
    natCoe_apply, zeta_apply_ne hx1, Nat.cast_one, one_mul, MulChar.mul_apply]
  rw [← hxprod, Nat.cast_mul, map_mul]
  ring

/-- An exact divisor-antidiagonal formula obtained by twisting one pair of factors. -/
theorem twoCharacterConvolution_apply
    (χ ψ : DirichletCharacter ℂ q) (n : ℕ) :
    twoCharacterConvolution χ ψ n =
      ∑ x ∈ n.divisorsAntidiagonal, χ.zetaMul x.1 * (ψ x.2 * χ.zetaMul x.2) := by
  rw [twoCharacterConvolution, mul_assoc, ArithmeticFunction.mul_apply]
  simp_rw [character_mul_product_apply]

private lemma twist_zetaMul_prime_pow_nonneg
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1)
    {p : ℕ} (hψp : 0 ≤ ψ p) (k : ℕ) :
    0 ≤ ψ (p ^ k : ℕ) * χ.zetaMul (p ^ k) := by
  rw [Nat.cast_pow, map_pow]
  exact mul_nonneg (pow_nonneg hψp _) (zetaMul_nonneg hχ _)

set_option backward.isDefEq.respectTransparency.types false in
private lemma twist_zetaMul_prime_pow_nonneg_of_neg_one
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime) (hχp : χ p = -1) (hψp : ψ p = -1)
    (k : ℕ) :
    0 ≤ ψ (p ^ k : ℕ) * χ.zetaMul (p ^ k) := by
  rw [Nat.cast_pow, map_pow, hψp]
  by_cases hk : _root_.Even k
  · rw [hk.neg_one_pow, one_mul]
    exact zetaMul_nonneg hχ _
  · have hk' : _root_.Even (k + 1) := (Nat.not_even_iff_odd.mp hk).add_odd odd_one
    have hz : χ.zetaMul (p ^ k) = 0 := by
      simp only [zetaMul, toArithmeticFunction, coe_zeta_mul_apply, coe_mk,
        Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq,
        false_and, ↓reduceIte, Nat.cast_pow, map_pow, hχp, neg_one_geom_sum,
        if_pos hk']
    rw [hz, mul_zero]

private lemma twoCharacterConvolution_prime_pow_nonneg_of_twist
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime)
    (htwist : ∀ k, 0 ≤ ψ (p ^ k : ℕ) * χ.zetaMul (p ^ k)) (k : ℕ) :
    0 ≤ twoCharacterConvolution χ ψ (p ^ k) := by
  rw [twoCharacterConvolution, mul_assoc, ArithmeticFunction.mul_apply]
  apply Finset.sum_nonneg
  intro x hx
  rw [character_mul_product_apply]
  apply mul_nonneg (zetaMul_nonneg hχ _)
  have hxdvd : x.2 ∣ p ^ k :=
    Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp hxdvd
  rw [hj]
  exact htwist j

/-- Positivity at every prime power, by structural casework on the two local
quadratic character values. -/
theorem twoCharacterConvolution_prime_pow_nonneg
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ twoCharacterConvolution χ ψ (p ^ k) := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with hχp | hχp | hχp
  · rw [twoCharacterConvolution_comm]
    exact twoCharacterConvolution_prime_pow_nonneg_of_twist hψ hp
      (twist_zetaMul_prime_pow_nonneg hψ (by simp [hχp])) k
  · rw [twoCharacterConvolution_comm]
    exact twoCharacterConvolution_prime_pow_nonneg_of_twist hψ hp
      (twist_zetaMul_prime_pow_nonneg hψ (by simp [hχp])) k
  · apply twoCharacterConvolution_prime_pow_nonneg_of_twist hχ hp
    intro j
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hψ p with hψp | hψp | hψp
    · exact twist_zetaMul_prime_pow_nonneg hχ (by simp [hψp]) j
    · exact twist_zetaMul_prime_pow_nonneg hχ (by simp [hψp]) j
    · exact twist_zetaMul_prime_pow_nonneg_of_neg_one hχ hp hχp hψp j

/-- Every coefficient is a nonnegative real number, expressed in the real-axis
order on `ℂ`. -/
theorem twoCharacterConvolution_nonneg
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (n : ℕ) :
    0 ≤ twoCharacterConvolution χ ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simpa only [(isMultiplicative_twoCharacterConvolution χ ψ).multiplicative_factorization
        _ hn] using!
      Finset.prod_nonneg fun p hp =>
        twoCharacterConvolution_prime_pow_nonneg hχ hψ
          (Nat.prime_of_mem_primeFactors hp) _

/-- The imaginary part vanishes; positivity is not merely a bound on the real part. -/
theorem twoCharacterConvolution_im_eq_zero
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (n : ℕ) :
    (twoCharacterConvolution χ ψ n).im = 0 := by
  have h := twoCharacterConvolution_nonneg hχ hψ n
  rw [RCLike.le_iff_re_im] at h
  exact h.2.symm

/-- The real part of every coefficient is nonnegative. -/
theorem twoCharacterConvolution_re_nonneg
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (n : ℕ) :
    0 ≤ (twoCharacterConvolution χ ψ n).re := by
  have h := twoCharacterConvolution_nonneg hχ hψ n
  rw [RCLike.le_iff_re_im] at h
  exact h.1

private lemma characterArithmeticFunction_LSeriesSummable
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (toArithmeticFunction (χ ·)) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
  intro n hn
  simpa only [toArithmeticFunction, coe_mk, hn, ↓reduceIte] using norm_le_one χ n

/-- Absolute convergence of the genuine fourfold convolution on `Re s > 1`;
quadraticity is not needed for convergence. -/
theorem LSeriesSummable_twoCharacterConvolution
    (χ ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (twoCharacterConvolution χ ψ) s :=
  ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul (χ.LSeriesSummable_zetaMul hs)
      (characterArithmeticFunction_LSeriesSummable ψ hs))
    (characterArithmeticFunction_LSeriesSummable (χ * ψ) hs)

private lemma characterArithmeticFunction_LSeries
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    LSeries (toArithmeticFunction (χ ·)) s = LSeries (fun n : ℕ => χ n) s :=
  LSeries_congr (fun hn => (χ.apply_eq_toArithmeticFunction_apply hn).symm) s

/-- The actual Dirichlet-series product identity, valid even at modulus zero.
The character series here are the raw, absolutely convergent Dirichlet series. -/
theorem LSeries_twoCharacterConvolution
    (χ ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (twoCharacterConvolution χ ψ) s =
      riemannZeta s * LSeries (fun n : ℕ => χ n) s *
        LSeries (fun n : ℕ => ψ n) s * LSeries (fun n : ℕ => (χ * ψ) n) s := by
  have hχ := characterArithmeticFunction_LSeriesSummable χ hs
  have hψ := characterArithmeticFunction_LSeriesSummable ψ hs
  have hχψ := characterArithmeticFunction_LSeriesSummable (χ * ψ) hs
  have hζχ := χ.LSeriesSummable_zetaMul hs
  have hζ : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s :=
    LSeriesSummable_zeta_iff.mpr hs
  have hζvalue : LSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s =
      riemannZeta s := LSeries_zeta_eq_riemannZeta hs
  have hζχvalue : LSeries χ.zetaMul s =
      riemannZeta s * LSeries (fun n : ℕ => χ n) s :=
    (ArithmeticFunction.LSeries_mul' hζ hχ).trans
      (congrArg₂ (· * ·) hζvalue (characterArithmeticFunction_LSeries χ s))
  have hpair : LSeries (χ.zetaMul * toArithmeticFunction (ψ ·) : ArithmeticFunction ℂ) s =
      riemannZeta s * LSeries (fun n : ℕ => χ n) s *
        LSeries (fun n : ℕ => ψ n) s :=
    (ArithmeticFunction.LSeries_mul' hζχ hψ).trans
      (congrArg₂ (· * ·) hζχvalue (characterArithmeticFunction_LSeries ψ s))
  exact (ArithmeticFunction.LSeries_mul'
    (ArithmeticFunction.LSeriesSummable_mul hζχ hψ) hχψ).trans
      (congrArg₂ (· * ·) hpair (characterArithmeticFunction_LSeries (χ * ψ) s))

/-- The analytic product of the Riemann zeta function and the three Dirichlet
L-functions is represented by the genuine convolution on `Re s > 1`. -/
theorem LSeries_twoCharacterConvolution_eq_LFunction_product
    [NeZero q] (χ ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (twoCharacterConvolution χ ψ) s =
      riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ * ψ).LFunction s := by
  rw [LSeries_twoCharacterConvolution χ ψ hs, χ.LFunction_eq_LSeries hs,
    ψ.LFunction_eq_LSeries hs, (χ * ψ).LFunction_eq_LSeries hs]

/-- Absolute convergence and the actual analytic value, in one `HasSum` statement. -/
theorem LSeriesHasSum_twoCharacterConvolution
    [NeZero q] (χ ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (twoCharacterConvolution χ ψ) s
      (riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ * ψ).LFunction s) :=
  LSeriesHasSum_iff.mpr ⟨LSeriesSummable_twoCharacterConvolution χ ψ hs,
    LSeries_twoCharacterConvolution_eq_LFunction_product χ ψ hs⟩

end DirichletCharacter
