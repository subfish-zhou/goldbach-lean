import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticPolyaVinogradovExplicit
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The nonnegative quadratic convolution in Siegel's elementary argument

For a quadratic character `χ`, this file packages the coefficients of
`ζ(s) L(s, χ)` as the real divisor sum

`aχ(n) = ∑ d ∣ n, Re χ(d)`.

The coefficients are nonnegative, and every nonzero square contributes at
least one.  Consequently their summatory function is at least `⌊√X⌋`.  The
last theorem combines this arithmetic lower bound with the explicit
Pólya--Vinogradov harmonic tail.  Its remaining discrepancy is kept as an
explicit term; no unproved upper estimate for that term is assumed.
-/

open Complex Finset
open ArithmeticFunction hiding log
open scoped BigOperators ComplexOrder Real

namespace DirichletCharacter

variable {q : ℕ}

/-- The real coefficient of `ζ(s) L(s, χ)`. -/
noncomputable def quadraticSiegelConvolution
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  (χ.zetaMul n).re

/-- The convolution coefficient is literally the real quadratic divisor sum. -/
theorem quadraticSiegelConvolution_eq_divisorSum
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    quadraticSiegelConvolution χ n = ∑ d ∈ n.divisors, (χ d).re := by
  rw [quadraticSiegelConvolution, zetaMul, coe_zeta_mul_apply]
  calc
    (∑ d ∈ n.divisors, (toArithmeticFunction fun x => χ x) d).re =
        (∑ d ∈ n.divisors, χ d).re := by
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
      simp [toArithmeticFunction, hd0]
    _ = ∑ d ∈ n.divisors, (χ d).re := by
      induction n.divisors using Finset.induction_on with
      | empty => simp
      | @insert d s hd ih => simp [hd, ih]

/-- The complex convolution coefficient lies on the real axis. -/
theorem zetaMul_im_eq_zero_of_sq_eq_one
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (n : ℕ) :
    (χ.zetaMul n).im = 0 := by
  have h := zetaMul_nonneg hquad n
  rw [RCLike.le_iff_re_im] at h
  simpa using h.2.symm

/-- Quadratic convolution coefficients are nonnegative real numbers. -/
theorem quadraticSiegelConvolution_nonneg
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ quadraticSiegelConvolution χ n := by
  have h := zetaMul_nonneg hquad n
  rw [RCLike.le_iff_re_im] at h
  exact h.1

set_option backward.isDefEq.respectTransparency.types false in
/-- At every even prime-power exponent the quadratic Euler coefficient is at
least one. -/
lemma one_le_zetaMul_prime_even_pow
    {χ : DirichletCharacter ℂ q} (hquad : χ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (1 : ℂ) ≤ χ.zetaMul (p ^ (2 * k)) := by
  simp only [zetaMul, toArithmeticFunction, coe_zeta_mul_apply, coe_mk,
    Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq,
    false_and, ↓reduceIte, Nat.cast_pow, map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hquad p with h | h | h
  · simp [h]
  · simp [h]
    positivity
  · simp [h, neg_one_geom_sum]

/-- Every nonzero square has quadratic convolution coefficient at least one. -/
theorem one_le_quadraticSiegelConvolution_sq
    {χ : DirichletCharacter ℂ q} (hquad : χ ^ 2 = 1)
    {m : ℕ} (hm : m ≠ 0) :
    1 ≤ quadraticSiegelConvolution χ (m ^ 2) := by
  have hfac := χ.isMultiplicative_zetaMul.multiplicative_factorization χ.zetaMul
    (pow_ne_zero 2 hm)
  have hcomplex : (1 : ℂ) ≤ χ.zetaMul (m ^ 2) := by
    rw [hfac]
    change (1 : ℂ) ≤ ∏ p ∈ (m ^ 2).factorization.support,
      χ.zetaMul (p ^ ((m ^ 2).factorization p))
    apply Finset.one_le_prod
    intro p hp
    simpa [Nat.factorization_pow] using
      (one_le_zetaMul_prime_even_pow hquad
        (Nat.prime_of_mem_primeFactors (by simpa using hp))
        (m.factorization p))
  rw [RCLike.le_iff_re_im] at hcomplex
  exact hcomplex.1

/-- The summatory quadratic convolution up to `X`. -/
noncomputable def quadraticSiegelConvolutionSummatory
    (χ : DirichletCharacter ℂ q) (X : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 X, quadraticSiegelConvolution χ n

/-- Dirichlet-convolution / divisor-double-sum identity. -/
theorem quadraticSiegelConvolutionSummatory_eq_divisorDoubleSum
    (χ : DirichletCharacter ℂ q) (X : ℕ) :
    quadraticSiegelConvolutionSummatory χ X =
      ∑ n ∈ Icc 1 X, ∑ d ∈ n.divisors, (χ d).re := by
  unfold quadraticSiegelConvolutionSummatory
  apply Finset.sum_congr rfl
  intro n hn
  exact quadraticSiegelConvolution_eq_divisorSum χ n

/-- Siegel's square lower-bound chain:
`⌊√X⌋ ≤ ∑_{1 ≤ n ≤ X} aχ(n)`. -/
theorem sqrt_le_quadraticSiegelConvolutionSummatory
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (X : ℕ) :
    (X.sqrt : ℝ) ≤ quadraticSiegelConvolutionSummatory χ X := by
  let S : Finset ℕ := (Icc 1 X.sqrt).image (fun m => m ^ 2)
  have hsub : S ⊆ Icc 1 X := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
    rw [Finset.mem_Icc] at hm ⊢
    constructor
    · nlinarith
    · have hsquare : m * m ≤ X := Nat.le_sqrt.mp hm.2
      simpa [pow_two] using hsquare
  have hsmall :
      (∑ n ∈ S, quadraticSiegelConvolution χ n) ≤
        ∑ n ∈ Icc 1 X, quadraticSiegelConvolution χ n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn hnS
    exact quadraticSiegelConvolution_nonneg χ hquad n
  have himage :
      (∑ n ∈ S, quadraticSiegelConvolution χ n) =
        ∑ m ∈ Icc 1 X.sqrt, quadraticSiegelConvolution χ (m ^ 2) := by
    exact Finset.sum_image (s := Icc 1 X.sqrt)
      (f := quadraticSiegelConvolution χ)
      (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)).injOn
  have hlower :
      (X.sqrt : ℝ) ≤
        ∑ m ∈ Icc 1 X.sqrt, quadraticSiegelConvolution χ (m ^ 2) := by
    calc
      (X.sqrt : ℝ) = ∑ m ∈ Icc 1 X.sqrt, (1 : ℝ) := by simp
      _ ≤ ∑ m ∈ Icc 1 X.sqrt, quadraticSiegelConvolution χ (m ^ 2) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_Icc] at hm
        exact one_le_quadraticSiegelConvolution_sq hquad (Nat.ne_of_gt hm.1)
  rw [quadraticSiegelConvolutionSummatory]
  rw [himage] at hsmall
  exact hlower.trans hsmall

/-- The exact residual between the convolution summatory function and `X`
times the finite harmonic truncation.  Later hyperbola estimates should bound
this quantity rather than postulate an unknown error bound. -/
noncomputable def quadraticSiegelConvolutionDiscrepancy
    (χ : DirichletCharacter ℂ q) (X m : ℕ) : ℝ :=
  quadraticSiegelConvolutionSummatory χ X -
    (X : ℝ) * quadraticHarmonicTruncation χ m

/-- Expansion of the residual as the divisor double sum minus the harmonic
main term. -/
theorem quadraticSiegelConvolutionDiscrepancy_eq_divisorDoubleSum_sub
    (χ : DirichletCharacter ℂ q) (X m : ℕ) :
    quadraticSiegelConvolutionDiscrepancy χ X m =
      (∑ n ∈ Icc 1 X, ∑ d ∈ n.divisors, (χ d).re) -
        (X : ℝ) * quadraticHarmonicTruncation χ m := by
  rw [quadraticSiegelConvolutionDiscrepancy,
    quadraticSiegelConvolutionSummatory_eq_divisorDoubleSum]

/-- The first load-bearing inequality in the elementary convolution route.
The square lower bound and the explicit Pólya--Vinogradov tail force a lower
bound for `X * Re L(1,χ)` up to the exact convolution discrepancy. -/
theorem sqrt_sub_convolutionDiscrepancy_sub_polyaVinogradovError_le
    [NeZero q] {χ : DirichletCharacter ℂ q} (hprimitive : χ.IsPrimitive)
    (hquad : χ ^ 2 = 1) (hnonprincipal : χ ≠ 1) (hq : 1 < q)
    (X : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    (X.sqrt : ℝ) - quadraticSiegelConvolutionDiscrepancy χ X m -
        (X : ℝ) * (8 * Real.sqrt q * (1 + Real.log q) / (m : ℝ)) ≤
      (X : ℝ) * (χ.LFunction 1).re := by
  have hlower := sqrt_le_quadraticSiegelConvolutionSummatory χ hquad X
  have htail :=
    hprimitive.abs_LFunction_one_re_sub_quadraticHarmonicTruncation_le_eight_mul_sqrt_q_mul_one_add_log_div
      hnonprincipal hq hm
  rw [abs_le] at htail
  have htrunc : quadraticHarmonicTruncation χ m ≤
      (χ.LFunction 1).re +
        8 * Real.sqrt q * (1 + Real.log q) / (m : ℝ) := by
    linarith [htail.1]
  have hmul := mul_le_mul_of_nonneg_left htrunc (Nat.cast_nonneg X)
  unfold quadraticSiegelConvolutionDiscrepancy
  linarith

end DirichletCharacter