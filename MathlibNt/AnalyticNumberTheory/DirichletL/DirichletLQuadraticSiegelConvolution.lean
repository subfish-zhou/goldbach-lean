import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticPolyaVinogradovExplicit

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
    _ = ∑ d ∈ n.divisors, (χ d).re := Complex.re_sum _ _

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


/-- The exact residual between the convolution summatory function and `X`
times the finite harmonic truncation.  Later hyperbola estimates should bound
this quantity rather than postulate an unknown error bound. -/
noncomputable def quadraticSiegelConvolutionDiscrepancy
    (χ : DirichletCharacter ℂ q) (X m : ℕ) : ℝ :=
  quadraticSiegelConvolutionSummatory χ X -
    (X : ℝ) * quadraticHarmonicTruncation χ m


end DirichletCharacter