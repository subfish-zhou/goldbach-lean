import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticSiegelConvolution

/-!
# Finite high-convolution arithmetic for the quadratic Siegel amplifier

For a quadratic character `χ`, the arithmetic function `χ.zetaMul` is the
coefficient sequence of `ζ(s) L(s, χ)`.  This file forms its genuine
Dirichlet-convolution powers.  It proves, without an analytic producer, that
all coefficients are nonnegative and that every nonzero even perfect power
has coefficient at least one at every positive convolution depth.

In particular, if the convolution depth `r` and an even exponent `e` are
positive, the summatory function through `M ^ e` is at least `M`.  Taking
`e = r` (with even `r`) is the finite, scan-free `X^(1/r)` support layer of
the classical high-power amplifier.

This arithmetic layer does **not** by itself improve the existing
`q^(-1/2)`-scale one-fold estimate.  To deduce the genuine large-conductor
Siegel bound from this module, one still needs an analytic estimate of the
following quantified strength for arbitrarily large even `r`:

`S_r(X) ≤ C_r X (log X)^(r-1) L(1,χ)^r + E_r(q,X)`

at a choice `X = q ^ A_r`, with
`E_r(q,X) ≤ (1/2) X^(1/r)` and
`A_r * (r-1) / r^2 → 0` (constants may depend on `r`, hence ultimately on
`η`).  The currently formalized one-fold Pólya--Vinogradov discrepancy gives
no such high-power remainder.  We therefore expose no conclusion-shaped
"source predicate" and make no claim of a large-`q` endpoint here.
-/

open Complex Finset
open ArithmeticFunction hiding log
open scoped BigOperators ComplexOrder Real

namespace DirichletCharacter

variable {q : ℕ}

/-- The `r`-fold Dirichlet-convolution coefficient of `ζ(s)L(s,χ)`. -/
noncomputable def quadraticSiegelPowerCoefficient
    (χ : DirichletCharacter ℂ q) (r n : ℕ) : ℂ :=
  (χ.zetaMul ^ r) n

/-- The coefficient at depth zero is the convolution identity. -/
theorem quadraticSiegelPowerCoefficient_zero
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    quadraticSiegelPowerCoefficient χ 0 n = if n = 1 then 1 else 0 := by
  rw [quadraticSiegelPowerCoefficient, pow_zero, ArithmeticFunction.one_apply]

/-- Exact antidiagonal recursion for the genuine convolution power. -/
theorem quadraticSiegelPowerCoefficient_succ
    (χ : DirichletCharacter ℂ q) (r n : ℕ) :
    quadraticSiegelPowerCoefficient χ (r + 1) n =
      ∑ x ∈ n.divisorsAntidiagonal,
        quadraticSiegelPowerCoefficient χ r x.1 * χ.zetaMul x.2 := by
  rw [quadraticSiegelPowerCoefficient, pow_succ, ArithmeticFunction.mul_apply]
  rfl

private lemma zetaMul_one (χ : DirichletCharacter ℂ q) : χ.zetaMul 1 = 1 := by
  rw [zetaMul, coe_zeta_mul_apply]
  norm_num [toArithmeticFunction]

/-- Every convolution power is normalized to one at `n = 1`. -/
theorem quadraticSiegelPowerCoefficient_one
    (χ : DirichletCharacter ℂ q) (r : ℕ) :
    quadraticSiegelPowerCoefficient χ r 1 = 1 := by
  induction r with
  | zero => rw [quadraticSiegelPowerCoefficient_zero]; simp
  | succ r ih =>
      rw [quadraticSiegelPowerCoefficient_succ]
      simp only [Nat.divisorsAntidiagonal_one, sum_singleton, ih, zetaMul_one, mul_one]

/-- Quadraticity makes every coefficient of every convolution power
nonnegative (in the real-axis order on `ℂ`). -/
theorem quadraticSiegelPowerCoefficient_nonneg
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (r n : ℕ) :
    0 ≤ quadraticSiegelPowerCoefficient χ r n := by
  induction r generalizing n with
  | zero =>
      rw [quadraticSiegelPowerCoefficient_zero]
      split <;> simp
  | succ r ih =>
      rw [quadraticSiegelPowerCoefficient_succ]
      exact Finset.sum_nonneg fun x _ =>
        mul_nonneg (ih x.1) (zetaMul_nonneg hquad x.2)

/-- At every positive depth the high convolution dominates the original
coefficient, by retaining the antidiagonal cell `(1,n)`. -/
theorem zetaMul_le_quadraticSiegelPowerCoefficient_succ
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1)
    (r : ℕ) {n : ℕ} (hn : n ≠ 0) :
    χ.zetaMul n ≤ quadraticSiegelPowerCoefficient χ (r + 1) n := by
  rw [quadraticSiegelPowerCoefficient_succ]
  have hmem : (1, n) ∈ n.divisorsAntidiagonal := by
    rw [Nat.mem_divisorsAntidiagonal]
    simp [hn]
  simpa only [quadraticSiegelPowerCoefficient_one, one_mul] using
    (Finset.single_le_sum
      (s := n.divisorsAntidiagonal)
      (f := fun x => quadraticSiegelPowerCoefficient χ r x.1 * χ.zetaMul x.2)
      (fun x _ => mul_nonneg (quadraticSiegelPowerCoefficient_nonneg χ hquad r x.1)
        (zetaMul_nonneg hquad x.2)) hmem)

/-- Every nonzero even perfect power has high-convolution coefficient at
least one.  The exponent is quantified; no finite scan is involved. -/
theorem one_le_quadraticSiegelPowerCoefficient_evenPow
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1)
    (r : ℕ) {m e : ℕ} (hm : m ≠ 0) (he : ∃ t, e = 2 * t) :
    (1 : ℂ) ≤ quadraticSiegelPowerCoefficient χ (r + 1) (m ^ e) := by
  rcases he with ⟨t, rfl⟩
  have hbase : (1 : ℝ) ≤ quadraticSiegelConvolution χ ((m ^ t) ^ 2) :=
    one_le_quadraticSiegelConvolution_sq hquad (pow_ne_zero _ hm)
  have hzeta : (1 : ℂ) ≤ χ.zetaMul ((m ^ t) ^ 2) := by
    rw [RCLike.le_iff_re_im]
    exact ⟨hbase, (zetaMul_im_eq_zero_of_sq_eq_one χ hquad _).symm⟩
  have hdom := zetaMul_le_quadraticSiegelPowerCoefficient_succ χ hquad r
    (n := (m ^ t) ^ 2) (pow_ne_zero _ (pow_ne_zero _ hm))
  have hout := hzeta.trans hdom
  simpa [pow_mul, Nat.mul_comm] using hout

/-- The real summatory function of the `r`-fold quadratic amplifier. -/
noncomputable def quadraticSiegelPowerSummatory
    (χ : DirichletCharacter ℂ q) (r X : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 X, (quadraticSiegelPowerCoefficient χ r n).re

/-- All summands of the real high-convolution summatory function are
nonnegative. -/
theorem quadraticSiegelPowerCoefficient_re_nonneg
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (r n : ℕ) :
    0 ≤ (quadraticSiegelPowerCoefficient χ r n).re := by
  have h := quadraticSiegelPowerCoefficient_nonneg χ hquad r n
  rw [RCLike.le_iff_re_im] at h
  exact h.1

/-- Perfect-power support lower bound.  At positive convolution depth and any
positive even exponent `e`, the sum through `M^e` is at least `M`. -/
theorem le_quadraticSiegelPowerSummatory_pow
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1)
    (r : ℕ) {e : ℕ} (hepos : 0 < e) (heven : ∃ t, e = 2 * t) (M : ℕ) :
    (M : ℝ) ≤ quadraticSiegelPowerSummatory χ (r + 1) (M ^ e) := by
  let S : Finset ℕ := (Icc 1 M).image (fun m => m ^ e)
  have hsub : S ⊆ Icc 1 (M ^ e) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
    rw [Finset.mem_Icc] at hm ⊢
    exact ⟨Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hm.1)),
      Nat.pow_le_pow_left hm.2 e⟩
  have hsmall :
      (∑ n ∈ S, (quadraticSiegelPowerCoefficient χ (r + 1) n).re) ≤
        ∑ n ∈ Icc 1 (M ^ e),
          (quadraticSiegelPowerCoefficient χ (r + 1) n).re := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn hnS
    exact quadraticSiegelPowerCoefficient_re_nonneg χ hquad (r + 1) n
  have himage :
      (∑ n ∈ S, (quadraticSiegelPowerCoefficient χ (r + 1) n).re) =
        ∑ m ∈ Icc 1 M,
          (quadraticSiegelPowerCoefficient χ (r + 1) (m ^ e)).re := by
    exact Finset.sum_image (s := Icc 1 M)
      (f := fun n => (quadraticSiegelPowerCoefficient χ (r + 1) n).re)
      (Nat.pow_left_injective (Nat.ne_of_gt hepos)).injOn
  calc
    (M : ℝ) = ∑ _m ∈ Icc 1 M, (1 : ℝ) := by simp
    _ ≤ ∑ m ∈ Icc 1 M,
        (quadraticSiegelPowerCoefficient χ (r + 1) (m ^ e)).re := by
      apply Finset.sum_le_sum
      intro m hm
      rw [Finset.mem_Icc] at hm
      have hcomplex := one_le_quadraticSiegelPowerCoefficient_evenPow
        χ hquad r (Nat.ne_of_gt hm.1) heven
      rw [RCLike.le_iff_re_im] at hcomplex
      exact hcomplex.1
    _ = ∑ n ∈ S, (quadraticSiegelPowerCoefficient χ (r + 1) n).re := himage.symm
    _ ≤ quadraticSiegelPowerSummatory χ (r + 1) (M ^ e) := hsmall

/-- The requested scan-free `X^(1/r)` specialization: at even positive depth
`r`, the summatory function through the perfect `r`-th power `M^r` is at
least `M`. -/
theorem le_quadraticSiegelPowerSummatory_selfPow
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1)
    {r : ℕ} (hrpos : 0 < r) (hreven : ∃ t, r = 2 * t) (M : ℕ) :
    (M : ℝ) ≤ quadraticSiegelPowerSummatory χ r (M ^ r) := by
  obtain ⟨r₀, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrpos)
  exact le_quadraticSiegelPowerSummatory_pow χ hquad r₀ hrpos hreven M

end DirichletCharacter
