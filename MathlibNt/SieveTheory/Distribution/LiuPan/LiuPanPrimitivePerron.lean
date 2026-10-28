import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# A finite Perron consumer for Liu's primitive hyperbola

This module supplies only the exact finite algebra needed by a later Perron
argument.  The truncated-kernel approximation is an explicit hypothesis; no
analytic estimate for that kernel is asserted here.
-/

open scoped BigOperators Interval

namespace MathlibNt.SieveTheory.LiuWeight

open Finset
open Topology Filter Set Asymptotics

/-- A coefficient sequence extended by zero at the forbidden coordinate `0`. -/
def liuPanPerronZeroExtension (A : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else A n

@[simp] theorem liuPanPerronZeroExtension_zero (A : ℕ → ℂ) :
    liuPanPerronZeroExtension A 0 = 0 := by
  simp [liuPanPerronZeroExtension]

theorem liuPanPerronZeroExtension_of_ne
    (A : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    liuPanPerronZeroExtension A n = A n := by
  simp [liuPanPerronZeroExtension, hn]

/-- The positive-real power used in the finite Dirichlet polynomials. -/
noncomputable def liuPanPerronNatPower (n : ℕ) (s : ℂ) : ℂ :=
  if n = 0 then 0 else Complex.exp (-s * Real.log n)

@[simp] theorem liuPanPerronNatPower_zero (s : ℂ) :
    liuPanPerronNatPower 0 s = 0 := by
  simp [liuPanPerronNatPower]

theorem liuPanPerronNatPower_of_ne {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    liuPanPerronNatPower n s = Complex.exp (-s * Real.log n) := by
  simp [liuPanPerronNatPower, hn]

/-- A finite Dirichlet polynomial twisted by a character.  The zero coordinate,
if present in the supplied finset, contributes exactly zero. -/
noncomputable def liuPanPerronDirichletPolynomial
    {q : ℕ} (U : Finset ℕ) (A : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ u ∈ U,
    liuPanPerronZeroExtension A u * χ (u : ZMod q) *
      liuPanPerronNatPower u s

/-- The coefficient of a positive product coordinate.  It is zero if either
coordinate is zero. -/
noncomputable def liuPanPerronProductCoefficient
    {q : ℕ} (A B : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (u v : ℕ) : ℂ :=
  if u = 0 ∨ v = 0 then 0
  else A u * B v * χ ((u * v : ℕ) : ZMod q)

/-- Exact finite factorization of the two twisted Dirichlet polynomials. -/
theorem liuPanPerronDirichletPolynomial_mul
    {q : ℕ} (U V : Finset ℕ) (A B : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    liuPanPerronDirichletPolynomial U A χ s *
        liuPanPerronDirichletPolynomial V B χ s =
      ∑ u ∈ U, ∑ v ∈ V,
        liuPanPerronProductCoefficient A B χ u v *
          liuPanPerronNatPower (u * v) s := by
  classical
  unfold liuPanPerronDirichletPolynomial
  rw [sum_mul]
  apply sum_congr rfl
  intro u hu
  rw [mul_sum]
  apply sum_congr rfl
  intro v hv
  by_cases hu0 : u = 0
  · subst u
    simp [liuPanPerronProductCoefficient]
  by_cases hv0 : v = 0
  · subst v
    simp [liuPanPerronProductCoefficient]
  rw [liuPanPerronZeroExtension_of_ne A hu0,
    liuPanPerronZeroExtension_of_ne B hv0,
    liuPanPerronNatPower_of_ne hu0,
    liuPanPerronNatPower_of_ne hv0,
    liuPanPerronNatPower_of_ne (Nat.mul_ne_zero hu0 hv0)]
  simp only [liuPanPerronProductCoefficient, hu0, hv0, or_self, if_false]
  have hχmul : χ (((u * v : ℕ) : ZMod q)) =
      χ (u : ZMod q) * χ (v : ZMod q) := by
    rw [Nat.cast_mul, map_mul]
  have huR0 : (u : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hu0
  have hvR0 : (v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hv0
  have hlog : Real.log (u * v : ℕ) = Real.log u + Real.log v := by
    simpa only [Nat.cast_mul] using Real.log_mul huR0 hvR0
  have hpow :
      Complex.exp (-s * Real.log u) * Complex.exp (-s * Real.log v) =
        Complex.exp (-s * Real.log (u * v : ℕ)) := by
    rw [← Complex.exp_add, hlog]
    congr 1
    push_cast
    ring
  rw [hχmul, ← hpow]
  ring

/-- The exact finite character-twisted hyperbola sum. -/
noncomputable def liuPanPerronHyperbolaSum
    {q : ℕ} (U V : Finset ℕ) (A B : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (Y : ℕ) : ℂ :=
  ∑ u ∈ U, ∑ v ∈ V,
    if u * v ≤ Y then liuPanPerronProductCoefficient A B χ u v else 0

/-- The half-integer Perron cutoff. -/
noncomputable def liuPanPerronHalfStep (Y : ℕ) : ℝ :=
  Y + 1 / 2

theorem natCast_lt_liuPanPerronHalfStep_iff {n Y : ℕ} :
    (n : ℝ) < liuPanPerronHalfStep Y ↔ n ≤ Y := by
  unfold liuPanPerronHalfStep
  constructor
  · intro h
    by_contra hnY
    have hYn : Y + 1 ≤ n := by omega
    have hYnR : (Y : ℝ) + 1 ≤ n := by exact_mod_cast hYn
    norm_num at h
    linarith
  · intro hnY
    have hnYR : (n : ℝ) ≤ Y := by exact_mod_cast hnY
    norm_num
    linarith

theorem natCast_ne_liuPanPerronHalfStep (n Y : ℕ) :
    (n : ℝ) ≠ liuPanPerronHalfStep Y := by
  intro h
  have htwo : (2 : ℝ) * n = 2 * Y + 1 := by
    rw [h]
    unfold liuPanPerronHalfStep
    ring
  have : (2 : ℕ) * n = 2 * Y + 1 := by
    exact_mod_cast htwo
  omega


/-- The ratio occurring in the Perron kernel is positive at every positive
integer coordinate. -/
theorem liuPanPerronHalfStep_div_natCast_pos {n Y : ℕ} (hn : n ≠ 0) :
    0 < liuPanPerronHalfStep Y / (n : ℝ) := by
  apply div_pos
  · unfold liuPanPerronHalfStep
    positivity
  · exact_mod_cast Nat.pos_of_ne_zero hn

private theorem one_div_four_mul_le_one_sub_inv_div_of_half_gap
    {x n M : ℝ} (hx : 0 < x) (hM : 1 ≤ M)
    (hgap : 1 / 2 ≤ x - n) (hxM : x ≤ 2 * M) :
    1 / (4 * M) ≤ 1 - (x / n)⁻¹ := by
  have hMp : 0 < M := lt_of_lt_of_le (by norm_num) hM
  rw [inv_div, div_eq_mul_inv]
  apply (le_sub_iff_add_le).2
  field_simp
  nlinarith

/-- Uniform separation from the logarithmic singularity on a box of side
`M`.  The constant `1 / (4 * M)` is deliberately safe at the upper half-step
`M + 1 / 2`. -/
theorem one_div_four_mul_le_abs_log_liuPanPerronHalfStep_div
    {n Y M : ℕ} (hn : n ≠ 0) (hM : 1 ≤ M)
    (hYM : Y ≤ M) (hnM : n ≤ M) :
    1 / (4 * (M : ℝ)) ≤
      |Real.log (liuPanPerronHalfStep Y / (n : ℝ))| := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hYMR : (Y : ℝ) ≤ M := by exact_mod_cast hYM
  have hnMR : (n : ℝ) ≤ M := by exact_mod_cast hnM
  have hx : 0 < liuPanPerronHalfStep Y := by
    unfold liuPanPerronHalfStep
    positivity
  have hratio : 0 < liuPanPerronHalfStep Y / (n : ℝ) :=
    div_pos hx hnR
  by_cases h : n ≤ Y
  · have hnY : (n : ℝ) ≤ Y := by exact_mod_cast h
    have hgap : (1 / 2 : ℝ) ≤ liuPanPerronHalfStep Y - n := by
      unfold liuPanPerronHalfStep
      norm_num
      linarith
    have hxM : liuPanPerronHalfStep Y ≤ 2 * (M : ℝ) := by
      unfold liuPanPerronHalfStep
      norm_num
      linarith
    have hlow :=
      one_div_four_mul_le_one_sub_inv_div_of_half_gap hx hMR hgap hxM
    have hone : (1 : ℝ) ≤ liuPanPerronHalfStep Y / (n : ℝ) := by
      rw [one_le_div₀ hnR]
      linarith
    rw [abs_of_nonneg (Real.log_nonneg hone)]
    exact hlow.trans (Real.one_sub_inv_le_log_of_pos hratio)
  · have hYn : Y + 1 ≤ n := by omega
    have hYnR : (Y : ℝ) + 1 ≤ n := by exact_mod_cast hYn
    have hgap : (1 / 2 : ℝ) ≤
        (n : ℝ) - liuPanPerronHalfStep Y := by
      unfold liuPanPerronHalfStep
      norm_num
      linarith
    have hn2M : (n : ℝ) ≤ 2 * (M : ℝ) := by nlinarith
    have hrevpos : 0 < (n : ℝ) / liuPanPerronHalfStep Y :=
      div_pos hnR hx
    have hlow :=
      one_div_four_mul_le_one_sub_inv_div_of_half_gap hnR hMR hgap hn2M
    have hle : liuPanPerronHalfStep Y / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnR]
      linarith
    rw [abs_of_nonpos (Real.log_nonpos hratio.le hle)]
    calc
      1 / (4 * (M : ℝ)) ≤
          1 - (((n : ℝ) / liuPanPerronHalfStep Y)⁻¹) := hlow
      _ ≤ Real.log ((n : ℝ) / liuPanPerronHalfStep Y) :=
        Real.one_sub_inv_le_log_of_pos hrevpos
      _ = -Real.log (liuPanPerronHalfStep Y / (n : ℝ)) := by
        rw [← Real.log_inv, inv_div]


/-- The vertical line `sigma + it`. -/
noncomputable def liuPanPerronLine (σ t : ℝ) : ℂ :=
  (σ : ℂ) + (t : ℂ) * Complex.I

/-- The classical truncated Perron kernel after parametrizing the vertical
segment by its imaginary coordinate. -/
noncomputable def liuPanTruncatedPerronKernel
    (σ T z : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ t in -T..T,
      Complex.exp (liuPanPerronLine σ t * Real.log z) /
        liuPanPerronLine σ t


/-- The actual vertical-line integral of the product of the two finite
Dirichlet polynomials. -/
noncomputable def liuPanTruncatedPerronIntegral
    {q : ℕ} (U V : Finset ℕ) (A B : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) (Y : ℕ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ t in -T..T,
      Complex.exp
          (liuPanPerronLine σ t * Real.log (liuPanPerronHalfStep Y)) /
          liuPanPerronLine σ t *
        (liuPanPerronDirichletPolynomial U A χ (liuPanPerronLine σ t) *
          liuPanPerronDirichletPolynomial V B χ (liuPanPerronLine σ t))

/-- The exact remainder after replacing the hyperbola cutoff by the truncated
Perron integral. -/
noncomputable def liuPanTruncatedPerronError
    {q : ℕ} (U V : Finset ℕ) (A B : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) (Y : ℕ) : ℂ :=
  liuPanPerronHyperbolaSum U V A B χ Y -
    liuPanTruncatedPerronIntegral U V A B χ σ T Y


private theorem liuPanPerronLine_ne_zero {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    liuPanPerronLine σ t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [liuPanPerronLine] at hre
  linarith

private theorem liuPanPerronKernelIntegrand_intervalIntegrable
    {σ T z : ℝ} (hσ : 0 < σ) :
    IntervalIntegrable
      (fun t : ℝ =>
        Complex.exp (liuPanPerronLine σ t * Real.log z) /
          liuPanPerronLine σ t)
      MeasureTheory.volume (-T) T := by
  apply Continuous.intervalIntegrable
  have hline : Continuous (liuPanPerronLine σ) := by
    unfold liuPanPerronLine
    fun_prop
  apply Continuous.div
  · exact Complex.continuous_exp.comp
      (hline.mul continuous_const)
  · exact hline
  · exact liuPanPerronLine_ne_zero hσ

private theorem liuPanPerronKernelIntegrand_exp_eq
    (σ z t : ℝ) :
    Complex.exp (liuPanPerronLine σ t * Real.log z) =
      (Real.exp (σ * Real.log z) : ℂ) *
        ((Real.cos (t * Real.log z) : ℂ) +
          (Real.sin (t * Real.log z) : ℂ) * Complex.I) := by
  rw [show liuPanPerronLine σ t * Real.log z =
      ((σ * Real.log z : ℝ) : ℂ) +
        ((t * Real.log z : ℝ) : ℂ) * Complex.I by
    unfold liuPanPerronLine
    push_cast
    ring]
  rw [Complex.exp_add_mul_I]
  norm_cast

private theorem liuPanPerronLine_inv_eq
    (σ t : ℝ) (hσ : σ ≠ 0) :
    (liuPanPerronLine σ t)⁻¹ =
      ((σ : ℂ) - (t : ℂ) * Complex.I) /
        ((σ ^ 2 + t ^ 2 : ℝ) : ℂ) := by
  have hline : liuPanPerronLine σ t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [liuPanPerronLine] at hre
    exact hσ hre
  have hsq : ((σ ^ 2 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show σ ^ 2 + t ^ 2 ≠ 0 by positivity)
  field_simp [hline, hsq]
  simp only [liuPanPerronLine]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- Pairing heights `t` and `-t` turns the complex Perron integrand into an
explicit real-valued cosine/sine expression. -/
theorem liuPanPerronKernelIntegrand_add_neg
    {σ : ℝ} (hσ : 0 < σ) (z t : ℝ) :
    Complex.exp (liuPanPerronLine σ t * Real.log z) /
          liuPanPerronLine σ t +
        Complex.exp (liuPanPerronLine σ (-t) * Real.log z) /
          liuPanPerronLine σ (-t) =
      ((2 * Real.exp (σ * Real.log z) *
          (σ * Real.cos (t * Real.log z) +
            t * Real.sin (t * Real.log z)) /
          (σ ^ 2 + t ^ 2) : ℝ) : ℂ) := by
  rw [liuPanPerronKernelIntegrand_exp_eq,
    liuPanPerronKernelIntegrand_exp_eq]
  simp only [div_eq_mul_inv,
    liuPanPerronLine_inv_eq σ t hσ.ne',
    liuPanPerronLine_inv_eq σ (-t) hσ.ne',
    Real.cos_neg, Real.sin_neg, neg_mul, neg_sq]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- Exact real cosine/sine form of the truncated Perron kernel.  This is only
an algebraic pairing identity; it does not assert a kernel approximation. -/
theorem liuPanTruncatedPerronKernel_eq_paired_real_integral
    {σ : ℝ} (hσ : 0 < σ) (T z : ℝ) :
    liuPanTruncatedPerronKernel σ T z =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ t in 0..T,
          ((2 * Real.exp (σ * Real.log z) *
              (σ * Real.cos (t * Real.log z) +
                t * Real.sin (t * Real.log z)) /
              (σ ^ 2 + t ^ 2) : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun t =>
    Complex.exp (liuPanPerronLine σ t * Real.log z) /
      liuPanPerronLine σ t
  have hf : Continuous f := by
    dsimp only [f]
    have hline : Continuous (liuPanPerronLine σ) := by
      unfold liuPanPerronLine
      fun_prop
    apply Continuous.div
    · exact Complex.continuous_exp.comp
        (hline.mul continuous_const)
    · exact hline
    · exact liuPanPerronLine_ne_zero hσ
  have hpair :
      (∫ t in -T..T, f t) = ∫ t in 0..T, (f t + f (-t)) := by
    have hfneg : IntervalIntegrable f MeasureTheory.volume (-T) 0 :=
      hf.intervalIntegrable (-T) 0
    have hfpos : IntervalIntegrable f MeasureTheory.volume 0 T :=
      hf.intervalIntegrable 0 T
    have href : IntervalIntegrable (fun t => f (-t))
        MeasureTheory.volume 0 T := by
      have hc : Continuous (fun t => f (-t)) := by fun_prop
      exact hc.intervalIntegrable 0 T
    calc
      (∫ t in -T..T, f t) =
          (∫ t in -T..0, f t) + ∫ t in 0..T, f t :=
        (intervalIntegral.integral_add_adjacent_intervals
          hfneg hfpos).symm
      _ = (∫ t in 0..T, f (-t)) + ∫ t in 0..T, f t := by
        rw [intervalIntegral.integral_comp_neg]
        norm_num
      _ = ∫ t in 0..T, (f (-t) + f t) :=
        (intervalIntegral.integral_add href hfpos).symm
      _ = ∫ t in 0..T, (f t + f (-t)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact add_comm _ _
  unfold liuPanTruncatedPerronKernel
  change (((2 * Real.pi : ℝ) : ℂ)⁻¹) * (∫ t in -T..T, f t) = _
  rw [hpair]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact liuPanPerronKernelIntegrand_add_neg hσ z t

private theorem liuPanPerronSincTail_eq_ibp
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, Real.sinc x =
      (-Real.cos b / b + Real.cos a / a) -
        ∫ x in a..b, Real.cos x / x ^ 2 := by
  have hpos_uIcc : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hsinc :
      (∫ x in a..b, Real.sinc x) = ∫ x in a..b, x⁻¹ * Real.sin x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hx0 : x ≠ 0 := (hpos_uIcc x hx).ne'
    rw [Real.sinc_of_ne_zero hx0]
    ring
  have hu : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := by
    intro x hx
    exact hasDerivAt_inv (hpos_uIcc x hx).ne'
  have hv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -Real.cos y) (Real.sin x) x := by
    intro x _hx
    have h : HasDerivAt (fun y : ℝ => -Real.cos y) (-(-Real.sin x)) x :=
      (Real.hasDerivAt_cos x).neg
    rwa [neg_neg] at h
  have hu' : IntervalIntegrable (fun x : ℝ => -(x ^ 2)⁻¹)
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact ((continuousOn_pow 2).inv₀ fun x hx => by
      exact pow_ne_zero 2
        (hpos_uIcc x (by simpa [Set.uIcc_of_le hab] using hx)).ne').neg
  have hv' : IntervalIntegrable (fun x : ℝ => Real.sin x)
      MeasureTheory.volume a b :=
    Real.continuous_sin.intervalIntegrable a b
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => x⁻¹) (v := fun x : ℝ => -Real.cos x)
    (u' := fun x : ℝ => -(x ^ 2)⁻¹) (v' := fun x : ℝ => Real.sin x)
    hu hv hu' hv'
  have hint :
      (∫ x in a..b, (-(x ^ 2)⁻¹) * -Real.cos x) =
        ∫ x in a..b, Real.cos x / x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x _hx
    field_simp [sq]
  rw [hsinc, hIBP, hint]
  ring_nf

private theorem liuPanIntervalIntegralInvSq_of_pos
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, (x ^ 2)⁻¹ = a⁻¹ - b⁻¹ := by
  have hpos_uIcc : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -y⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    have h : HasDerivAt (fun y : ℝ => -y⁻¹) (-(-(x ^ 2)⁻¹)) x :=
      (hasDerivAt_inv (hpos_uIcc x hx).ne').neg
    rwa [neg_neg] at h
  have hint : IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹)
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact (continuousOn_pow 2).inv₀ fun x hx => by
      exact pow_ne_zero 2
        (hpos_uIcc x (by simpa [Set.uIcc_of_le hab] using hx)).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

private theorem norm_liuPanPerronSincTail_le
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, Real.sinc x‖ ≤ 3 * a⁻¹ := by
  have hb_pos : 0 < b := ha.trans_le hab
  have hpos_uIcc : ∀ x ∈ Set.Icc a b, 0 < x := by
    intro x hx
    exact ha.trans_le hx.1
  have hboundary : ‖-Real.cos b / b + Real.cos a / a‖ ≤ 2 * a⁻¹ := by
    calc
      ‖-Real.cos b / b + Real.cos a / a‖
          = |(-Real.cos b / b) + (Real.cos a / a)| := by
              rw [Real.norm_eq_abs]
      _ ≤ |-Real.cos b / b| + |Real.cos a / a| := abs_add_le _ _
      _ ≤ b⁻¹ + a⁻¹ := by
            refine add_le_add ?_ ?_
            · calc
                |-Real.cos b / b| = |Real.cos b| / b := by
                  rw [abs_div, abs_neg, abs_of_pos hb_pos]
                _ ≤ 1 / b := div_le_div_of_nonneg_right
                  (Real.abs_cos_le_one b) hb_pos.le
                _ = b⁻¹ := by rw [one_div]
            · calc
                |Real.cos a / a| = |Real.cos a| / a := by
                  rw [abs_div, abs_of_pos ha]
                _ ≤ 1 / a := div_le_div_of_nonneg_right
                  (Real.abs_cos_le_one a) ha.le
                _ = a⁻¹ := by rw [one_div]
      _ ≤ a⁻¹ + a⁻¹ := by
            exact add_le_add (by
              simpa [one_div] using one_div_le_one_div_of_le ha hab) le_rfl
      _ = 2 * a⁻¹ := by ring
  have hnormInt : IntervalIntegrable (fun x : ℝ => ‖Real.cos x / x ^ 2‖)
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact ((Real.continuous_cos.continuousOn).div (continuousOn_pow 2) fun x hx => by
      exact pow_ne_zero 2 (hpos_uIcc x hx).ne').norm
  have hinvInt : IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹)
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact (continuousOn_pow 2).inv₀ fun x hx => by
      exact pow_ne_zero 2 (hpos_uIcc x hx).ne'
  have hJ : ‖∫ x in a..b, Real.cos x / x ^ 2‖ ≤ a⁻¹ := by
    calc
      ‖∫ x in a..b, Real.cos x / x ^ 2‖
          ≤ ∫ x in a..b, ‖Real.cos x / x ^ 2‖ :=
            intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ x in a..b, (x ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on hab hnormInt hinvInt ?_
            intro x hx
            have hx_pos : 0 < x := hpos_uIcc x hx
            calc
              ‖Real.cos x / x ^ 2‖ = |Real.cos x| / x ^ 2 := by
                rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hx_pos 2)]
              _ ≤ 1 / x ^ 2 :=
                div_le_div_of_nonneg_right (Real.abs_cos_le_one x) (sq_nonneg x)
              _ = (x ^ 2)⁻¹ := by rw [one_div]
      _ = a⁻¹ - b⁻¹ := liuPanIntervalIntegralInvSq_of_pos ha hab
      _ ≤ a⁻¹ := sub_le_self _ (inv_nonneg.mpr hb_pos.le)
  rw [liuPanPerronSincTail_eq_ibp ha hab]
  calc
    ‖(-Real.cos b / b + Real.cos a / a) -
        ∫ x in a..b, Real.cos x / x ^ 2‖
        ≤ ‖-Real.cos b / b + Real.cos a / a‖ +
            ‖∫ x in a..b, Real.cos x / x ^ 2‖ := norm_sub_le _ _
    _ ≤ 2 * a⁻¹ + a⁻¹ := add_le_add hboundary hJ
    _ = 3 * a⁻¹ := by ring

private theorem abs_liuPanPositivePerronSineTail_le
    {a T S : ℝ} (ha : 0 < a) (hT : 0 < T) (hTS : T ≤ S) :
    |∫ t in T..S, Real.sin (a * t) / t| ≤ 3 / (a * T) := by
  have hpos_uIcc : ∀ t ∈ Set.uIcc T S, 0 < t := by
    intro t ht
    rw [Set.uIcc_of_le hTS] at ht
    exact hT.trans_le ht.1
  have hrewrite :
      (∫ t in T..S, Real.sin (a * t) / t) =
        a * ∫ t in T..S, Real.sinc (a * t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : t ≠ 0 := (hpos_uIcc t ht).ne'
    have hat0 : a * t ≠ 0 := mul_ne_zero ha.ne' ht0
    change Real.sin (a * t) / t = a * Real.sinc (a * t)
    rw [Real.sinc_of_ne_zero hat0]
    field_simp
  have hscale :
      a * ∫ t in T..S, Real.sinc (a * t) =
        ∫ x in a * T..a * S, Real.sinc x :=
    intervalIntegral.mul_integral_comp_mul_left a
  rw [hrewrite, hscale, ← Real.norm_eq_abs]
  have hbound := norm_liuPanPerronSincTail_le (mul_pos ha hT)
    (mul_le_mul_of_nonneg_left hTS ha.le)
  simpa [div_eq_mul_inv] using hbound

/-- The finite oscillatory sine tail needed for the quantitative Perron
approximation.  Integration by parts gives the explicit constant `3`. -/
theorem LiuPanPerronSineTailBound :
    ∀ a T S : ℝ, a ≠ 0 → 0 < T → T ≤ S →
      |∫ t in T..S, Real.sin (a * t) / t| ≤ 3 / (|a| * T) := by
  intro a T S ha hT hTS
  by_cases hapos : 0 < a
  · simpa [abs_of_pos hapos] using
      abs_liuPanPositivePerronSineTail_le hapos hT hTS
  · have haneg : a < 0 := lt_of_le_of_ne (le_of_not_gt hapos) ha
    have hnegpos : 0 < -a := neg_pos.mpr haneg
    have heq :
        (∫ t in T..S, Real.sin (a * t) / t) =
          -(∫ t in T..S, Real.sin ((-a) * t) / t) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro t ht
      change Real.sin (a * t) / t = -(Real.sin ((-a) * t) / t)
      rw [show a * t = -((-a) * t) by ring, Real.sin_neg]
      ring
    rw [heq, abs_neg]
    simpa [abs_of_neg haneg] using
      abs_liuPanPositivePerronSineTail_le hnegpos hT hTS

private theorem cauchySeq_intervalIntegral_of_inv_tail
    (f : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hfi : ∀ a b : ℝ,
      IntervalIntegrable f MeasureTheory.volume a b)
    (htail : ∀ {T S : ℝ}, 0 < T → T ≤ S →
      |∫ t in T..S, f t| ≤ C / T) :
    CauchySeq (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t) := by
  refine Metric.cauchySeq_iff.2 ?_
  intro ε hε
  have hlim :
      Filter.Tendsto (fun M : ℝ => C * M⁻¹) Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Filter.Tendsto (fun M : ℝ => C * M⁻¹) Filter.atTop
          (nhds (C * 0)))
  have hsmall : ∀ᶠ M : ℝ in Filter.atTop, C * M⁻¹ < ε :=
    hlim.eventually (gt_mem_nhds hε)
  have hlarge : ∀ᶠ M : ℝ in Filter.atTop, 1 ≤ M :=
    Filter.eventually_ge_atTop 1
  rcases Filter.eventually_atTop.1 (hsmall.and hlarge) with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro A hA B hB
  have hMsmall : C * M⁻¹ < ε := (hM M le_rfl).1
  have hMpos : 0 < M := zero_lt_one.trans_le (hM M le_rfl).2
  by_cases hAB : A ≤ B
  · have hsub :
        (∫ t in (0 : ℝ)..B, f t) - (∫ t in (0 : ℝ)..A, f t) =
          ∫ t in A..B, f t :=
      intervalIntegral.integral_interval_sub_left (hfi 0 B) (hfi 0 A)
    have htailAB := htail (hMpos.trans_le hA) hAB
    have hinv : C / A ≤ C / M :=
      div_le_div_of_nonneg_left hC hMpos hA
    calc
      dist (∫ t in (0 : ℝ)..A, f t)
          (∫ t in (0 : ℝ)..B, f t) =
          |(∫ t in (0 : ℝ)..B, f t) -
            (∫ t in (0 : ℝ)..A, f t)| := by
        rw [Real.dist_eq]
        exact abs_sub_comm _ _
      _ = |∫ t in A..B, f t| := by rw [hsub]
      _ ≤ C / A := htailAB
      _ ≤ C / M := hinv
      _ = C * M⁻¹ := by rw [div_eq_mul_inv]
      _ < ε := hMsmall
  · have hBA : B ≤ A := le_of_not_ge hAB
    have hsub :
        (∫ t in (0 : ℝ)..A, f t) - (∫ t in (0 : ℝ)..B, f t) =
          ∫ t in B..A, f t :=
      intervalIntegral.integral_interval_sub_left (hfi 0 A) (hfi 0 B)
    have htailBA := htail (hMpos.trans_le hB) hBA
    have hinv : C / B ≤ C / M :=
      div_le_div_of_nonneg_left hC hMpos hB
    calc
      dist (∫ t in (0 : ℝ)..A, f t)
          (∫ t in (0 : ℝ)..B, f t) =
          |(∫ t in (0 : ℝ)..A, f t) -
            (∫ t in (0 : ℝ)..B, f t)| := by
        rw [Real.dist_eq]
      _ = |∫ t in B..A, f t| := by rw [hsub]
      _ ≤ C / B := htailBA
      _ ≤ C / M := hinv
      _ = C * M⁻¹ := by rw [div_eq_mul_inv]
      _ < ε := hMsmall


private theorem liuPanIntervalIntegralExpNegMulConstMulSelf
    (a R B : ℝ) :
    ∫ x in R..B, a * Real.exp (-a * x) =
      Real.exp (-a * R) - Real.exp (-a * B) := by
  have hderiv : ∀ x ∈ Set.uIcc R B,
      HasDerivAt (fun y : ℝ => -Real.exp (-a * y))
        (a * Real.exp (-a * x)) x := by
    intro x _hx
    have hlin : HasDerivAt (fun y : ℝ => -a * y) (-a) x := by
      simpa using (hasDerivAt_id x).const_mul (-a)
    have h := (Real.hasDerivAt_exp (-a * x)).comp x hlin
    rw [show a * Real.exp (-a * x) =
      -(Real.exp (-a * x) * -a) from by ring]
    exact h.neg
  have hint : IntervalIntegrable
      (fun x : ℝ => a * Real.exp (-a * x))
      MeasureTheory.volume R B := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring


private theorem liuPanIntegralIoiExpNegMulSin
    (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sin x =
      1 / (a ^ 2 + 1) := by
  let z : ℂ := (-(a : ℂ)) + Complex.I
  have hzre : z.re < 0 := by
    simp [z, ha]
  have hint : MeasureTheory.Integrable
      (fun x : ℝ => Complex.exp (z * x))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    integrableOn_exp_mul_complex_Ioi (a := z) hzre 0
  have him := integral_im
    (μ := MeasureTheory.volume.restrict (Set.Ioi 0)) hint
  have hpoint :
      (fun x : ℝ => Real.exp (-a * x) * Real.sin x) =
        fun x : ℝ => (Complex.exp (z * x)).im := by
    funext x
    simp [z, Complex.exp_im, mul_add, mul_comm]
  calc
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sin x =
        ∫ x : ℝ in Set.Ioi 0, (Complex.exp (z * x)).im := by
      rw [hpoint]
    _ = (∫ x : ℝ in Set.Ioi 0, Complex.exp (z * x)).im := by
      simpa using him
    _ = (-Complex.exp (z * (0 : ℝ)) / z).im := by
      rw [integral_exp_mul_complex_Ioi (a := z) hzre 0]
    _ = 1 / (a ^ 2 + 1) := by
      simp [z, Complex.div_im, Complex.normSq]
      ring

private theorem liuPanIntegralIoiOneDivOneAddSqEqArctanInv
    (a : ℝ) (ha : 0 < a) :
    ∫ u : ℝ in Set.Ioi a, (1 / (u ^ 2 + 1) : ℝ) =
      Real.arctan a⁻¹ := by
  have h :
      ∫ u : ℝ in Set.Ioi a, (1 / (u ^ 2 + 1) : ℝ) =
        Real.pi / 2 - Real.arctan a := by
    simpa [one_div, add_comm] using
      integral_Ioi_inv_one_add_sq (i := a)
  rw [h]
  exact (Real.arctan_inv_of_pos ha).symm

private theorem liuPanIntegralIoiExpNegMulConst
    (a x : ℝ) (hx : 0 < x) :
    ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) =
      Real.exp (-a * x) / x := by
  have h := integral_exp_mul_Ioi (a := -x) (by linarith : -x < 0) a
  calc
    ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) =
        ∫ u : ℝ in Set.Ioi a, Real.exp ((-x) * u) := by
      congr with u
      ring_nf
    _ = Real.exp (-a * x) / x := by
      rw [h]
      field_simp [hx.ne']

private theorem liuPanIntegralIoiExpNegMulConstMulSin
    (a x : ℝ) (hx : 0 < x) :
    ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) * Real.sin x =
      Real.exp (-a * x) * Real.sinc x := by
  rw [MeasureTheory.integral_mul_const]
  rw [liuPanIntegralIoiExpNegMulConst a x hx]
  rw [Real.sinc_of_ne_zero hx.ne']
  field_simp [hx.ne']

private theorem liuPanIntegrableExpNegMulSin_prod_Ioi
    (a : ℝ) (ha : 0 < a) :
    MeasureTheory.Integrable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioi a))) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  let ν := MeasureTheory.volume.restrict (Set.Ioi a)
  change MeasureTheory.Integrable
    (Function.uncurry
      (fun x u : ℝ => Real.exp (-u * x) * Real.sin x)) (μ.prod ν)
  have hsm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x))
      (μ.prod ν) := by
    exact (by fun_prop : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x))
      (μ.prod ν))
  rw [MeasureTheory.integrable_prod_iff hsm]
  constructor
  · dsimp [μ]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    change MeasureTheory.Integrable
      (fun u : ℝ => Real.exp (-u * x) * Real.sin x) ν
    have h_exp : MeasureTheory.Integrable
        (fun u : ℝ => Real.exp (-u * x)) ν := by
      dsimp [ν]
      change MeasureTheory.IntegrableOn
        (fun u : ℝ => Real.exp (-u * x)) (Set.Ioi a)
      simpa [mul_comm] using
        integrableOn_exp_mul_Ioi (a := -x) (neg_lt_zero.mpr hx) a
    exact h_exp.mul_const (Real.sin x)
  · have h_exp_a : MeasureTheory.Integrable
        (fun x : ℝ => Real.exp (-a * x)) μ := by
      dsimp [μ]
      change MeasureTheory.IntegrableOn
        (fun x : ℝ => Real.exp (-a * x)) (Set.Ioi 0)
      simpa [mul_comm] using
        exp_neg_integrableOn_Ioi (0 : ℝ) (b := a) ha
    refine h_exp_a.mono ?_ ?_
    · exact hsm.norm.integral_prod_right'
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      have h_exp_x : MeasureTheory.Integrable
          (fun y : ℝ => Real.exp (-y * x)) ν := by
        dsimp [ν]
        change MeasureTheory.IntegrableOn
          (fun y : ℝ => Real.exp (-y * x)) (Set.Ioi a)
        simpa [mul_comm] using
          integrableOn_exp_mul_Ioi (a := -x) (neg_lt_zero.mpr hx0) a
      have h_lhs : MeasureTheory.Integrable
          (fun y : ℝ =>
            ‖Function.uncurry
              (fun x u : ℝ => Real.exp (-u * x) * Real.sin x)
              (x, y)‖) ν := by
        simpa [Function.uncurry] using
          (h_exp_x.mul_const (Real.sin x)).norm
      have h_rhs : MeasureTheory.Integrable
          (fun y : ℝ => Real.exp (-y * x) * x) ν :=
        h_exp_x.mul_const x
      calc
        ‖∫ y : ℝ, ‖Function.uncurry
            (fun x u : ℝ => Real.exp (-u * x) * Real.sin x)
            (x, y)‖ ∂ν‖ =
            ∫ y : ℝ, ‖Function.uncurry
              (fun x u : ℝ => Real.exp (-u * x) * Real.sin x)
              (x, y)‖ ∂ν := by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact MeasureTheory.integral_nonneg fun y => norm_nonneg _
        _ ≤ ∫ y : ℝ, Real.exp (-y * x) * x ∂ν := by
          refine MeasureTheory.integral_mono_ae h_lhs h_rhs ?_
          filter_upwards with y
          rw [Function.uncurry, Real.norm_eq_abs, abs_mul,
            abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_left
            (by simpa [abs_of_pos hx0] using
              (Real.abs_sin_le_abs (x := x)))
            (Real.exp_pos _).le
        _ = Real.exp (-a * x) := by
          dsimp [ν]
          rw [MeasureTheory.integral_mul_const]
          rw [liuPanIntegralIoiExpNegMulConst a x hx0]
          field_simp [hx0.ne']
        _ = ‖Real.exp (-a * x)‖ := by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem liuPanIntegralIoiExpNegMulSinc_eq_arctan_inv
    (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x =
      Real.arctan a⁻¹ := by
  have hswap :
      (∫ x : ℝ in Set.Ioi 0,
        ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) * Real.sin x) =
      ∫ u : ℝ in Set.Ioi a,
        ∫ x : ℝ in Set.Ioi 0, Real.exp (-u * x) * Real.sin x := by
    simpa [Function.uncurry] using
      MeasureTheory.integral_integral_swap
        (liuPanIntegrableExpNegMulSin_prod_Ioi a ha)
  calc
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x =
        ∫ x : ℝ in Set.Ioi 0,
          ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) * Real.sin x := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      exact (liuPanIntegralIoiExpNegMulConstMulSin a x hx).symm
    _ = ∫ u : ℝ in Set.Ioi a,
        ∫ x : ℝ in Set.Ioi 0,
          Real.exp (-u * x) * Real.sin x := hswap
    _ = ∫ u : ℝ in Set.Ioi a, (1 / (u ^ 2 + 1) : ℝ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      exact liuPanIntegralIoiExpNegMulSin u (lt_trans ha hu)
    _ = Real.arctan a⁻¹ :=
      liuPanIntegralIoiOneDivOneAddSqEqArctanInv a ha


private theorem abs_liuPanPerronPoissonCosineIntegrand_le
    {σ a t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    |σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2)| ≤ σ / t ^ 2 := by
  rw [abs_div, abs_mul, abs_of_pos hσ,
    abs_of_pos (by positivity : 0 < σ ^ 2 + t ^ 2)]
  calc
    σ * |Real.cos (a * t)| / (σ ^ 2 + t ^ 2) ≤
        σ / (σ ^ 2 + t ^ 2) := by
      apply div_le_div_of_nonneg_right
      · simpa using
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (a * t)) hσ.le
      · positivity
    _ ≤ σ / t ^ 2 := by
      apply div_le_div_of_nonneg_left hσ.le (sq_pos_of_pos ht)
      nlinarith only [sq_nonneg σ]

/-- The absolutely convergent cosine part of the paired Perron kernel has an
explicit finite tail. -/
theorem abs_liuPanPerronPoissonCosineTail_le
    {σ a T S : ℝ} (hσ : 0 < σ) (hT : 0 < T) (hTS : T ≤ S) :
    |∫ t in T..S, σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2)| ≤
      σ / T := by
  have hS : 0 < S := hT.trans_le hTS
  have hcont :
      Continuous (fun t : ℝ =>
        σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2)) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    positivity
  have hnormInt : IntervalIntegrable
      (fun t : ℝ =>
        ‖σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2)‖)
      MeasureTheory.volume T S :=
    hcont.norm.intervalIntegrable T S
  have hboundInt : IntervalIntegrable (fun t : ℝ => σ / t ^ 2)
      MeasureTheory.volume T S := by
    apply ContinuousOn.intervalIntegrable_of_Icc hTS
    exact continuousOn_const.div (continuousOn_id.pow 2) fun t ht =>
      pow_ne_zero 2 (hT.trans_le ht.1).ne'
  calc
    |∫ t in T..S, σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2)| =
        ‖∫ t in T..S, σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2)‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∫ t in T..S,
          ‖σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hTS
    _ ≤ ∫ t in T..S, σ / t ^ 2 := by
      refine intervalIntegral.integral_mono_on hTS hnormInt hboundInt ?_
      intro t ht
      rw [Real.norm_eq_abs]
      exact abs_liuPanPerronPoissonCosineIntegrand_le hσ
        (hT.trans_le ht.1)
    _ = σ * (T⁻¹ - S⁻¹) := by
      change (∫ t in T..S, σ * (t ^ 2)⁻¹) =
        σ * (T⁻¹ - S⁻¹)
      rw [intervalIntegral.integral_const_mul,
        liuPanIntervalIntegralInvSq_of_pos hT hTS]
    _ ≤ σ * T⁻¹ := by
      exact mul_le_mul_of_nonneg_left
        (sub_le_self _ (inv_nonneg.mpr hS.le)) hσ.le
    _ = σ / T := by rw [div_eq_mul_inv]

private theorem abs_liuPanPerronPoissonSineIntegrand_sub_le
    {σ a t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    |t * Real.sin (a * t) / (σ ^ 2 + t ^ 2) -
        Real.sin (a * t) / t| ≤
      σ / (2 * t ^ 2) := by
  have hid :
      t * Real.sin (a * t) / (σ ^ 2 + t ^ 2) -
          Real.sin (a * t) / t =
        -(σ ^ 2 * Real.sin (a * t)) /
          (t * (σ ^ 2 + t ^ 2)) := by
    field_simp [hσ.ne', ht.ne']
    ring
  rw [hid, abs_div, abs_neg, abs_mul, abs_pow, abs_of_pos hσ,
    abs_of_pos (mul_pos ht (by positivity : 0 < σ ^ 2 + t ^ 2))]
  calc
    σ ^ 2 * |Real.sin (a * t)| / (t * (σ ^ 2 + t ^ 2)) ≤
        σ ^ 2 / (t * (σ ^ 2 + t ^ 2)) := by
      apply div_le_div_of_nonneg_right
      · simpa using mul_le_mul_of_nonneg_left
          (Real.abs_sin_le_one (a * t)) (sq_nonneg σ)
      · positivity
    _ ≤ σ / (2 * t ^ 2) := by
      rw [div_le_div_iff₀ (mul_pos ht (by positivity))
        (mul_pos (by positivity) (by positivity))]
      have hamgm : 2 * σ * t ≤ σ ^ 2 + t ^ 2 := by
        nlinarith only [sq_nonneg (σ - t)]
      have hm := mul_le_mul_of_nonneg_left hamgm
        (mul_nonneg hσ.le ht.le)
      nlinarith only [hm]

/-- After removing the Dirichlet sine kernel, the remaining `t`-sine part is
absolutely bounded by `σ / (2T)`.  Together with the sine-tail estimate this
gives the quantitative conditional tail needed for the Poisson component. -/
theorem abs_liuPanPerronPoissonSineTail_le
    {σ a T S : ℝ} (hσ : 0 < σ) (ha : a ≠ 0)
    (hT : 0 < T) (hTS : T ≤ S) :
    |∫ t in T..S,
        t * Real.sin (a * t) / (σ ^ 2 + t ^ 2)| ≤
      3 / (|a| * T) + σ / (2 * T) := by
  let f : ℝ → ℝ :=
    fun t => t * Real.sin (a * t) / (σ ^ 2 + t ^ 2)
  let g : ℝ → ℝ := fun t => Real.sin (a * t) / t
  have hf : IntervalIntegrable f MeasureTheory.volume T S := by
    apply Continuous.intervalIntegrable
    dsimp [f]
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    positivity
  have hg : IntervalIntegrable g MeasureTheory.volume T S := by
    apply ContinuousOn.intervalIntegrable_of_Icc hTS
    dsimp [g]
    exact (by
      fun_prop : ContinuousOn (fun t : ℝ => Real.sin (a * t))
        (Set.Icc T S)).div continuousOn_id fun t ht =>
          (hT.trans_le ht.1).ne'
  have hdiffInt : IntervalIntegrable (fun t => f t - g t)
      MeasureTheory.volume T S :=
    hf.sub hg
  have hboundInt : IntervalIntegrable
      (fun t : ℝ => σ / (2 * t ^ 2)) MeasureTheory.volume T S := by
    apply ContinuousOn.intervalIntegrable_of_Icc hTS
    exact continuousOn_const.div
      (continuousOn_const.mul (continuousOn_id.pow 2)) fun t ht =>
        mul_ne_zero (by norm_num)
          (pow_ne_zero 2 (hT.trans_le ht.1).ne')
  have hdiff :
      |∫ t in T..S, f t - g t| ≤ σ / (2 * T) := by
    have hS : 0 < S := hT.trans_le hTS
    calc
      |∫ t in T..S, f t - g t| =
          ‖∫ t in T..S, f t - g t‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ ∫ t in T..S, ‖f t - g t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hTS
      _ ≤ ∫ t in T..S, σ / (2 * t ^ 2) := by
        refine intervalIntegral.integral_mono_on hTS hdiffInt.norm
          hboundInt ?_
        intro t ht
        rw [Real.norm_eq_abs]
        exact abs_liuPanPerronPoissonSineIntegrand_sub_le hσ
          (hT.trans_le ht.1)
      _ = (σ / 2) * (T⁻¹ - S⁻¹) := by
        have hfun :
            (fun t : ℝ => σ / (2 * t ^ 2)) =
              fun t => (σ / 2) * (t ^ 2)⁻¹ := by
          funext t
          field_simp
        rw [hfun]
        rw [intervalIntegral.integral_const_mul,
          liuPanIntervalIntegralInvSq_of_pos hT hTS]
      _ ≤ (σ / 2) * T⁻¹ := by
        exact mul_le_mul_of_nonneg_left
          (sub_le_self _ (inv_nonneg.mpr hS.le)) (by positivity)
      _ = σ / (2 * T) := by field_simp
  have hsin :
      |∫ t in T..S, g t| ≤ 3 / (|a| * T) := by
    simpa [g] using LiuPanPerronSineTailBound a T S ha hT hTS
  have heq :
      (∫ t in T..S, f t) =
        (∫ t in T..S, g t) + ∫ t in T..S, f t - g t := by
    rw [intervalIntegral.integral_sub hf hg]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hsin hdiff)

private theorem abs_intervalIntegral_sub_limit_le_of_inv_tail
    (f : ℝ → ℝ) {C L T : ℝ}
    (hfi : ∀ a b : ℝ,
      IntervalIntegrable f MeasureTheory.volume a b)
    (hlim : Filter.Tendsto
      (fun S : ℝ => ∫ t in (0 : ℝ)..S, f t)
      Filter.atTop (nhds L))
    (htail : ∀ {S : ℝ}, T ≤ S →
      |∫ t in T..S, f t| ≤ C / T) :
    |(∫ t in (0 : ℝ)..T, f t) - L| ≤ C / T := by
  have hconst :
      Filter.Tendsto (fun _ : ℝ => ∫ t in (0 : ℝ)..T, f t)
        Filter.atTop (nhds (∫ t in (0 : ℝ)..T, f t)) :=
    tendsto_const_nhds
  have habs := (hlim.sub hconst).abs
  have htailLim :
      Filter.Tendsto (fun S : ℝ => |∫ t in T..S, f t|)
        Filter.atTop
        (nhds |L - ∫ t in (0 : ℝ)..T, f t|) := by
    apply habs.congr'
    filter_upwards with S
    congr 1
    exact intervalIntegral.integral_interval_sub_left (hfi 0 S) (hfi 0 T)
  have hbound : ∀ᶠ S : ℝ in Filter.atTop,
      |∫ t in T..S, f t| ≤ C / T := by
    filter_upwards [Filter.eventually_ge_atTop T] with S hTS
    exact htail hTS
  have hle := le_of_tendsto htailLim hbound
  rwa [abs_sub_comm] at hle

/-- The finite cosine integrals have an improper limit.  Its explicit Poisson
value is a separate normalization step. -/
theorem exists_liuPanPerronPoissonCosineIntegralLimit
    {σ a : ℝ} (hσ : 0 < σ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun T : ℝ =>
        ∫ t in (0 : ℝ)..T,
          σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2))
      Filter.atTop (nhds L) := by
  let f : ℝ → ℝ :=
    fun t => σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2)
  have hfi : ∀ x y : ℝ,
      IntervalIntegrable f MeasureTheory.volume x y := by
    intro x y
    apply Continuous.intervalIntegrable
    dsimp [f]
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    positivity
  have hcauchy :
      CauchySeq (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t) := by
    apply cauchySeq_intervalIntegral_of_inv_tail f σ hσ.le hfi
    intro T S hT hTS
    simpa [f] using
      abs_liuPanPerronPoissonCosineTail_le hσ hT hTS
  simpa [f] using cauchySeq_tendsto_of_complete hcauchy

/-- Any limit of the cosine component inherits the explicit `σ / T` error. -/
theorem abs_liuPanPerronPoissonCosineIntegral_sub_limit_le
    {σ a L T : ℝ} (hσ : 0 < σ) (hT : 0 < T)
    (hlim : Filter.Tendsto
      (fun S : ℝ =>
        ∫ t in (0 : ℝ)..S,
          σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2))
      Filter.atTop (nhds L)) :
    |(∫ t in (0 : ℝ)..T,
        σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2)) - L| ≤
      σ / T := by
  let f : ℝ → ℝ :=
    fun t => σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2)
  have hfi : ∀ x y : ℝ,
      IntervalIntegrable f MeasureTheory.volume x y := by
    intro x y
    apply Continuous.intervalIntegrable
    dsimp [f]
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    positivity
  apply abs_intervalIntegral_sub_limit_le_of_inv_tail f hfi
    (by simpa [f] using hlim)
  intro S hTS
  simpa [f] using
    abs_liuPanPerronPoissonCosineTail_le hσ hT hTS

/-- The finite `t`-sine integrals have an improper limit for every nonzero
frequency.  The remaining Poisson identity is the exact evaluation of this
limit. -/
theorem exists_liuPanPerronPoissonSineIntegralLimit
    {σ a : ℝ} (hσ : 0 < σ) (ha : a ≠ 0) :
    ∃ L : ℝ, Filter.Tendsto
      (fun T : ℝ =>
        ∫ t in (0 : ℝ)..T,
          t * Real.sin (a * t) / (σ ^ 2 + t ^ 2))
      Filter.atTop (nhds L) := by
  let f : ℝ → ℝ :=
    fun t => t * Real.sin (a * t) / (σ ^ 2 + t ^ 2)
  let C : ℝ := 3 / |a| + σ / 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hfi : ∀ x y : ℝ,
      IntervalIntegrable f MeasureTheory.volume x y := by
    intro x y
    apply Continuous.intervalIntegrable
    dsimp [f]
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    positivity
  have hcauchy :
      CauchySeq (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t) := by
    apply cauchySeq_intervalIntegral_of_inv_tail f C hC hfi
    intro T S hT hTS
    have h :=
      abs_liuPanPerronPoissonSineTail_le hσ ha hT hTS
    change
      |∫ t in T..S,
          t * Real.sin (a * t) / (σ ^ 2 + t ^ 2)| ≤
        (3 / |a| + σ / 2) / T
    calc
      |∫ t in T..S,
          t * Real.sin (a * t) / (σ ^ 2 + t ^ 2)| ≤
          3 / (|a| * T) + σ / (2 * T) := h
      _ = (3 / |a| + σ / 2) / T := by
        field_simp [abs_ne_zero.mpr ha]
  simpa [f] using cauchySeq_tendsto_of_complete hcauchy

/-- Any limit of the `t`-sine component inherits the sine-tail error plus the
absolutely convergent Poisson correction. -/
theorem abs_liuPanPerronPoissonSineIntegral_sub_limit_le
    {σ a L T : ℝ} (hσ : 0 < σ) (ha : a ≠ 0) (hT : 0 < T)
    (hlim : Filter.Tendsto
      (fun S : ℝ =>
        ∫ t in (0 : ℝ)..S,
          t * Real.sin (a * t) / (σ ^ 2 + t ^ 2))
      Filter.atTop (nhds L)) :
    |(∫ t in (0 : ℝ)..T,
        t * Real.sin (a * t) / (σ ^ 2 + t ^ 2)) - L| ≤
      3 / (|a| * T) + σ / (2 * T) := by
  let f : ℝ → ℝ :=
    fun t => t * Real.sin (a * t) / (σ ^ 2 + t ^ 2)
  let C : ℝ := 3 / |a| + σ / 2
  have hfi : ∀ x y : ℝ,
      IntervalIntegrable f MeasureTheory.volume x y := by
    intro x y
    apply Continuous.intervalIntegrable
    dsimp [f]
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    positivity
  have hbound :
      |(∫ t in (0 : ℝ)..T, f t) - L| ≤ C / T := by
    apply abs_intervalIntegral_sub_limit_le_of_inv_tail f hfi
      (by simpa [f] using hlim)
    intro S hTS
    have h :=
      abs_liuPanPerronPoissonSineTail_le hσ ha hT hTS
    change
      |∫ t in T..S,
          t * Real.sin (a * t) / (σ ^ 2 + t ^ 2)| ≤
        (3 / |a| + σ / 2) / T
    calc
      |∫ t in T..S,
          t * Real.sin (a * t) / (σ ^ 2 + t ^ 2)| ≤
          3 / (|a| * T) + σ / (2 * T) := h
      _ = (3 / |a| + σ / 2) / T := by
        field_simp [abs_ne_zero.mpr ha]
  change
    |(∫ t in (0 : ℝ)..T,
      t * Real.sin (a * t) / (σ ^ 2 + t ^ 2)) - L| ≤
      3 / (|a| * T) + σ / (2 * T)
  calc
    |(∫ t in (0 : ℝ)..T,
      t * Real.sin (a * t) / (σ ^ 2 + t ^ 2)) - L| ≤
        C / T := by simpa [f] using hbound
    _ = 3 / (|a| * T) + σ / (2 * T) := by
      dsimp [C]
      field_simp [abs_ne_zero.mpr ha]

/-- The complex integrand whose real part is the sum of the two Poisson
components in the paired Perron kernel. -/
noncomputable def liuPanPerronPoissonContourIntegrand
    (σ a : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (((a : ℂ) * Complex.I) * s) /
    ((σ : ℂ) + Complex.I * s)

private theorem liuPanPerronPoissonContourIntegrand_sub_residue_isBigO
    (σ a : ℝ) :
    (fun s : ℂ =>
      liuPanPerronPoissonContourIntegrand σ a s -
        ((Complex.exp (-(a * σ)) : ℂ) / Complex.I) /
          (s - (σ : ℂ) * Complex.I)) =O[
      𝓝[≠] ((σ : ℂ) * Complex.I)] (1 : ℂ → ℂ) := by
  let p : ℂ := (σ : ℂ) * Complex.I
  let E : ℂ → ℂ :=
    fun s => Complex.exp (((a : ℂ) * Complex.I) * s)
  have hE : DifferentiableAt ℂ E p := by
    dsimp [E]
    fun_prop
  have hsub :
      (fun s : ℂ => E s - E p) =O[𝓝 p] (fun s => s - p) :=
    hE.isBigO_sub
  have hsub' :
      (fun s : ℂ => E s - E p) =O[𝓝[≠] p] (fun s => s - p) :=
    hsub.mono inf_le_left
  have htheta :
      (fun s : ℂ => s - p) =Θ[𝓝[≠] p] (fun s => s - p) :=
    isTheta_refl _ _
  have hquot := hsub'.mul htheta.inv.isBigO
  have hquot' :
      (fun s : ℂ => (E s - E p) * (s - p)⁻¹) =O[𝓝[≠] p]
        (fun s => (s - p) * (s - p)⁻¹) :=
    hquot
  have hright :
      (fun s : ℂ => (s - p) * (s - p)⁻¹) =ᶠ[𝓝[≠] p]
        (1 : ℂ → ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact mul_inv_cancel₀ (sub_ne_zero.mpr hs)
  have hbase :
      (fun s : ℂ => (E s - E p) * (s - p)⁻¹) =O[𝓝[≠] p]
        (1 : ℂ → ℂ) :=
    hquot'.congr' Filter.EventuallyEq.rfl hright
  have hscaled := hbase.const_mul_left ((Complex.I)⁻¹)
  refine hscaled.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s hs
  dsimp [E, p]
  unfold liuPanPerronPoissonContourIntegrand
  rw [show (σ : ℂ) + Complex.I * s =
      Complex.I * (s - (σ : ℂ) * Complex.I) by
    ring_nf
    rw [Complex.I_sq]
    norm_num]
  rw [show
      Complex.exp (((a : ℂ) * Complex.I) * ((σ : ℂ) * Complex.I)) =
        (Complex.exp (-(a * σ)) : ℂ) by
    congr 1
    ring_nf
    rw [Complex.I_sq]
    norm_num]
  field_simp [Complex.I_ne_zero, sub_ne_zero.mpr hs]

/-- The upper rectangle encloses the sole pole of the combined Poisson
integrand, with its residue evaluated exactly. -/
theorem liuPanPerronPoissonUpperRectangle_residue
    {σ a R : ℝ} (hσ : 0 < σ) (hσR : σ < R) :
    RectangleIntegral'
        (liuPanPerronPoissonContourIntegrand σ a)
        (-R : ℂ) ((R : ℂ) + (R : ℂ) * Complex.I) =
      (Complex.exp (-(a * σ)) : ℂ) / Complex.I := by
  let p : ℂ := (σ : ℂ) * Complex.I
  let A : ℂ := (Complex.exp (-(a * σ)) : ℂ) / Complex.I
  have hR : 0 < R := hσ.trans hσR
  apply ResidueTheoremOnRectangleWithSimplePole' (p := p) (A := A)
  · simp
    linarith
  · simpa using hR.le
  · rw [rectangle_mem_nhds_iff]
    simp only [Complex.mem_reProdIm]
    constructor
    · rw [Set.uIoo_of_le (by
        simp
        linarith : ((-R : ℂ).re) ≤
          (((R : ℂ) + (R : ℂ) * Complex.I).re))]
      dsimp [p]
      simp
      linarith
    · rw [Set.uIoo_of_le (by
        simp [hR.le] : ((-R : ℂ).im) ≤
          (((R : ℂ) + (R : ℂ) * Complex.I).im))]
      dsimp [p]
      simp
      exact ⟨hσ, hσR⟩
  · apply DifferentiableOn.div
    · fun_prop
    · fun_prop
    · intro s hs
      rw [show (σ : ℂ) + Complex.I * s = Complex.I * (s - p) by
        dsimp [p]
        ring_nf
        rw [Complex.I_sq]
        norm_num]
      exact mul_ne_zero Complex.I_ne_zero
        (sub_ne_zero.mpr (by simpa using hs.2))
  · change
      (fun s : ℂ =>
        liuPanPerronPoissonContourIntegrand σ a s -
          ((Complex.exp (-(a * σ)) : ℂ) / Complex.I) /
            (s - (σ : ℂ) * Complex.I)) =O[
        𝓝[≠] ((σ : ℂ) * Complex.I)] (1 : ℂ → ℂ)
    exact
      liuPanPerronPoissonContourIntegrand_sub_residue_isBigO σ a

/-- Pairing the contour integrand on the real axis recovers exactly the sum of
the cosine and `t`-sine Poisson components. -/
theorem liuPanPerronPoissonContourIntegrand_add_neg
    {σ : ℝ} (hσ : 0 < σ) (a t : ℝ) :
    liuPanPerronPoissonContourIntegrand σ a (t : ℂ) +
        liuPanPerronPoissonContourIntegrand σ a (-t : ℂ) =
      ((2 * (σ * Real.cos (a * t) + t * Real.sin (a * t)) /
          (σ ^ 2 + t ^ 2) : ℝ) : ℂ) := by
  unfold liuPanPerronPoissonContourIntegrand
  rw [show ((σ : ℂ) + Complex.I * (t : ℂ)) =
      liuPanPerronLine σ t by
    unfold liuPanPerronLine
    ring]
  rw [show ((σ : ℂ) + Complex.I * (-t : ℂ)) =
      liuPanPerronLine σ (-t) by
    unfold liuPanPerronLine
    push_cast
    ring]
  rw [show ((a : ℂ) * Complex.I) * (t : ℂ) =
      ((a * t : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [show ((a : ℂ) * Complex.I) * (-t : ℂ) =
      ((-(a * t) : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  norm_cast
  rw [Real.cos_neg, Real.sin_neg]
  simp only [div_eq_mul_inv,
    liuPanPerronLine_inv_eq σ t hσ.ne',
    liuPanPerronLine_inv_eq σ (-t) hσ.ne', neg_sq]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- Unnormalizing the residue theorem gives the exact boundary integral
required before estimating the three non-real sides of the square. -/
theorem liuPanPerronPoissonUpperRectangle_boundary
    {σ a R : ℝ} (hσ : 0 < σ) (hσR : σ < R) :
    RectangleIntegral
        (liuPanPerronPoissonContourIntegrand σ a)
        (-R : ℂ) ((R : ℂ) + (R : ℂ) * Complex.I) =
      (2 * Real.pi * Real.exp (-(a * σ)) : ℝ) := by
  have h :=
    liuPanPerronPoissonUpperRectangle_residue (a := a) hσ hσR
  change (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      RectangleIntegral (liuPanPerronPoissonContourIntegrand σ a)
        (-R : ℂ) ((R : ℂ) + (R : ℂ) * Complex.I) =
      (Complex.exp (-(a * σ)) : ℂ) / Complex.I at h
  calc
    RectangleIntegral (liuPanPerronPoissonContourIntegrand σ a)
        (-R : ℂ) ((R : ℂ) + (R : ℂ) * Complex.I) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          ((1 / (2 * (Real.pi : ℂ) * Complex.I)) *
            RectangleIntegral
              (liuPanPerronPoissonContourIntegrand σ a)
              (-R : ℂ) ((R : ℂ) + (R : ℂ) * Complex.I)) := by
      field_simp [Real.pi_ne_zero, Complex.I_ne_zero]
    _ = (2 * (Real.pi : ℂ) * Complex.I) *
        ((Complex.exp (-(a * σ)) : ℂ) / Complex.I) := by
      rw [h]
    _ = (2 * Real.pi * Real.exp (-(a * σ)) : ℝ) := by
      rw [show -(↑a * ↑σ) = ((-(a * σ) : ℝ) : ℂ) by
        push_cast
        ring]
      rw [← Complex.ofReal_exp]
      push_cast
      field_simp [Complex.I_ne_zero]

private theorem norm_liuPanPerronPoissonContourIntegrand_horizontal_le
    {σ a R x : ℝ} (hσR : σ < R) :
    ‖liuPanPerronPoissonContourIntegrand σ a
        ((x : ℂ) + (R : ℂ) * Complex.I)‖ ≤
      Real.exp (-a * R) / (R - σ) := by
  unfold liuPanPerronPoissonContourIntegrand
  rw [norm_div, Complex.norm_exp]
  have hnum :
      ((((a : ℂ) * Complex.I) *
        ((x : ℂ) + (R : ℂ) * Complex.I)).re) = -a * R := by
    simp
  rw [hnum]
  have hdenre :
      ((σ : ℂ) + Complex.I *
        ((x : ℂ) + (R : ℂ) * Complex.I)).re = σ - R := by
    simp
    ring
  have hre := Complex.abs_re_le_norm
    ((σ : ℂ) + Complex.I *
      ((x : ℂ) + (R : ℂ) * Complex.I))
  rw [hdenre, abs_of_neg (sub_neg.mpr hσR)] at hre
  have hre' : R - σ ≤
      ‖(σ : ℂ) + Complex.I *
        ((x : ℂ) + (R : ℂ) * Complex.I)‖ := by
    linarith
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le
    (sub_pos.mpr hσR) hre'

private theorem norm_liuPanPerronPoissonHorizontalIntegral_raw_le
    {σ a R : ℝ} (hR : 0 < R) (hσR : σ < R) :
    ‖HIntegral (liuPanPerronPoissonContourIntegrand σ a) (-R) R R‖ ≤
      (Real.exp (-a * R) / (R - σ)) * (2 * R) := by
  unfold HIntegral
  calc
    ‖∫ x in -R..R,
        liuPanPerronPoissonContourIntegrand σ a
          ((x : ℂ) + (R : ℂ) * Complex.I)‖ ≤
        (Real.exp (-a * R) / (R - σ)) * |R - (-R)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
      filter_upwards [] with x
      intro _hx
      exact norm_liuPanPerronPoissonContourIntegrand_horizontal_le hσR
    _ = (Real.exp (-a * R) / (R - σ)) * (2 * R) := by
      rw [show R - -R = 2 * R by ring,
        abs_of_pos (mul_pos (by norm_num) hR)]

/-- The top edge of the Poisson rectangle has an explicit exponentially
decaying bound once its height is more than twice the pole height. -/
theorem norm_liuPanPerronPoissonHorizontalIntegral_le
    {σ a R : ℝ} (hσ : 0 ≤ σ) (hR : 2 * σ < R) :
    ‖HIntegral (liuPanPerronPoissonContourIntegrand σ a) (-R) R R‖ ≤
      4 * Real.exp (-a * R) := by
  have hRpos : 0 < R :=
    lt_of_le_of_lt (mul_nonneg (by norm_num) hσ) hR
  have hσR : σ < R := by linarith
  calc
    _ ≤ (Real.exp (-a * R) / (R - σ)) * (2 * R) :=
      norm_liuPanPerronPoissonHorizontalIntegral_raw_le hRpos hσR
    _ = 2 * Real.exp (-a * R) * (R / (R - σ)) := by
      field_simp
    _ ≤ 2 * Real.exp (-a * R) * 2 := by
      gcongr
      rw [div_le_iff₀ (sub_pos.mpr hσR)]
      linarith
    _ = 4 * Real.exp (-a * R) := by ring

private theorem norm_liuPanPerronPoissonContourIntegrand_vertical_right_le
    {σ a R y : ℝ} (hR : 0 < R) :
    ‖liuPanPerronPoissonContourIntegrand σ a
        ((R : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.exp (-a * y) / R := by
  unfold liuPanPerronPoissonContourIntegrand
  rw [norm_div, Complex.norm_exp]
  have hnum :
      ((((a : ℂ) * Complex.I) *
        ((R : ℂ) + (y : ℂ) * Complex.I)).re) = -a * y := by
    simp
  rw [hnum]
  have hdenim :
      ((σ : ℂ) + Complex.I *
        ((R : ℂ) + (y : ℂ) * Complex.I)).im = R := by
    simp
  have him := Complex.abs_im_le_norm
    ((σ : ℂ) + Complex.I *
      ((R : ℂ) + (y : ℂ) * Complex.I))
  rw [hdenim, abs_of_pos hR] at him
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hR him

private theorem norm_liuPanPerronPoissonContourIntegrand_vertical_left_le
    {σ a R y : ℝ} (hR : 0 < R) :
    ‖liuPanPerronPoissonContourIntegrand σ a
        (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.exp (-a * y) / R := by
  unfold liuPanPerronPoissonContourIntegrand
  rw [norm_div, Complex.norm_exp]
  have hnum :
      ((((a : ℂ) * Complex.I) *
        (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I)).re) = -a * y := by
    simp
  rw [hnum]
  have hdenim :
      ((σ : ℂ) + Complex.I *
        (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I)).im = -R := by
    simp
  have him := Complex.abs_im_le_norm
    ((σ : ℂ) + Complex.I *
      (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I))
  rw [hdenim, abs_neg, abs_of_pos hR] at him
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hR him

private theorem liuPanPerronPoissonVerticalMajorantIntegral
    {a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    (∫ y in (0 : ℝ)..R, Real.exp (-a * y) / R) =
      (1 - Real.exp (-a * R)) / (a * R) := by
  have hfun : (fun y : ℝ => Real.exp (-a * y) / R) =
      fun y => (a * R)⁻¹ * (a * Real.exp (-a * y)) := by
    funext y
    field_simp
  rw [hfun, intervalIntegral.integral_const_mul,
    liuPanIntervalIntegralExpNegMulConstMulSelf]
  simp only [mul_zero, Real.exp_zero]
  field_simp

/-- The right vertical edge of the Poisson rectangle is bounded by
`1 / (aR)`. -/
theorem norm_liuPanPerronPoissonVerticalRightIntegral_le
    {σ a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    ‖VIntegral (liuPanPerronPoissonContourIntegrand σ a) R 0 R‖ ≤
      1 / (a * R) := by
  have hgint : IntervalIntegrable
      (fun y : ℝ => Real.exp (-a * y) / R)
      MeasureTheory.volume 0 R := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold VIntegral
  rw [norm_smul, Complex.norm_I, one_mul]
  calc
    ‖∫ y in (0 : ℝ)..R,
        liuPanPerronPoissonContourIntegrand σ a
          ((R : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        ∫ y in (0 : ℝ)..R, Real.exp (-a * y) / R := by
      apply intervalIntegral.norm_integral_le_of_norm_le hR.le
      · filter_upwards [] with y
        intro _hy
        exact
          norm_liuPanPerronPoissonContourIntegrand_vertical_right_le hR
      · exact hgint
    _ = (1 - Real.exp (-a * R)) / (a * R) :=
      liuPanPerronPoissonVerticalMajorantIntegral ha hR
    _ ≤ 1 / (a * R) := by
      apply div_le_div_of_nonneg_right _ (mul_nonneg ha.le hR.le)
      exact sub_le_self 1 (Real.exp_pos _).le

/-- The left vertical edge of the Poisson rectangle is bounded by
`1 / (aR)`. -/
theorem norm_liuPanPerronPoissonVerticalLeftIntegral_le
    {σ a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    ‖VIntegral (liuPanPerronPoissonContourIntegrand σ a) (-R) 0 R‖ ≤
      1 / (a * R) := by
  have hgint : IntervalIntegrable
      (fun y : ℝ => Real.exp (-a * y) / R)
      MeasureTheory.volume 0 R := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold VIntegral
  rw [norm_smul, Complex.norm_I, one_mul]
  calc
    ‖∫ y in (0 : ℝ)..R,
        liuPanPerronPoissonContourIntegrand σ a
          (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        ∫ y in (0 : ℝ)..R, Real.exp (-a * y) / R := by
      apply intervalIntegral.norm_integral_le_of_norm_le hR.le
      · filter_upwards [] with y
        intro _hy
        exact
          norm_liuPanPerronPoissonContourIntegrand_vertical_left_le hR
      · exact hgint
    _ = (1 - Real.exp (-a * R)) / (a * R) :=
      liuPanPerronPoissonVerticalMajorantIntegral ha hR
    _ ≤ 1 / (a * R) := by
      apply div_le_div_of_nonneg_right _ (mul_nonneg ha.le hR.le)
      exact sub_le_self 1 (Real.exp_pos _).le

/-- The top edge of the upper Poisson rectangle vanishes as its height tends
to infinity. -/
theorem tendsto_liuPanPerronPoissonHorizontalIntegral_atTop
    {σ a : ℝ} (hσ : 0 ≤ σ) (ha : 0 < a) :
    Filter.Tendsto
      (fun R : ℝ => HIntegral
        (liuPanPerronPoissonContourIntegrand σ a) (-R) R R)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [eventually_gt_atTop (2 * σ)] with R hR
    exact norm_liuPanPerronPoissonHorizontalIntegral_le hσ hR
  · have hscale : Filter.Tendsto (fun R : ℝ => a * R)
        Filter.atTop Filter.atTop :=
      (Filter.tendsto_const_mul_atTop_of_pos ha).2 Filter.tendsto_id
    have hexp : Filter.Tendsto (fun R : ℝ => Real.exp (-(a * R)))
        Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
    simpa [neg_mul] using
      (tendsto_const_nhds.mul hexp : Filter.Tendsto
        (fun R : ℝ => 4 * Real.exp (-(a * R)))
        Filter.atTop (nhds (4 * 0)))

/-- The right vertical edge of the upper Poisson rectangle vanishes as its
width tends to infinity. -/
theorem tendsto_liuPanPerronPoissonVerticalRightIntegral_atTop
    {σ a : ℝ} (ha : 0 < a) :
    Filter.Tendsto
      (fun R : ℝ => VIntegral
        (liuPanPerronPoissonContourIntegrand σ a) R 0 R)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [eventually_gt_atTop 0] with R hR
    exact norm_liuPanPerronPoissonVerticalRightIntegral_le ha hR
  · have hlim : Filter.Tendsto (fun R : ℝ => (1 / a) * R⁻¹)
        Filter.atTop (nhds 0) := by
      simpa using
        (tendsto_const_nhds.mul tendsto_inv_atTop_zero : Filter.Tendsto
          (fun R : ℝ => (1 / a) * R⁻¹) Filter.atTop
          (nhds ((1 / a) * 0)))
    simpa [div_eq_mul_inv, mul_inv, mul_comm] using hlim

/-- The left vertical edge of the upper Poisson rectangle vanishes as its
width tends to infinity. -/
theorem tendsto_liuPanPerronPoissonVerticalLeftIntegral_atTop
    {σ a : ℝ} (ha : 0 < a) :
    Filter.Tendsto
      (fun R : ℝ => VIntegral
        (liuPanPerronPoissonContourIntegrand σ a) (-R) 0 R)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [eventually_gt_atTop 0] with R hR
    exact norm_liuPanPerronPoissonVerticalLeftIntegral_le ha hR
  · have hlim : Filter.Tendsto (fun R : ℝ => (1 / a) * R⁻¹)
        Filter.atTop (nhds 0) := by
      simpa using
        (tendsto_const_nhds.mul tendsto_inv_atTop_zero : Filter.Tendsto
          (fun R : ℝ => (1 / a) * R⁻¹) Filter.atTop
          (nhds ((1 / a) * 0)))
    simpa [div_eq_mul_inv, mul_inv, mul_comm] using hlim

/-- Sending the three non-real edges of the upper rectangle to infinity
identifies the whole real-axis contour integral. -/
theorem tendsto_liuPanPerronPoissonRealIntegral_atTop
    {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) :
    Filter.Tendsto
      (fun R : ℝ => HIntegral
        (liuPanPerronPoissonContourIntegrand σ a) (-R) R 0)
      Filter.atTop
      (nhds ((2 * Real.pi * Real.exp (-(a * σ)) : ℝ) : ℂ)) := by
  have htop :=
    tendsto_liuPanPerronPoissonHorizontalIntegral_atTop hσ.le ha
  have hright :=
    tendsto_liuPanPerronPoissonVerticalRightIntegral_atTop
      (σ := σ) ha
  have hleft :=
    tendsto_liuPanPerronPoissonVerticalLeftIntegral_atTop
      (σ := σ) ha
  have hlimit :
      Filter.Tendsto
        (fun R : ℝ =>
          ((2 * Real.pi * Real.exp (-(a * σ)) : ℝ) : ℂ) +
            HIntegral (liuPanPerronPoissonContourIntegrand σ a)
              (-R) R R -
            VIntegral (liuPanPerronPoissonContourIntegrand σ a)
              R 0 R +
            VIntegral (liuPanPerronPoissonContourIntegrand σ a)
              (-R) 0 R)
        Filter.atTop
        (nhds ((2 * Real.pi * Real.exp (-(a * σ)) : ℝ) : ℂ)) := by
    convert ((tendsto_const_nhds.add htop).sub hright).add hleft using 1
    all_goals simp
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop σ] with R hσR
  have hboundary :=
    liuPanPerronPoissonUpperRectangle_boundary
      (a := a) hσ hσR
  have hboundary' :
      HIntegral (liuPanPerronPoissonContourIntegrand σ a) (-R) R 0 -
          HIntegral (liuPanPerronPoissonContourIntegrand σ a) (-R) R R +
          VIntegral (liuPanPerronPoissonContourIntegrand σ a) R 0 R -
          VIntegral (liuPanPerronPoissonContourIntegrand σ a) (-R) 0 R =
        ((2 * Real.pi * Real.exp (-(a * σ)) : ℝ) : ℂ) := by
    simpa [RectangleIntegral] using hboundary
  rw [← hboundary']
  ring

/-- Pairing the negative and positive halves of the real edge gives the
finite cosine-plus-sine Poisson integral exactly. -/
theorem liuPanPerronPoissonRealIntegral_eq_paired
    {σ : ℝ} (hσ : 0 < σ) (a R : ℝ) :
    HIntegral (liuPanPerronPoissonContourIntegrand σ a) (-R) R 0 =
      ∫ t in 0..R,
        ((2 * (σ * Real.cos (a * t) + t * Real.sin (a * t)) /
          (σ ^ 2 + t ^ 2) : ℝ) : ℂ) := by
  let f : ℝ → ℂ :=
    fun t => liuPanPerronPoissonContourIntegrand σ a (t : ℂ)
  have hf : Continuous f := by
    dsimp only [f]
    unfold liuPanPerronPoissonContourIntegrand
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t
      rw [show (σ : ℂ) + Complex.I * (t : ℂ) =
          liuPanPerronLine σ t by
        unfold liuPanPerronLine
        ring]
      exact liuPanPerronLine_ne_zero hσ t
  have hfneg : IntervalIntegrable f MeasureTheory.volume (-R) 0 :=
    hf.intervalIntegrable (-R) 0
  have hfpos : IntervalIntegrable f MeasureTheory.volume 0 R :=
    hf.intervalIntegrable 0 R
  have href : IntervalIntegrable (fun t => f (-t))
      MeasureTheory.volume 0 R := by
    have hc : Continuous (fun t => f (-t)) := by fun_prop
    exact hc.intervalIntegrable 0 R
  have hpair :
      (∫ t in -R..R, f t) = ∫ t in 0..R, (f t + f (-t)) := by
    calc
      (∫ t in -R..R, f t) =
          (∫ t in -R..0, f t) + ∫ t in 0..R, f t :=
        (intervalIntegral.integral_add_adjacent_intervals
          hfneg hfpos).symm
      _ = (∫ t in 0..R, f (-t)) + ∫ t in 0..R, f t := by
        rw [intervalIntegral.integral_comp_neg]
        norm_num
      _ = ∫ t in 0..R, (f (-t) + f t) :=
        (intervalIntegral.integral_add href hfpos).symm
      _ = ∫ t in 0..R, (f t + f (-t)) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        exact add_comm _ _
  unfold HIntegral
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  change (∫ t in -R..R, f t) = _
  rw [hpair]
  apply intervalIntegral.integral_congr
  intro t _ht
  simpa [f] using liuPanPerronPoissonContourIntegrand_add_neg hσ a t

private theorem liuPanPerronPoissonUpperRectangle_neg_sigma_boundary
    {σ a R : ℝ} (hσ : 0 < σ) (hR : 0 ≤ R) :
    RectangleIntegral
        (liuPanPerronPoissonContourIntegrand (-σ) a)
        (-R : ℂ) ((R : ℂ) + (R : ℂ) * Complex.I) = 0 := by
  apply HolomorphicOn.vanishesOnRectangle
    (U := Complex.Rectangle (-R : ℂ)
      ((R : ℂ) + (R : ℂ) * Complex.I))
  · apply DifferentiableOn.div
    · fun_prop
    · fun_prop
    · intro s hs hzero
      have hre := congrArg Complex.re hzero
      rw [Complex.Rectangle, Complex.mem_reProdIm] at hs
      have himem : s.im ∈ Set.uIcc (0 : ℝ) R := by
        simpa using hs.2
      have him : 0 ≤ s.im := by
        rw [Set.uIcc_of_le hR] at himem
        exact himem.1
      simp at hre
      linarith
  · exact Set.Subset.rfl

private theorem tendsto_liuPanPerronPoissonHorizontalIntegral_neg_sigma_atTop
    {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) :
    Filter.Tendsto
      (fun R : ℝ => HIntegral
        (liuPanPerronPoissonContourIntegrand (-σ) a) (-R) R R)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [eventually_gt_atTop 0] with R hR
    have hraw :=
      norm_liuPanPerronPoissonHorizontalIntegral_raw_le
        (σ := -σ) (a := a) hR (by linarith)
    calc
      ‖HIntegral (liuPanPerronPoissonContourIntegrand (-σ) a)
          (-R) R R‖ ≤
          (Real.exp (-a * R) / (R - -σ)) * (2 * R) := hraw
      _ ≤ 2 * Real.exp (-a * R) := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ (by linarith : 0 < R - -σ)).2
        nlinarith [Real.exp_pos (-a * R)]
  · have hscale : Filter.Tendsto (fun R : ℝ => a * R)
        Filter.atTop Filter.atTop :=
      (Filter.tendsto_const_mul_atTop_of_pos ha).2 Filter.tendsto_id
    have hexp : Filter.Tendsto (fun R : ℝ => Real.exp (-(a * R)))
        Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
    simpa [neg_mul] using
      (tendsto_const_nhds.mul hexp : Filter.Tendsto
        (fun R : ℝ => 2 * Real.exp (-(a * R)))
        Filter.atTop (nhds (2 * 0)))

private theorem tendsto_liuPanPerronPoissonRealIntegral_neg_sigma_atTop
    {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) :
    Filter.Tendsto
      (fun R : ℝ => HIntegral
        (liuPanPerronPoissonContourIntegrand (-σ) a) (-R) R 0)
      Filter.atTop (nhds 0) := by
  have htop :=
    tendsto_liuPanPerronPoissonHorizontalIntegral_neg_sigma_atTop hσ ha
  have hright :=
    tendsto_liuPanPerronPoissonVerticalRightIntegral_atTop
      (σ := -σ) ha
  have hleft :=
    tendsto_liuPanPerronPoissonVerticalLeftIntegral_atTop
      (σ := -σ) ha
  have hlimit :
      Filter.Tendsto
        (fun R : ℝ =>
          HIntegral (liuPanPerronPoissonContourIntegrand (-σ) a)
              (-R) R R -
            VIntegral (liuPanPerronPoissonContourIntegrand (-σ) a)
              R 0 R +
            VIntegral (liuPanPerronPoissonContourIntegrand (-σ) a)
              (-R) 0 R)
        Filter.atTop (nhds 0) := by
    simpa using (htop.sub hright).add hleft
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hboundary :=
    liuPanPerronPoissonUpperRectangle_neg_sigma_boundary
      (a := a) hσ hR.le
  have hboundary' :
      HIntegral (liuPanPerronPoissonContourIntegrand (-σ) a) (-R) R 0 -
          HIntegral (liuPanPerronPoissonContourIntegrand (-σ) a) (-R) R R +
          VIntegral (liuPanPerronPoissonContourIntegrand (-σ) a) R 0 R -
          VIntegral (liuPanPerronPoissonContourIntegrand (-σ) a) (-R) 0 R =
        0 := by
    simpa [RectangleIntegral] using hboundary
  calc
    HIntegral (liuPanPerronPoissonContourIntegrand (-σ) a) (-R) R R -
          VIntegral (liuPanPerronPoissonContourIntegrand (-σ) a) R 0 R +
          VIntegral (liuPanPerronPoissonContourIntegrand (-σ) a) (-R) 0 R =
        HIntegral (liuPanPerronPoissonContourIntegrand (-σ) a) (-R) R 0 -
          (HIntegral (liuPanPerronPoissonContourIntegrand (-σ) a) (-R) R 0 -
            HIntegral (liuPanPerronPoissonContourIntegrand (-σ) a) (-R) R R +
            VIntegral (liuPanPerronPoissonContourIntegrand (-σ) a) R 0 R -
            VIntegral (liuPanPerronPoissonContourIntegrand (-σ) a) (-R) 0 R) := by
      ring
    _ = HIntegral (liuPanPerronPoissonContourIntegrand (-σ) a) (-R) R 0 := by
      rw [hboundary']
      ring

private theorem liuPanPerronPoissonRealIntegral_neg_sigma_eq_paired
    {σ : ℝ} (hσ : 0 < σ) (a R : ℝ) :
    HIntegral (liuPanPerronPoissonContourIntegrand (-σ) a) (-R) R 0 =
      ∫ t in 0..R,
        ((2 * (-σ * Real.cos (a * t) + t * Real.sin (a * t)) /
          (σ ^ 2 + t ^ 2) : ℝ) : ℂ) := by
  let f : ℝ → ℂ :=
    fun t => liuPanPerronPoissonContourIntegrand (-σ) a (t : ℂ)
  have hf : Continuous f := by
    dsimp only [f]
    unfold liuPanPerronPoissonContourIntegrand
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t hzero
      have hre := congrArg Complex.re hzero
      simp at hre
      linarith
  have hfneg : IntervalIntegrable f MeasureTheory.volume (-R) 0 :=
    hf.intervalIntegrable (-R) 0
  have hfpos : IntervalIntegrable f MeasureTheory.volume 0 R :=
    hf.intervalIntegrable 0 R
  have href : IntervalIntegrable (fun t => f (-t))
      MeasureTheory.volume 0 R := by
    have hc : Continuous (fun t => f (-t)) := by fun_prop
    exact hc.intervalIntegrable 0 R
  have hpair :
      (∫ t in -R..R, f t) = ∫ t in 0..R, (f t + f (-t)) := by
    calc
      (∫ t in -R..R, f t) =
          (∫ t in -R..0, f t) + ∫ t in 0..R, f t :=
        (intervalIntegral.integral_add_adjacent_intervals
          hfneg hfpos).symm
      _ = (∫ t in 0..R, f (-t)) + ∫ t in 0..R, f t := by
        rw [intervalIntegral.integral_comp_neg]
        norm_num
      _ = ∫ t in 0..R, (f (-t) + f t) :=
        (intervalIntegral.integral_add href hfpos).symm
      _ = ∫ t in 0..R, (f t + f (-t)) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        exact add_comm _ _
  unfold HIntegral
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  change (∫ t in -R..R, f t) = _
  rw [hpair]
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only [f]
  unfold liuPanPerronPoissonContourIntegrand
  rw [show (((-σ : ℝ) : ℂ) + Complex.I * (t : ℂ)) =
      liuPanPerronLine (-σ) t by
    unfold liuPanPerronLine
    ring]
  push_cast
  rw [show -(σ : ℂ) + Complex.I * -(t : ℂ) =
      liuPanPerronLine (-σ) (-t) by
    unfold liuPanPerronLine
    push_cast
    ring]
  rw [show ((a : ℂ) * Complex.I) * (t : ℂ) =
      ((a * t : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [show ((a : ℂ) * Complex.I) * (-t : ℂ) =
      ((-(a * t) : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  norm_cast
  rw [Real.cos_neg, Real.sin_neg]
  simp only [div_eq_mul_inv,
    liuPanPerronLine_inv_eq (-σ) t (neg_ne_zero.mpr hσ.ne'),
    liuPanPerronLine_inv_eq (-σ) (-t) (neg_ne_zero.mpr hσ.ne'),
    neg_sq]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  norm_num

private theorem tendsto_liuPanPerronPoissonPairedIntegral_pos_atTop
    {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) :
    Filter.Tendsto
      (fun R : ℝ => ∫ t in 0..R,
        2 * (σ * Real.cos (a * t) + t * Real.sin (a * t)) /
          (σ ^ 2 + t ^ 2))
      Filter.atTop
      (nhds (2 * Real.pi * Real.exp (-(a * σ)))) := by
  have hc := tendsto_liuPanPerronPoissonRealIntegral_atTop hσ ha
  have hp : Filter.Tendsto
      (fun R : ℝ => ((∫ t in 0..R,
        2 * (σ * Real.cos (a * t) + t * Real.sin (a * t)) /
          (σ ^ 2 + t ^ 2) : ℝ) : ℂ))
      Filter.atTop
      (nhds ((2 * Real.pi * Real.exp (-(a * σ)) : ℝ) : ℂ)) := by
    apply hc.congr'
    filter_upwards with R
    rw [← intervalIntegral.integral_ofReal]
    exact liuPanPerronPoissonRealIntegral_eq_paired hσ a R
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hp
  have hexp : (Complex.exp (-(↑a * ↑σ))).re =
      Real.exp (-(a * σ)) := by
    convert Complex.exp_ofReal_re (-(a * σ)) using 1
    push_cast
    ring
  simpa [Function.comp_def, hexp] using hre

private theorem tendsto_liuPanPerronPoissonPairedIntegral_neg_sigma_atTop
    {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) :
    Filter.Tendsto
      (fun R : ℝ => ∫ t in 0..R,
        2 * (-σ * Real.cos (a * t) + t * Real.sin (a * t)) /
          (σ ^ 2 + t ^ 2))
      Filter.atTop (nhds 0) := by
  have hc :=
    tendsto_liuPanPerronPoissonRealIntegral_neg_sigma_atTop hσ ha
  have hp : Filter.Tendsto
      (fun R : ℝ => ((∫ t in 0..R,
        2 * (-σ * Real.cos (a * t) + t * Real.sin (a * t)) /
          (σ ^ 2 + t ^ 2) : ℝ) : ℂ))
      Filter.atTop (nhds (0 : ℂ)) := by
    apply hc.congr'
    filter_upwards with R
    rw [← intervalIntegral.integral_ofReal]
    exact liuPanPerronPoissonRealIntegral_neg_sigma_eq_paired hσ a R
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hp
  simpa [Function.comp_def] using hre

private theorem liuPanPerronPoissonPositiveFrequencyLimits
    {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) :
    Filter.Tendsto
        (fun T : ℝ => ∫ t in (0 : ℝ)..T,
          σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2))
        Filter.atTop
        (nhds (Real.pi / 2 * Real.exp (-(a * σ)))) ∧
      Filter.Tendsto
        (fun T : ℝ => ∫ t in (0 : ℝ)..T,
          t * Real.sin (a * t) / (σ ^ 2 + t ^ 2))
        Filter.atTop
        (nhds (Real.pi / 2 * Real.exp (-(a * σ)))) := by
  rcases exists_liuPanPerronPoissonCosineIntegralLimit
      (a := a) hσ with ⟨Lc, hC⟩
  rcases exists_liuPanPerronPoissonSineIntegralLimit
      hσ ha.ne' with ⟨Ls, hS⟩
  let C : ℝ → ℝ := fun R => ∫ t in (0 : ℝ)..R,
    σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2)
  let S : ℝ → ℝ := fun R => ∫ t in (0 : ℝ)..R,
    t * Real.sin (a * t) / (σ ^ 2 + t ^ 2)
  have hfiC : ∀ R : ℝ, IntervalIntegrable
      (fun t : ℝ => σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2))
      MeasureTheory.volume 0 R := by
    intro R
    apply Continuous.intervalIntegrable
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    positivity
  have hfiS : ∀ R : ℝ, IntervalIntegrable
      (fun t : ℝ => t * Real.sin (a * t) / (σ ^ 2 + t ^ 2))
      MeasureTheory.volume 0 R := by
    intro R
    apply Continuous.intervalIntegrable
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    positivity
  have hplus : Filter.Tendsto (fun R => 2 * (C R + S R))
      Filter.atTop
      (nhds (2 * Real.pi * Real.exp (-(a * σ)))) := by
    apply (tendsto_liuPanPerronPoissonPairedIntegral_pos_atTop
      hσ ha).congr'
    filter_upwards with R
    dsimp only [C, S]
    rw [← intervalIntegral.integral_add (hfiC R) (hfiS R),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    ring
  have hminus : Filter.Tendsto (fun R => 2 * (-C R + S R))
      Filter.atTop (nhds 0) := by
    apply
      (tendsto_liuPanPerronPoissonPairedIntegral_neg_sigma_atTop
        hσ ha).congr'
    filter_upwards with R
    dsimp only [C, S]
    rw [show
        -(∫ t in (0 : ℝ)..R,
            σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2)) +
            (∫ t in (0 : ℝ)..R,
              t * Real.sin (a * t) / (σ ^ 2 + t ^ 2)) =
          (∫ t in (0 : ℝ)..R,
              t * Real.sin (a * t) / (σ ^ 2 + t ^ 2)) -
            (∫ t in (0 : ℝ)..R,
              σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2)) by ring,
      ← intervalIntegral.integral_sub (hfiS R) (hfiC R),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    ring
  have hC' : Filter.Tendsto C Filter.atTop (nhds Lc) := by
    simpa [C] using hC
  have hS' : Filter.Tendsto S Filter.atTop (nhds Ls) := by
    simpa [S] using hS
  have hpredPlus : Filter.Tendsto (fun R => 2 * (C R + S R))
      Filter.atTop (nhds (2 * (Lc + Ls))) := by
    simpa using tendsto_const_nhds.mul (hC'.add hS')
  have hpredMinus : Filter.Tendsto (fun R => 2 * (-C R + S R))
      Filter.atTop (nhds (2 * (-Lc + Ls))) := by
    simpa using tendsto_const_nhds.mul (hC'.neg.add hS')
  have heqPlus := tendsto_nhds_unique hplus hpredPlus
  have heqMinus := tendsto_nhds_unique hminus hpredMinus
  have hLc : Lc = Real.pi / 2 * Real.exp (-(a * σ)) := by
    linarith
  have hLs : Ls = Real.pi / 2 * Real.exp (-(a * σ)) := by
    linarith
  constructor
  · simpa [C, hLc] using hC'
  · simpa [S, hLs] using hS'

/-- The cosine component of the Poisson kernel has its exact improper value
for every real frequency. -/
theorem tendsto_liuPanPerronPoissonCosineIntegral_atTop
    {σ a : ℝ} (hσ : 0 < σ) :
    Filter.Tendsto
      (fun T : ℝ => ∫ t in (0 : ℝ)..T,
        σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2))
      Filter.atTop
      (nhds (Real.pi / 2 * Real.exp (-(|a| * σ)))) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have h :=
      (liuPanPerronPoissonPositiveFrequencyLimits hσ (neg_pos.mpr ha)).1
    have hfun :
        (fun T : ℝ => ∫ t in (0 : ℝ)..T,
          σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2)) =
        fun T : ℝ => ∫ t in (0 : ℝ)..T,
          σ * Real.cos ((-a) * t) / (σ ^ 2 + t ^ 2) := by
      funext T
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only
      rw [show a * t = -((-a) * t) by ring, Real.cos_neg]
    rw [hfun]
    simpa [abs_of_neg ha] using h
  · subst a
    have hscale : Filter.Tendsto (fun T : ℝ => T / σ)
        Filter.atTop Filter.atTop := by
      simpa [div_eq_mul_inv, mul_comm] using
        (Filter.tendsto_const_mul_atTop_of_pos (inv_pos.mpr hσ)).2
          Filter.tendsto_id
    have harctan : Filter.Tendsto
        (fun T : ℝ => Real.arctan (T / σ))
        Filter.atTop (nhds (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right inf_le_left).comp hscale
    have hfinite :
        (fun T : ℝ => ∫ t in (0 : ℝ)..T,
            σ * Real.cos (0 * t) / (σ ^ 2 + t ^ 2)) =
          fun T => Real.arctan (T / σ) := by
      funext T
      simpa using (integral_div_sq_add_sq (a := (0 : ℝ))
        (b := T) (c := σ))
    have hzero :
        Filter.Tendsto
          (fun T : ℝ => ∫ t in (0 : ℝ)..T,
            σ * Real.cos (0 * t) / (σ ^ 2 + t ^ 2))
          Filter.atTop (nhds (Real.pi / 2)) := by
      rw [hfinite]
      exact harctan
    simpa using hzero
  · simpa [abs_of_pos ha] using
      (liuPanPerronPoissonPositiveFrequencyLimits hσ ha).1

/-- The `t`-sine component of the Poisson kernel has the signed exact
improper value at every nonzero frequency. -/
theorem tendsto_liuPanPerronPoissonSineIntegral_atTop
    {σ a : ℝ} (hσ : 0 < σ) (ha : a ≠ 0) :
    Filter.Tendsto
      (fun T : ℝ => ∫ t in (0 : ℝ)..T,
        t * Real.sin (a * t) / (σ ^ 2 + t ^ 2))
      Filter.atTop
      (nhds ((if 0 < a then Real.pi / 2 else -(Real.pi / 2)) *
        Real.exp (-(|a| * σ)))) := by
  by_cases hapos : 0 < a
  · simpa [hapos, abs_of_pos hapos] using
      (liuPanPerronPoissonPositiveFrequencyLimits hσ hapos).2
  · have haneg : a < 0 := lt_of_le_of_ne (le_of_not_gt hapos) ha
    have h :=
      (liuPanPerronPoissonPositiveFrequencyLimits hσ (neg_pos.mpr haneg)).2
    have hneg := h.neg
    have hfun :
        (fun T : ℝ => ∫ t in (0 : ℝ)..T,
          t * Real.sin (a * t) / (σ ^ 2 + t ^ 2)) =
        fun T : ℝ => -(∫ t in (0 : ℝ)..T,
          t * Real.sin ((-a) * t) / (σ ^ 2 + t ^ 2)) := by
      funext T
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only
      rw [show a * t = -((-a) * t) by ring, Real.sin_neg]
      ring
    rw [hfun]
    simpa [hapos, abs_of_neg haneg] using hneg

/-- Explicit truncation error for the Perron kernel away from its jump. -/
theorem norm_liuPanTruncatedPerronKernel_sub_indicator_le
    {σ T z : ℝ} (hσ : 0 < σ) (hT : 0 < T)
    (hz : 0 < z) (hz1 : z ≠ 1) :
    ‖((if 1 < z then 1 else 0 : ℂ) -
        liuPanTruncatedPerronKernel σ T z)‖ ≤
      (z ^ σ / Real.pi) *
        (3 / (|Real.log z| * T) + 3 * σ / (2 * T)) := by
  let a := Real.log z
  let C : ℝ := ∫ t in (0 : ℝ)..T,
    σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2)
  let S : ℝ := ∫ t in (0 : ℝ)..T,
    t * Real.sin (a * t) / (σ ^ 2 + t ^ 2)
  let Lc : ℝ := Real.pi / 2 * Real.exp (-(|a| * σ))
  let Ls : ℝ :=
    (if 0 < a then Real.pi / 2 else -(Real.pi / 2)) *
      Real.exp (-(|a| * σ))
  have ha : a ≠ 0 := by
    dsimp only [a]
    exact Real.log_ne_zero_of_pos_of_ne_one hz hz1
  have hfiC : IntervalIntegrable
      (fun t : ℝ => σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2))
      MeasureTheory.volume 0 T := by
    apply Continuous.intervalIntegrable
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    positivity
  have hfiS : IntervalIntegrable
      (fun t : ℝ => t * Real.sin (a * t) / (σ ^ 2 + t ^ 2))
      MeasureTheory.volume 0 T := by
    apply Continuous.intervalIntegrable
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    positivity
  have hrealIntegral :
      (∫ t in (0 : ℝ)..T,
        2 * Real.exp (σ * Real.log z) *
          (σ * Real.cos (t * Real.log z) +
            t * Real.sin (t * Real.log z)) /
          (σ ^ 2 + t ^ 2)) =
        2 * (z ^ σ) * (C + S) := by
    rw [show Real.exp (σ * Real.log z) = z ^ σ by
      rw [Real.rpow_def_of_pos hz]
      congr 1
      ring]
    rw [← intervalIntegral.integral_add hfiC hfiS,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp only [a]
    rw [mul_comm t (Real.log z)]
    ring
  have hK :
      liuPanTruncatedPerronKernel σ T z =
        ((z ^ σ / Real.pi * (C + S) : ℝ) : ℂ) := by
    rw [liuPanTruncatedPerronKernel_eq_paired_real_integral hσ]
    rw [intervalIntegral.integral_ofReal, hrealIntegral]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hClim :
      Filter.Tendsto
        (fun R : ℝ => ∫ t in (0 : ℝ)..R,
          σ * Real.cos (a * t) / (σ ^ 2 + t ^ 2))
        Filter.atTop (nhds Lc) := by
    simpa [Lc] using
      (tendsto_liuPanPerronPoissonCosineIntegral_atTop
        (a := a) hσ)
  have hSlim :
      Filter.Tendsto
        (fun R : ℝ => ∫ t in (0 : ℝ)..R,
          t * Real.sin (a * t) / (σ ^ 2 + t ^ 2))
        Filter.atTop (nhds Ls) := by
    simpa [Ls] using
      (tendsto_liuPanPerronPoissonSineIntegral_atTop
        (a := a) hσ ha)
  have hCerr : |C - Lc| ≤ σ / T := by
    exact abs_liuPanPerronPoissonCosineIntegral_sub_limit_le
      hσ hT hClim
  have hSerr :
      |S - Ls| ≤ 3 / (|a| * T) + σ / (2 * T) := by
    exact abs_liuPanPerronPoissonSineIntegral_sub_limit_le
      hσ ha hT hSlim
  have hindicator :
      (if 1 < z then 1 else 0 : ℝ) =
        z ^ σ / Real.pi * (Lc + Ls) := by
    by_cases hzgt : 1 < z
    · have halog : 0 < a := by
        dsimp only [a]
        exact Real.log_pos hzgt
      rw [if_pos hzgt]
      simp only [Lc, Ls, if_pos halog, abs_of_pos halog]
      rw [Real.rpow_def_of_pos hz]
      field_simp [Real.pi_ne_zero]
      rw [← Real.exp_add]
      dsimp only [a]
      ring_nf
      simp
    · have hzlt : z < 1 := lt_of_le_of_ne (le_of_not_gt hzgt) hz1
      have halog : a < 0 := by
        dsimp only [a]
        exact Real.log_neg hz hzlt
      simp [hzgt, Lc, Ls, if_neg (not_lt.mpr halog.le)]
  have hfactor : 0 ≤ z ^ σ / Real.pi := by
    positivity
  rw [hK]
  rw [show (if 1 < z then 1 else 0 : ℂ) =
      ((if 1 < z then 1 else 0 : ℝ) : ℂ) by
    split_ifs <;> norm_num]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hdiff :
      (if 1 < z then 1 else 0 : ℝ) -
          z ^ σ / Real.pi * (C + S) =
        (z ^ σ / Real.pi) * ((Lc - C) + (Ls - S)) := by
    rw [hindicator]
    ring
  rw [hdiff, abs_mul, abs_of_nonneg hfactor]
  calc
    (z ^ σ / Real.pi) * |(Lc - C) + (Ls - S)| ≤
        (z ^ σ / Real.pi) * (|Lc - C| + |Ls - S|) := by
      gcongr
      exact abs_add_le _ _
    _ ≤ (z ^ σ / Real.pi) *
        (σ / T + (3 / (|a| * T) + σ / (2 * T))) := by
      gcongr
      · simpa [abs_sub_comm] using hCerr
      · simpa [abs_sub_comm] using hSerr
    _ = (z ^ σ / Real.pi) *
        (3 / (|Real.log z| * T) + 3 * σ / (2 * T)) := by
      dsimp only [a]
      ring

/-- The half-step logarithm stays uniformly separated from zero for every
positive integer coordinate, not only those inside the box. -/
theorem one_div_eight_mul_le_abs_log_liuPanPerronHalfStep_div
    {n Y M : ℕ} (hn : n ≠ 0) (hM : 1 ≤ M) (hYM : Y ≤ M) :
    1 / (8 * (M : ℝ)) ≤
      |Real.log (liuPanPerronHalfStep Y / (n : ℝ))| := by
  by_cases hnM : n ≤ M
  · calc
      1 / (8 * (M : ℝ)) ≤ 1 / (4 * (M : ℝ)) := by
        have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
        gcongr
        norm_num
      _ ≤ |Real.log (liuPanPerronHalfStep Y / (n : ℝ))| :=
        one_div_four_mul_le_abs_log_liuPanPerronHalfStep_div
          hn hM hYM hnM
  · have hnlow : M + 1 ≤ n := by omega
    have hnR : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hMR : (0 : ℝ) < M := by
      exact_mod_cast (show 0 < M by omega)
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hx : 0 < liuPanPerronHalfStep Y := by
      unfold liuPanPerronHalfStep
      positivity
    have hxM :
        liuPanPerronHalfStep Y ≤ (M : ℝ) + 1 / 2 := by
      unfold liuPanPerronHalfStep
      have hYR : (Y : ℝ) ≤ M := by exact_mod_cast hYM
      linarith
    have hnMR : (M : ℝ) + 1 ≤ n := by
      exact_mod_cast hnlow
    have hratio :
        liuPanPerronHalfStep Y / (n : ℝ) < 1 := by
      rw [div_lt_one hnR]
      linarith
    rw [abs_of_neg (Real.log_neg
      (liuPanPerronHalfStep_div_natCast_pos hn) hratio)]
    rw [← Real.log_inv, inv_div]
    have hrev : 0 < (n : ℝ) / liuPanPerronHalfStep Y :=
      div_pos hnR hx
    have hratioBound :
        liuPanPerronHalfStep Y / (n : ℝ) ≤
          ((M : ℝ) + 1 / 2) / ((M : ℝ) + 1) := by
      exact div_le_div₀ (by positivity) hxM (by positivity) hnMR
    calc
      1 / (8 * (M : ℝ)) ≤
          1 - (liuPanPerronHalfStep Y / (n : ℝ)) := by
        calc
          1 / (8 * (M : ℝ)) ≤
              1 - (((M : ℝ) + 1 / 2) / ((M : ℝ) + 1)) := by
            field_simp
            ring_nf
            nlinarith
          _ ≤ 1 - (liuPanPerronHalfStep Y / (n : ℝ)) :=
            sub_le_sub_left hratioBound 1
      _ = 1 - (((n : ℝ) / liuPanPerronHalfStep Y)⁻¹) := by
        rw [inv_div]
      _ ≤ Real.log ((n : ℝ) / liuPanPerronHalfStep Y) :=
        Real.one_sub_inv_le_log_of_pos hrev


private theorem liuPanPerronTermIntegrand_eq
    (Y n : ℕ) (c : ℂ) (σ t : ℝ) (hn : n ≠ 0) :
    Complex.exp
          (liuPanPerronLine σ t * Real.log (liuPanPerronHalfStep Y)) /
        liuPanPerronLine σ t *
      (c * liuPanPerronNatPower n (liuPanPerronLine σ t)) =
    (Complex.exp
          (liuPanPerronLine σ t *
            Real.log (liuPanPerronHalfStep Y / n)) /
        liuPanPerronLine σ t) * c := by
  have hx0 : liuPanPerronHalfStep Y ≠ 0 := by
    unfold liuPanPerronHalfStep
    positivity
  have hnR0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hlog :
      Real.log (liuPanPerronHalfStep Y / n) =
        Real.log (liuPanPerronHalfStep Y) - Real.log n :=
    Real.log_div hx0 hnR0
  rw [liuPanPerronNatPower_of_ne hn, hlog]
  calc
    _ = (Complex.exp
          (liuPanPerronLine σ t * Real.log (liuPanPerronHalfStep Y)) *
        Complex.exp (-liuPanPerronLine σ t * Real.log n)) /
          liuPanPerronLine σ t * c := by ring
    _ = Complex.exp
          (liuPanPerronLine σ t * Real.log (liuPanPerronHalfStep Y) +
            (-liuPanPerronLine σ t * Real.log n)) /
          liuPanPerronLine σ t * c := by rw [Complex.exp_add]
    _ = _ := by
      congr 2
      push_cast
      ring_nf

private theorem liuPanPerronTermIntegral_eq_kernel
    {σ T : ℝ} (Y n : ℕ) (c : ℂ) (hn : n ≠ 0) :
    (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ t in -T..T,
          Complex.exp
                (liuPanPerronLine σ t * Real.log (liuPanPerronHalfStep Y)) /
              liuPanPerronLine σ t *
            (c * liuPanPerronNatPower n (liuPanPerronLine σ t)) =
      c * liuPanTruncatedPerronKernel σ T
        (liuPanPerronHalfStep Y / n) := by
  have hfun :
      (fun t : ℝ =>
        Complex.exp
              (liuPanPerronLine σ t * Real.log (liuPanPerronHalfStep Y)) /
            liuPanPerronLine σ t *
          (c * liuPanPerronNatPower n (liuPanPerronLine σ t))) =
        fun t : ℝ =>
          (Complex.exp
                (liuPanPerronLine σ t *
                  Real.log (liuPanPerronHalfStep Y / n)) /
              liuPanPerronLine σ t) * c := by
    funext t
    exact liuPanPerronTermIntegrand_eq Y n c σ t hn
  rw [hfun, intervalIntegral.integral_mul_const]
  unfold liuPanTruncatedPerronKernel
  ring

private theorem liuPanPerronTerm_intervalIntegrable
    {σ T : ℝ} (Y n : ℕ) (c : ℂ) (hσ : 0 < σ) (hn : n ≠ 0) :
    IntervalIntegrable
      (fun t : ℝ =>
        Complex.exp
              (liuPanPerronLine σ t * Real.log (liuPanPerronHalfStep Y)) /
            liuPanPerronLine σ t *
          (c * liuPanPerronNatPower n (liuPanPerronLine σ t)))
      MeasureTheory.volume (-T) T := by
  have hfun :
      (fun t : ℝ =>
        Complex.exp
              (liuPanPerronLine σ t * Real.log (liuPanPerronHalfStep Y)) /
            liuPanPerronLine σ t *
          (c * liuPanPerronNatPower n (liuPanPerronLine σ t))) =
        fun t : ℝ =>
          (Complex.exp
                (liuPanPerronLine σ t *
                  Real.log (liuPanPerronHalfStep Y / n)) /
              liuPanPerronLine σ t) * c := by
    funext t
    exact liuPanPerronTermIntegrand_eq Y n c σ t hn
  rw [hfun]
  exact (liuPanPerronKernelIntegrand_intervalIntegrable
    (z := liuPanPerronHalfStep Y / n) hσ).mul_const c

/-- Expanding the finite Dirichlet polynomials and interchanging their finite
sums with the interval integral gives the exact kernel sum. -/
theorem liuPanTruncatedPerronIntegral_eq_kernelSum
    {q : ℕ} (U V : Finset ℕ) (A B : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) {σ T : ℝ} (Y : ℕ) (hσ : 0 < σ) :
    liuPanTruncatedPerronIntegral U V A B χ σ T Y =
      ∑ u ∈ U, ∑ v ∈ V,
        liuPanPerronProductCoefficient A B χ u v *
          liuPanTruncatedPerronKernel σ T
            (liuPanPerronHalfStep Y / (u * v : ℕ)) := by
  classical
  unfold liuPanTruncatedPerronIntegral
  simp_rw [liuPanPerronDirichletPolynomial_mul]
  simp only [mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · rw [mul_sum]
    apply sum_congr rfl
    intro u hu
    rw [intervalIntegral.integral_finsetSum]
    · rw [mul_sum]
      apply sum_congr rfl
      intro v hv
      by_cases huv0 : u * v = 0
      · simp [liuPanPerronProductCoefficient, Nat.mul_eq_zero.mp huv0]
      exact liuPanPerronTermIntegral_eq_kernel Y (u * v)
        (liuPanPerronProductCoefficient A B χ u v) huv0
    · intro v hv
      by_cases huv0 : u * v = 0
      · simp [liuPanPerronProductCoefficient, Nat.mul_eq_zero.mp huv0]
      exact liuPanPerronTerm_intervalIntegrable Y (u * v)
        (liuPanPerronProductCoefficient A B χ u v) hσ huv0
  · intro u hu
    have hvint : ∀ v ∈ V, IntervalIntegrable
        (fun t : ℝ =>
          Complex.exp
                (liuPanPerronLine σ t * Real.log (liuPanPerronHalfStep Y)) /
              liuPanPerronLine σ t *
            (liuPanPerronProductCoefficient A B χ u v *
              liuPanPerronNatPower (u * v) (liuPanPerronLine σ t)))
        MeasureTheory.volume (-T) T := by
      intro v hv
      by_cases huv0 : u * v = 0
      · simp [liuPanPerronProductCoefficient, Nat.mul_eq_zero.mp huv0]
      exact liuPanPerronTerm_intervalIntegrable Y (u * v)
        (liuPanPerronProductCoefficient A B χ u v) hσ huv0
    rw [show
      (fun t : ℝ => ∑ v ∈ V,
        Complex.exp
              (liuPanPerronLine σ t * Real.log (liuPanPerronHalfStep Y)) /
            liuPanPerronLine σ t *
          (liuPanPerronProductCoefficient A B χ u v *
            liuPanPerronNatPower (u * v) (liuPanPerronLine σ t))) =
        ∑ v ∈ V, fun t : ℝ =>
          Complex.exp
                (liuPanPerronLine σ t * Real.log (liuPanPerronHalfStep Y)) /
              liuPanPerronLine σ t *
            (liuPanPerronProductCoefficient A B χ u v *
              liuPanPerronNatPower (u * v) (liuPanPerronLine σ t)) by
      funext t
      simp]
    exact IntervalIntegrable.sum V hvint


end MathlibNt.SieveTheory.LiuWeight
