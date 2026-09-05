import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import AnalyticNumberTheory.Sieve.LinearSieve
import AnalyticNumberTheory.Sieve.SelbergIdentities
import AnalyticNumberTheory.Sieve.WeightedPan

/-! # AnalyticNumberTheory.Sieve.SelbergUpperBound

## Generic Selberg upper-bound sieve

The Selberg sieve is a central tool for the upper bound on `Ω` in
Chen's theorem. An upper Moebius sequence from Λ² weights separates
the sifted count into a main term and a remainder. The classical
shape (Halberstam--Richert 1974 Ch. 3; Nathanson GTM 164 Ch. 10;
Liu 2022 §III) is
`S(A,P,z) ≤ X/G(z) + Σ |R_d|`, where
`G(z) = Σ_{d|P} g(d)` and
`g(d) = ν(d)·∏_{p|d}(1−ν(p))⁻¹`.
For the full divisor sum used here, optimal Λ² weights attain
`mainSum = 1/G(z)`.

This module supplies:

1. `SelbergWeights`, a generic bounded, supported weight structure,
   and its trivial existence theorem `selberg_sieve_weights_exist`.
2. Bridges to mathlib's `BoundingSieve.lambdaSquared`:
   `selberg_lambda_is_upper_moebius`, the basic upper bound
   `omega_upper_bound_via_mathlib`, diagonalization
   `mainSum_diag_via_mathlib`, and the Cauchy--Schwarz lower bound
   `mainSum_cauchy_schwarz_lower_bound`.
3. Explicit optimal full-divisor weights `optimalSelbergWeight`,
   with `mainSum(Λ²w*) = (Σg)⁻¹` (`optimalSelbergMainSum_eq`),
   giving the finite theorem `selberg_upper_bound_optimal`
   without additional analytic input.
4. `UniformSelbergUpperBound` for a family of `BoundingSieve`
   structures, with `N₀` before `∀ N`, proved directly from
   the optimal-weight theorem. The numerical Chen bound
   `3.9404·𝔖(N)·N/log²N` additionally requires Mertens/singular-series
   main-term estimates and a weighted Pan remainder input
   (`WeightedPan`); the finite theorem does not supply them.

References:
  - Selberg, A. (1947), Norske Vid. Selsk. Forh. Trondheim 19, 75-79
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 3
  - Nathanson, "Additive Number Theory: The Classical Bases" (1996), Ch. 10
  - Liu, Z. (2022), arXiv:2203.07871, §III
  - Mathlib `SelbergSieve.lean`: BoundingSieve, Λ² sieve, selbergTerms
-/

namespace AnalyticNumberTheory.Sieve

open Finset Real

open scoped Classical
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

/-! ## 1. Selberg weight structure -/

/-- Selberg weights for a sieve product `Q` and level `z`:
`λ₁ = 1`, `λ_d = 0` if `d > z` or `d ∤ Q`, and `|λ_d| ≤ 1`.
This generalizes the Chen-specific `SelbergWeights (N ε)`,
where `Q = selbergQ N ε` is the product of primes at most `z`
not dividing `N`, and `z = N^(1/4-ε/2)`. -/
structure SelbergWeights (Q z : ℕ) where
  /-- The weight function `λ_d`. -/
  lambda : ℕ → ℝ
  /-- λ₁ = 1 -/
  lambda_one : lambda 1 = 1
  /-- `λ_d = 0` if `d > z` or `d ∤ Q`. -/
  lambda_support : ∀ d : ℕ, d > z ∨ ¬ d ∣ Q → lambda d = 0
  /-- |λ_d| ≤ 1 -/
  lambda_bounded : ∀ d : ℕ, |lambda d| ≤ 1

/-- **Trivial Selberg weights**: `λ₁ = 1` and all other weights zero
give valid `SelbergWeights`, with
`Σ_{d₁,d₂} λ_{d₁}λ_{d₂}/φ([d₁,d₂]) = 1`,
since only `d₁ = d₂ = 1` contributes.
This is the trivial comparison choice for the optimal weights
in Chen's Lemma 3. -/
theorem selberg_sieve_weights_exist (Q z : ℕ) (hQ : Q ≠ 0) (hz : 1 ≤ z) :
    ∃ (SW : SelbergWeights Q z),
      (Q.divisors.sum (fun d₁ =>
        Q.divisors.sum (fun d₂ =>
          SW.lambda d₁ * SW.lambda d₂ / Nat.totient (Nat.lcm d₁ d₂)))) = 1 := by
  let SW : SelbergWeights Q z :=
    { lambda := fun d => if d = 1 then 1 else 0
      lambda_one := by simp
      lambda_support := by
        intro d hd
        by_cases hd1 : d = 1
        · subst d
          exfalso
          rcases hd with hlarge | hndvd
          · exact (not_lt_of_ge hz) hlarge
          · exact hndvd (Nat.one_dvd _)
        · simp [hd1]
      lambda_bounded := by
        intro d
        by_cases hd1 : d = 1 <;> simp [hd1] }
  refine ⟨SW, ?_⟩
  have h1mem : (1 : ℕ) ∈ Q.divisors := Nat.mem_divisors.mpr ⟨one_dvd Q, hQ⟩
  have hsum :
      (Q.divisors.sum (fun d₁ =>
        Q.divisors.sum (fun d₂ =>
          SW.lambda d₁ * SW.lambda d₂ / Nat.totient (Nat.lcm d₁ d₂)))) =
        (1 : ℝ) / Nat.totient 1 := by
    -- Only d₂ = 1 contributes to the inner sum.
    have hinner : ∀ d₁ : ℕ,
        (Q.divisors.sum (fun d₂ =>
          SW.lambda d₁ * SW.lambda d₂ / Nat.totient (Nat.lcm d₁ d₂))) =
          if d₁ = 1 then (1 : ℝ) / Nat.totient 1 else 0 := by
      intro d₁
      have hstep : (Q.divisors.sum (fun d₂ =>
            SW.lambda d₁ * SW.lambda d₂ / Nat.totient (Nat.lcm d₁ d₂))) =
          ∑ d₂ ∈ Q.divisors, if d₂ = 1 then
            SW.lambda d₁ * (1 : ℝ) / Nat.totient (Nat.lcm d₁ d₂) else 0 := by
        apply Finset.sum_congr rfl
        intro d₂ hd₂
        by_cases h : d₂ = 1
        · subst d₂
          simp [SW]
        · simp [SW, h]
      rw [hstep]
      rw [Finset.sum_ite_eq_of_mem' _ 1 _ h1mem]
      by_cases h : d₁ = 1
      · subst d₁
        simp [SW]
      · simp [SW, h]
    calc
      (Q.divisors.sum (fun d₁ =>
        Q.divisors.sum (fun d₂ =>
          SW.lambda d₁ * SW.lambda d₂ / Nat.totient (Nat.lcm d₁ d₂))))
          = ∑ d₁ ∈ Q.divisors, (if d₁ = 1 then (1 : ℝ) / Nat.totient 1 else 0) := by
            apply Finset.sum_congr rfl
            intro d₁ hd₁
            exact hinner d₁
      _ = (1 : ℝ) / Nat.totient 1 := by
            rw [Finset.sum_ite_eq_of_mem' _ 1 _ h1mem]
  simpa [Nat.totient_one] using hsum

/-! ## 2. Bridges to mathlib -/

/-- Construct mathlib's Λ² weights from `SelbergWeights`:
`lambdaSquared weights d
 = Σ_{d₁|d} Σ_{d₂|d} [d=lcm(d₁,d₂)]·weights(d₁)·weights(d₂)`. -/
def selbergLambdaSquared {Q z : ℕ} (SW : SelbergWeights Q z) : ℕ → ℝ :=
  BoundingSieve.lambdaSquared SW.lambda

/-- The `lambdaSquared` sequence from Selberg weights
is an upper Moebius sequence. -/
theorem selberg_lambda_is_upper_moebius {Q z : ℕ} (SW : SelbergWeights Q z) :
    BoundingSieve.IsUpperMoebius (selbergLambdaSquared SW) := by
  exact BoundingSieve.upperMoebius_lambdaSquared SW.lambda SW.lambda_one

/-- **Basic Selberg upper bound** (mathlib): any sequence `w`
with `w 1 = 1` gives
`siftedSum ≤ totalMass·mainSum(Λ²w) + errSum(Λ²w)`.
Choosing weights minimizing `mainSum` gives the optimal finite
upper bound; the remainder still needs separate control. -/
theorem omega_upper_bound_via_mathlib
    (S : BoundingSieve) (w : ℕ → ℝ) (hw : w 1 = 1) :
    S.siftedSum ≤ S.totalMass * S.mainSum (BoundingSieve.lambdaSquared w) +
      S.errSum (BoundingSieve.lambdaSquared w) := by
  exact BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius _
    (BoundingSieve.upperMoebius_lambdaSquared w hw)

/-- **Main-term diagonalization** (mathlib): `mainSum(Λ²w)` is a
diagonal quadratic form with coefficients `(selbergTerms l)⁻¹`. -/
theorem mainSum_diag_via_mathlib
    (S : BoundingSieve) (w : ℕ → ℝ) :
    S.mainSum (BoundingSieve.lambdaSquared w) =
      ∑ l ∈ S.prodPrimes.divisors, (S.selbergTerms l)⁻¹ *
        (∑ d ∈ S.prodPrimes.divisors,
          if l ∣ d then S.nu d * w d else 0) ^ 2 := by
  exact S.mainSum_lambdaSquared_eq_sum_mul_sum_sq w

/-- **Optimality lower bound** (Cauchy--Schwarz/Titu):
for `w 1 = 1`,
`mainSum(Λ²w) ≥ (Σ_{l|P} selbergTerms l)⁻¹`.
Optimal Selberg weights attain equality
(`optimalSelbergMainSum_eq`). -/
theorem mainSum_cauchy_schwarz_lower_bound
    (S : BoundingSieve) (w : ℕ → ℝ) (hw : w 1 = 1) :
    (S.prodPrimes.divisors.sum (fun l => S.selbergTerms l))⁻¹ ≤
      S.mainSum (BoundingSieve.lambdaSquared w) := by
  -- Helper: Σ_{l ∈ d.divisors} (μ l : ℝ) = [d = 1]
  -- This follows from (ζ * μ)(d) = 1(d) via Möbius inversion
  have hMoebiusSum : ∀ d ∈ S.prodPrimes.divisors,
      ∑ l ∈ d.divisors, (μ l : ℝ) = if d = 1 then (1 : ℝ) else 0 := by
    intro d hd
    have h := ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ)
    have hkey : (ζ * (μ : ArithmeticFunction ℝ)) d = (1 : ArithmeticFunction ℝ) d := by rw [h]
    rw [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply] at hkey
    simp only [ArithmeticFunction.intCoe_apply] at hkey
    exact hkey
  -- Möbius inversion: Σ_l (μ l : ℝ) * x_l = 1
  -- where x_l = Σ_{d ∈ D} [l|d] ν(d) w(d)
  have hMoebiusInv : ∑ l ∈ S.prodPrimes.divisors,
      (μ l : ℝ) * (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0) = 1 := by
    calc ∑ l ∈ S.prodPrimes.divisors,
          (μ l : ℝ) * (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0)
        = ∑ l ∈ S.prodPrimes.divisors,
            ∑ d ∈ S.prodPrimes.divisors,
              (μ l : ℝ) * (if l ∣ d then S.nu d * w d else 0) := by simp_rw [mul_sum]
      _ = ∑ d ∈ S.prodPrimes.divisors,
            ∑ l ∈ S.prodPrimes.divisors,
              (μ l : ℝ) * (if l ∣ d then S.nu d * w d else 0) := by rw [sum_comm]
      _ = ∑ d ∈ S.prodPrimes.divisors,
            S.nu d * w d * (∑ l ∈ d.divisors, (μ l : ℝ)) := by
        refine sum_congr rfl fun d hd => ?_
        have hdvd : d ∣ S.prodPrimes := (Nat.mem_divisors.mp hd).1
        simp_rw [mul_ite, mul_zero]
        rw [← sum_filter, Nat.divisors_filter_dvd_of_dvd S.prodPrimes_ne_zero hdvd, mul_sum]
        exact sum_congr rfl (fun l _ => mul_comm _ _)
      _ = ∑ d ∈ S.prodPrimes.divisors,
            S.nu d * w d * (if d = 1 then (1 : ℝ) else 0) := by
        refine sum_congr rfl fun d hd => ?_
        rw [hMoebiusSum d hd]
      _ = S.nu 1 * w 1 := by
        have h1mem : (1 : ℕ) ∈ S.prodPrimes.divisors :=
          Nat.mem_divisors.mpr ⟨one_dvd S.prodPrimes, S.prodPrimes_ne_zero⟩
        simp_rw [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq_of_mem' _ _ _ h1mem]
      _ = 1 := by
        have h_nu1 : S.nu 1 = 1 := S.nu_mult.map_one
        rw [h_nu1, hw]
        norm_num
  -- Titu's lemma (Sedrakyan's lemma / Engel form of Cauchy-Schwarz)
  -- Applied with f_l = (μ l : ℝ) * x_l, g_l = selbergTerms l * (μ l : ℝ)²
  have hTitu :
      (∑ l ∈ S.prodPrimes.divisors,
        (μ l : ℝ) * (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0)) ^ 2 /
      ∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l * (μ l : ℝ) ^ 2 ≤
      ∑ l ∈ S.prodPrimes.divisors,
        ((μ l : ℝ) * (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0)) ^ 2 /
        (S.selbergTerms l * (μ l : ℝ) ^ 2) := by
    apply sq_sum_div_le_sum_sq_div
    intro l hl
    have hsq := S.squarefree_of_mem_divisors_prodPrimes hl
    have hpos := S.selbergTerms_pos ((Nat.mem_divisors.mp hl).1)
    have hμsq : (μ l : ℝ) ^ 2 = 1 := by exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [hμsq, mul_one]
    exact hpos
  -- Simplify denominator: Σ selbergTerms l * μ(l)² = Σ selbergTerms l
  -- (since all l | P are squarefree, μ(l)² = 1)
  have hDenom : ∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l * (μ l : ℝ) ^ 2 =
      ∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l := by
    refine sum_congr rfl fun l hl => ?_
    have hsq := S.squarefree_of_mem_divisors_prodPrimes hl
    have hμsq : (μ l : ℝ) ^ 2 = 1 := by exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [hμsq, mul_one]
  -- Simplify RHS: Σ ((μ l) * x_l)² / (selbergTerms l * μ(l)²) = Σ selbergTerms(l)⁻¹ * x_l²
  have hRHS : ∑ l ∈ S.prodPrimes.divisors,
        ((μ l : ℝ) * (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0)) ^ 2 /
        (S.selbergTerms l * (μ l : ℝ) ^ 2) =
      ∑ l ∈ S.prodPrimes.divisors,
        (S.selbergTerms l)⁻¹ *
        (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0) ^ 2 := by
    refine sum_congr rfl fun l hl => ?_
    have hsq := S.squarefree_of_mem_divisors_prodPrimes hl
    have hμsq : (μ l : ℝ) ^ 2 = 1 := by exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [hμsq, mul_one, mul_pow, hμsq, one_mul, div_eq_inv_mul]
  -- Diagonalization (Mathlib: mainSum_lambdaSquared_eq_sum_mul_sum_sq)
  have h_diag : S.mainSum (BoundingSieve.lambdaSquared w) =
      ∑ l ∈ S.prodPrimes.divisors,
        (S.selbergTerms l)⁻¹ *
        (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0) ^ 2 :=
    S.mainSum_lambdaSquared_eq_sum_mul_sum_sq w
  -- Chain everything together
  rw [hMoebiusInv, hDenom] at hTitu
  simp only [one_pow] at hTitu
  rw [hRHS] at hTitu
  rw [one_div] at hTitu
  rw [h_diag]
  exact hTitu

/-! ## 3. Optimal Selberg weights -/

/-- Optimal Selberg main term: `(Σ_{l|P} selbergTerms l)⁻¹`. -/
noncomputable def selbergMainTerm (S : BoundingSieve) : ℝ :=
  (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l)⁻¹

/-- Optimal diagonal values `x*_l = g(l)·μ(l)·(Σg)⁻¹`,
minimizing `Σ_l g(l)⁻¹·x_l²` subject to `w(1)=1`. -/
noncomputable def optimalSelbergX (S : BoundingSieve) (l : ℕ) : ℝ :=
  S.selbergTerms l * (μ l : ℝ) * selbergMainTerm S

/-- **Optimal Selberg Λ² weights**: apply upper-interval Moebius
inversion to `optimalSelbergX` on the divisor lattice of `prodPrimes`,
then divide by the density:
`w*(d) = ν(d)⁻¹·Σ_{e : d|e|P} μ(e/d)·x*_e`.
`optimalSelbergMainSum_eq` proves
`mainSum(Λ²w*) = (Σg)⁻¹`, attaining the lower bound
`mainSum_cauchy_schwarz_lower_bound`. -/
noncomputable def optimalSelbergWeight (S : BoundingSieve) : ℕ → ℝ :=
  fun d =>
    if _hd : d ∣ S.prodPrimes then
      (∑ e ∈ S.prodPrimes.divisors,
        if d ∣ e then (μ (e / d) : ℝ) * optimalSelbergX S e else 0) / S.nu d
    else 0

/-- Standard Moebius sum: `Σ_{d|n} μ(d) = [n=1]`. -/
private lemma sum_moebius_eq_one {n : ℕ} :
    (∑ d ∈ n.divisors, (μ d : ℝ)) = if n = 1 then (1 : ℝ) else 0 := by
  have h := ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ)
  have hkey : (ζ * (μ : ArithmeticFunction ℝ)) n = (1 : ArithmeticFunction ℝ) n := by rw [h]
  rw [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply] at hkey
  simpa [ArithmeticFunction.intCoe_apply, mul_comm] using hkey

/-- For nonzero `e` with `d|e` and `l|e`,
`l|d ↔ e/d | e/l`. This quotient form converts divisibility
by `l` into divisibility of `e/l` for reindexing a restricted
Moebius sum. -/
private lemma dvd_iff_div_dvd {e l d : ℕ} (he : e ≠ 0) (hd : d ∣ e) (hl : l ∣ e) :
    l ∣ d ↔ e / d ∣ e / l := by
  constructor
  · intro hld
    rcases hld with ⟨k, rfl⟩
    have hl0 : 0 < l := Nat.pos_of_dvd_of_pos hl (Nat.pos_of_ne_zero he)
    have hkl : k ∣ e / l := by
      have heq : e = l * (e / l) := by
        rw [mul_comm, Nat.div_mul_cancel hl]
      rw [heq] at hd
      exact (Nat.mul_dvd_mul_iff_left hl0).mp hd
    have hq : e / (l * k) = (e / l) / k := (Nat.div_div_eq_div_mul e l k).symm
    rw [hq]
    exact Nat.div_dvd_of_dvd hkl
  · intro hdl
    rcases hdl with ⟨j, hj⟩
    have heq1 : e = l * (e / l) := by
      rw [mul_comm, Nat.div_mul_cancel hl]
    have heq2 : d * (e / d) = e := by
      rw [mul_comm, Nat.div_mul_cancel hd]
    have hdq : 0 < e / d :=
      Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hd) (Nat.pos_of_ne_zero he)
    have hmain : d * (e / d) = l * j * (e / d) := by
      calc
        d * (e / d) = e := heq2
        _ = l * (e / l) := heq1
        _ = l * (j * (e / d)) := by
          rw [hj]
          ring
        _ = l * j * (e / d) := by ring
    refine ⟨j, ?_⟩
    exact Nat.mul_right_cancel hdq hmain

/-- Restricted Moebius sum: for `l|e` and `e ≠ 0`,
`Σ_{d|e, l|d} μ(e/d) = [e=l]`. -/
private lemma sum_moebius_quotient_of_dvd {e l : ℕ} (he : e ≠ 0) (hle : l ∣ e) :
    (∑ d ∈ e.divisors, if l ∣ d then (μ (e / d) : ℝ) else 0) =
      if e = l then (1 : ℝ) else 0 := by
  -- Reindex d ↦ e/d: the condition [l|d] becomes [e/d | e/l].
  have hbij :
      (∑ d ∈ e.divisors, if l ∣ d then (μ (e / d) : ℝ) else 0) =
        ∑ d ∈ e.divisors, if d ∣ e / l then (μ d : ℝ) else 0 := by
    refine Finset.sum_bij (fun d _ => e / d) ?_ ?_ ?_ ?_
    · intro d hd
      have hdvd : d ∣ e := (Nat.mem_divisors.mp hd).1
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, he⟩
    · intro a ha b hb hab
      have havd : a ∣ e := (Nat.mem_divisors.mp ha).1
      have hbvd : b ∣ e := (Nat.mem_divisors.mp hb).1
      calc
        a = e / (e / a) := (Nat.div_div_self havd he).symm
        _ = e / (e / b) := by rw [hab]
        _ = b := Nat.div_div_self hbvd he
    · intro d hd
      have hdvd : d ∣ e := (Nat.mem_divisors.mp hd).1
      refine ⟨e / d, ?_, ?_⟩
      · exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, he⟩
      · exact Nat.div_div_self hdvd he
    · intro d hd
      have hdvd : d ∣ e := (Nat.mem_divisors.mp hd).1
      by_cases hld : l ∣ d
      · have hdld : e / d ∣ e / l := (dvd_iff_div_dvd he hdvd hle).mp hld
        simp [hld, hdld]
      · have hndld : ¬ e / d ∣ e / l := by
          intro h
          apply hld
          exact (dvd_iff_div_dvd he hdvd hle).mpr h
        simp [hld, hndld]
  rw [hbij]
  -- The sum is now Σ_{d|e, d|e/l} μ(d); since e/l divides e, its index set is (e/l).divisors.
  have hfilter : e.divisors.filter (fun d => d ∣ e / l) = (e / l).divisors :=
    Nat.divisors_filter_dvd_of_dvd he (Nat.div_dvd_of_dvd hle)
  rw [← Finset.sum_filter]
  rw [hfilter]
  rw [sum_moebius_eq_one]
  by_cases hel : e = l
  · have hl0 : 0 < l := Nat.pos_of_dvd_of_pos hle (Nat.pos_of_ne_zero he)
    simp [hel]
    exact Nat.div_self hl0
  · have hdiv_ne : e / l ≠ 1 := by
      intro h
      apply hel
      calc
        e = l * (e / l) := by rw [mul_comm, Nat.div_mul_cancel hle]
        _ = l * 1 := by rw [h]
        _ = l := by rw [mul_one]
    simp [hdiv_ne, hel]

/-- **Normalization of the optimal weight**: `w*(1) = 1`. -/
theorem optimalSelbergWeight_one (S : BoundingSieve) :
    optimalSelbergWeight S 1 = 1 := by
  unfold optimalSelbergWeight
  rw [dif_pos (one_dvd S.prodPrimes)]
  -- Numerator: Σ_{e|P} μ(e)·x*_e = (Σg)⁻¹·Σ_e g(e)·μ(e)² = (Σg)⁻¹·Σg = 1.
  have hnum : (∑ e ∈ S.prodPrimes.divisors,
        (μ (e / 1) : ℝ) * optimalSelbergX S e) = 1 := by
    have hstep1 : (∑ e ∈ S.prodPrimes.divisors,
        (μ (e / 1) : ℝ) * optimalSelbergX S e) =
        selbergMainTerm S * (∑ e ∈ S.prodPrimes.divisors, S.selbergTerms e) := by
      -- e/1 = e, and μ(e)·x*_e = μ(e)·g(e)·μ(e)·T = T·g(e)·μ(e)² = T·g(e).
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      have hsq := S.squarefree_of_mem_divisors_prodPrimes he
      have hμsq : (μ e : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
      unfold optimalSelbergX
      simp only [Nat.div_one]
      ring_nf
      rw [hμsq]
      ring
    rw [hstep1]
    unfold selbergMainTerm
    have hsum_ne : (∑ e ∈ S.prodPrimes.divisors, S.selbergTerms e) ≠ 0 := by
      have h1mem : (1 : ℕ) ∈ S.prodPrimes.divisors :=
        Nat.mem_divisors.mpr ⟨one_dvd S.prodPrimes, S.prodPrimes_ne_zero⟩
      have hpos1 : 0 < S.selbergTerms 1 := by
        rw [BoundingSieve.selbergTerms_apply]
        have hν1 : S.nu 1 = 1 := S.nu_mult.map_one
        simp [hν1]
      exact ne_of_gt (Finset.sum_pos
        (fun e he => S.selbergTerms_pos ((Nat.mem_divisors.mp he).1)) ⟨1, h1mem⟩)
    field_simp [hsum_ne]
  -- The denominator is ν(1) = 1.
  have hν1 : S.nu 1 = 1 := S.nu_mult.map_one
  rw [hν1]
  have hif : (∑ e ∈ S.prodPrimes.divisors,
        if (1 : ℕ) ∣ e then (μ (e / 1) : ℝ) * optimalSelbergX S e else 0) =
      ∑ e ∈ S.prodPrimes.divisors, (μ (e / 1) : ℝ) * optimalSelbergX S e := by
    apply Finset.sum_congr rfl
    intro e he
    rw [if_pos (one_dvd e)]
  rw [hif, hnum]
  norm_num

/-- **Diagonal-value identification**:
`Σ_{d : l|d|P} ν(d)·w*(d) = x*_l`.
This is the upper-interval Moebius-inversion identity for
`w* = ν⁻¹·y*`, where
`y*(d) = Σ_{e : d|e|P} μ(e/d)·x*_e`. -/
theorem optimalSelbergX_eq_sum_nu_mul_weight (S : BoundingSieve) (l : ℕ)
    (hl : l ∣ S.prodPrimes) :
    optimalSelbergX S l =
      ∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * optimalSelbergWeight S d else 0 := by
  -- For d|P, ν(d)·w*(d) = y*(d) := Σ_{e : d|e|P} μ(e/d)·x*_e.
  have hd_def : ∀ d : ℕ, d ∈ S.prodPrimes.divisors →
      S.nu d * optimalSelbergWeight S d =
        ∑ e ∈ S.prodPrimes.divisors, if d ∣ e then (μ (e / d) : ℝ) * optimalSelbergX S e else 0 := by
    intro d hd
    have hdvd : d ∣ S.prodPrimes := (Nat.mem_divisors.mp hd).1
    have hν : S.nu d ≠ 0 := S.nu_ne_zero hdvd
    unfold optimalSelbergWeight
    rw [dif_pos hdvd]
    field_simp [hν]
  -- Exchange sums: Σ_d [l|d]·Σ_e [d|e]·μ(e/d)·x*_e = Σ_e x*_e·Σ_{d : l|d|e} μ(e/d).
  have hswap :
      (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then
          (∑ e ∈ S.prodPrimes.divisors, if d ∣ e then (μ (e / d) : ℝ) * optimalSelbergX S e else 0)
        else 0) =
        ∑ e ∈ S.prodPrimes.divisors, optimalSelbergX S e *
          (∑ d ∈ S.prodPrimes.divisors,
            if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) := by
    -- First express the inner sum multiplicatively, then exchange sums.
    calc
      (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then
          (∑ e ∈ S.prodPrimes.divisors, if d ∣ e then (μ (e / d) : ℝ) * optimalSelbergX S e else 0)
        else 0)
          = ∑ d ∈ S.prodPrimes.divisors,
              ∑ e ∈ S.prodPrimes.divisors,
                if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) * optimalSelbergX S e else 0) else 0 := by
              apply Finset.sum_congr rfl
              intro d hd
              by_cases hld : l ∣ d
              · simp [hld]
              · simp [hld]
      _ = ∑ e ∈ S.prodPrimes.divisors,
              ∑ d ∈ S.prodPrimes.divisors,
                if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) * optimalSelbergX S e else 0) else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ e ∈ S.prodPrimes.divisors, optimalSelbergX S e *
              (∑ d ∈ S.prodPrimes.divisors,
                if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) := by
              apply Finset.sum_congr rfl
              intro e he
              -- Factor the inner sum: Σ_d [l|d]·[d|e]·μ(e/d)·x*_e = x*_e·Σ_d [l|d]·[d|e]·μ(e/d).
              have hinner : (∑ d ∈ S.prodPrimes.divisors,
                    if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) * optimalSelbergX S e else 0) else 0) =
                  optimalSelbergX S e *
                    (∑ d ∈ S.prodPrimes.divisors,
                      if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) := by
                rw [mul_comm]
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro d hd
                by_cases hld : l ∣ d
                · by_cases hde : d ∣ e
                  · simp [hld, hde]
                  · simp [hld, hde]
                · simp [hld]
              rw [hinner]
  -- For fixed e, the inner sum Σ_{d : l|d|e} μ(e/d) equals [e=l].
  have hinner_delta : ∀ e : ℕ, e ∈ S.prodPrimes.divisors →
      (∑ d ∈ S.prodPrimes.divisors,
        if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) =
        if e = l then (1 : ℝ) else 0 := by
    intro e he
    have hdvd_e : e ∣ S.prodPrimes := (Nat.mem_divisors.mp he).1
    have he0 : e ≠ 0 := Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hdvd_e (Nat.pos_of_ne_zero S.prodPrimes_ne_zero))
    have hrestrict :
        (∑ d ∈ S.prodPrimes.divisors,
          if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) =
          ∑ d ∈ e.divisors, if l ∣ d then (μ (e / d) : ℝ) else 0 := by
      -- Combine the two conditions and restrict the index set to e.divisors.
      have hfilt : S.prodPrimes.divisors.filter (fun d => l ∣ d ∧ d ∣ e) =
          e.divisors.filter (fun d => l ∣ d) := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · intro h
          exact ⟨⟨h.2.2, he0⟩, h.2.1⟩
        · intro h
          exact ⟨⟨h.1.1.trans hdvd_e, S.prodPrimes_ne_zero⟩, h.2, h.1.1⟩
      calc
        (∑ d ∈ S.prodPrimes.divisors,
          if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0)
            = ∑ d ∈ S.prodPrimes.divisors, if l ∣ d ∧ d ∣ e then (μ (e / d) : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro d hd
              by_cases hld : l ∣ d <;> by_cases hde : d ∣ e <;> simp [hld, hde]
        _ = ∑ d ∈ (S.prodPrimes.divisors.filter (fun d => l ∣ d ∧ d ∣ e)), (μ (e / d) : ℝ) := by
              rw [← Finset.sum_filter]
        _ = ∑ d ∈ (e.divisors.filter (fun d => l ∣ d)), (μ (e / d) : ℝ) := by
              rw [hfilt]
        _ = ∑ d ∈ e.divisors, if l ∣ d then (μ (e / d) : ℝ) else 0 := by
              rw [Finset.sum_filter]
    rw [hrestrict]
    by_cases hle : l ∣ e
    · rw [sum_moebius_quotient_of_dvd he0 hle]
    · have hne : e ≠ l := by intro hel; apply hle; rw [hel]
      -- If l does not divide e, the inner sum is empty.
      have hsum0 : (∑ d ∈ e.divisors, if l ∣ d then (μ (e / d) : ℝ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        by_cases hld : l ∣ d
        · exfalso
          apply hle
          exact hld.trans (Nat.mem_divisors.mp hd).1
        · simp [hld]
      rw [hsum0]
      simp [hne]
  -- Combine the identities.
  calc
    optimalSelbergX S l
        = ∑ e ∈ S.prodPrimes.divisors, optimalSelbergX S e *
            (if e = l then (1 : ℝ) else 0) := by
          have hlm : l ∈ S.prodPrimes.divisors :=
            Nat.mem_divisors.mpr ⟨hl, S.prodPrimes_ne_zero⟩
          simp_rw [mul_ite, mul_one, mul_zero]
          rw [← Finset.sum_ite_eq_of_mem' S.prodPrimes.divisors l (fun e => optimalSelbergX S e) hlm]
    _ = ∑ e ∈ S.prodPrimes.divisors, optimalSelbergX S e *
          (∑ d ∈ S.prodPrimes.divisors,
            if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [← hinner_delta e he]
    _ = ∑ d ∈ S.prodPrimes.divisors, if l ∣ d then
            (∑ e ∈ S.prodPrimes.divisors, if d ∣ e then (μ (e / d) : ℝ) * optimalSelbergX S e else 0)
          else 0 := hswap.symm
    _ = ∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * optimalSelbergWeight S d else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hld : l ∣ d
          · rw [← hd_def d hd]
          · simp [hld]

/-- **Optimal main-term identity**:
`mainSum(Λ²w*) = (Σ_{l|P} selbergTerms l)⁻¹`,
the equality case of `mainSum_cauchy_schwarz_lower_bound`. -/
theorem optimalSelbergMainSum_eq (S : BoundingSieve) :
    S.mainSum (BoundingSieve.lambdaSquared (optimalSelbergWeight S)) = selbergMainTerm S := by
  rw [mainSum_diag_via_mathlib]
  -- The inner sum equals x*_l.
  have hx : ∀ l ∈ S.prodPrimes.divisors,
      (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * optimalSelbergWeight S d else 0) =
        optimalSelbergX S l := by
    intro l hl
    exact (optimalSelbergX_eq_sum_nu_mul_weight S l ((Nat.mem_divisors.mp hl).1)).symm
  have hsum1 : (∑ l ∈ S.prodPrimes.divisors,
        (S.selbergTerms l)⁻¹ *
          (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * optimalSelbergWeight S d else 0) ^ 2) =
      ∑ l ∈ S.prodPrimes.divisors, (S.selbergTerms l)⁻¹ * (optimalSelbergX S l) ^ 2 := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [← hx l hl]
  rw [hsum1]
  -- Expand x*_l = g(l)·μ(l)·T; each summand becomes T²·g(l).
  have hsum2 : (∑ l ∈ S.prodPrimes.divisors,
        (S.selbergTerms l)⁻¹ * (optimalSelbergX S l) ^ 2) =
      (selbergMainTerm S) ^ 2 * (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have hg : S.selbergTerms l ≠ 0 := (S.selbergTerms_pos ((Nat.mem_divisors.mp hl).1)).ne'
    have hsq := S.squarefree_of_mem_divisors_prodPrimes hl
    have hμsq : ((μ l : ℝ) ^ 2) = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    unfold optimalSelbergX
    have hx2 : (S.selbergTerms l * (μ l : ℝ) * selbergMainTerm S) ^ 2 =
        (S.selbergTerms l) ^ 2 * ((μ l : ℝ) ^ 2) * (selbergMainTerm S) ^ 2 := by ring
    rw [hx2, hμsq]
    field_simp [hg]
  rw [hsum2]
  -- T²·Σg = T
  unfold selbergMainTerm
  have hsum_ne : (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l) ≠ 0 := by
    have h1mem : (1 : ℕ) ∈ S.prodPrimes.divisors :=
      Nat.mem_divisors.mpr ⟨one_dvd S.prodPrimes, S.prodPrimes_ne_zero⟩
    have hpos1 : 0 < S.selbergTerms 1 := by
      rw [BoundingSieve.selbergTerms_apply]
      have hν1 : S.nu 1 = 1 := S.nu_mult.map_one
      simp [hν1]
    exact ne_of_gt (Finset.sum_pos
      (fun l hl => S.selbergTerms_pos ((Nat.mem_divisors.mp hl).1)) ⟨1, h1mem⟩)
  field_simp [hsum_ne]

/-- **Finite Selberg upper bound**: optimal Λ² weights minimize
the main term and give
`siftedSum ≤ totalMass·(Σ_{l|P} selbergTerms l)⁻¹ + errSum(Λ²w*)`.
This is the exact finite form of `S ≤ X/G(z) + R`
(Halberstam--Richert 1974 Ch. 3).
In the Chen application, estimates of the indicated
`(Σg)⁻¹ ≈ 8𝔖(N)/log N` shape and `errSum ≪ N/log^A N`
require separate Mertens/singular-series and weighted Pan inputs. -/
theorem selberg_upper_bound_optimal (S : BoundingSieve) :
    ∃ w : ℕ → ℝ, w 1 = 1 ∧
      S.siftedSum ≤
        S.totalMass * (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l)⁻¹ +
          S.errSum (BoundingSieve.lambdaSquared w) := by
  refine ⟨optimalSelbergWeight S, optimalSelbergWeight_one S, ?_⟩
  have h := omega_upper_bound_via_mathlib S (optimalSelbergWeight S) (optimalSelbergWeight_one S)
  rw [optimalSelbergMainSum_eq S] at h
  simpa [selbergMainTerm] using h

/-- **Sieve-product form of the Selberg main term**:
for any `BoundingSieve`,
`(Σ_{d|P} selbergTerms d)⁻¹ = ∏_{p|P} (1−ν(p))`.
Invert `selbergSum_eq_prod_inv`, namely
`Σg = ∏(1−ν(p))⁻¹`.
For a `SieveProblem`, the product is `sieveProduct`
(`selbergMainTerm_eq_sieveProduct`). -/
theorem selbergMainTerm_eq_prod_one_sub_nu (S : BoundingSieve) :
    (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l)⁻¹ =
      ∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p) := by
  calc
    (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l)⁻¹
        = (∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p)⁻¹)⁻¹ := by
            rw [selbergSum_eq_prod_inv]
    _ = ∏ p ∈ S.prodPrimes.primeFactors, ((1 - S.nu p)⁻¹)⁻¹ := by
            rw [← Finset.prod_inv_distrib]
    _ = ∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p) := by
            apply Finset.prod_congr rfl
            intro p hp
            have hp_p : p.Prime := Nat.prime_of_mem_primeFactors hp
            have hp_dvd : p ∣ S.prodPrimes := Nat.dvd_of_mem_primeFactors hp
            have hne : (1 - S.nu p) ≠ 0 := by
              linarith [S.nu_lt_one_of_prime p hp_p hp_dvd]
            exact inv_inv (1 - S.nu p)

/-- For a classical `SieveProblem`,
`(Σ_{d|P} selbergTerms d)⁻¹ = sieveProduct`. -/
theorem selbergMainTerm_eq_sieveProduct (SP : SieveProblem) :
    (∑ l ∈ SP.prodPrimes.divisors, SP.selbergTerms l)⁻¹ = sieveProduct SP := by
  rw [selbergMainTerm_eq_prod_one_sub_nu SP.toBoundingSieve, sieveProduct_eq_prod_one_sub_nu SP]

/-- **Sieve-product upper bound**: for a `SieveProblem`,
optimal Λ² weights give
`siftedSum ≤ totalMass·V(z) + errSum(Λ²w*)`,
where `V(z) = sieveProduct`.
The identity `(Σg)⁻¹ = V(z)` is the main-term form used in
the Chen upper bound for `Ω`; estimates for `V(z)` come from
Mertens and singular-series analysis. -/
theorem selberg_upper_bound_sieveProduct (SP : SieveProblem) :
    ∃ w : ℕ → ℝ, w 1 = 1 ∧
      SP.siftedSum ≤ SP.totalMass * sieveProduct SP +
        SP.errSum (BoundingSieve.lambdaSquared w) := by
  obtain ⟨w, hw1, hbound⟩ := selberg_upper_bound_optimal SP.toBoundingSieve
  refine ⟨w, hw1, ?_⟩
  rwa [selbergMainTerm_eq_sieveProduct SP] at hbound

/-! ## 3.7 Moebius weights attain the full-divisor optimum -/

/-- Upper-interval divisor sum for multiplicative `f`:
`Σ_{e : d|e|P} f(e) = f(d)·Σ_{g|P/d} f(g)`. -/
private lemma sum_multiplicative_over_supersets {S : BoundingSieve} {d : ℕ}
    (hd : d ∣ S.prodPrimes) (f : ℕ → ℝ)
    (hf_mul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n) :
    (∑ e ∈ S.prodPrimes.divisors, if d ∣ e then f e else 0) =
      f d * (∑ g ∈ (S.prodPrimes / d).divisors, f g) := by
  have hP0 : S.prodPrimes ≠ 0 := S.prodPrimes_ne_zero
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hP0))
  have hPd : S.prodPrimes / d ≠ 0 :=
    Nat.ne_of_gt (Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hd) (Nat.pos_of_ne_zero hP0))
  calc
    (∑ e ∈ S.prodPrimes.divisors, if d ∣ e then f e else 0)
        = ∑ e ∈ (S.prodPrimes.divisors.filter (fun e => d ∣ e)), f e := by
            rw [← Finset.sum_filter]
    _ = ∑ g ∈ (S.prodPrimes / d).divisors, f (d * g) := by
            refine Finset.sum_bij (fun e he => e / d) ?_ ?_ ?_ ?_
            · intro e he
              rw [Finset.mem_filter] at he
              rcases he with ⟨heP, hde⟩
              have he_dvd : e ∣ S.prodPrimes := (Nat.mem_divisors.mp heP).1
              have hmain : d * (e / d) ∣ d * (S.prodPrimes / d) := by
                rw [Nat.mul_div_cancel' hde, Nat.mul_div_cancel' hd]
                exact he_dvd
              have hq : e / d ∣ S.prodPrimes / d :=
                (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hd0)).mp hmain
              exact Nat.mem_divisors.mpr ⟨hq, hPd⟩
            · intro e1 he1 e2 he2 hdiv
              have hde1 : d ∣ e1 := (Finset.mem_filter.mp he1).2
              have hde2 : d ∣ e2 := (Finset.mem_filter.mp he2).2
              calc
                e1 = d * (e1 / d) := (Nat.mul_div_cancel' hde1).symm
                _ = d * (e2 / d) := by rw [hdiv]
                _ = e2 := Nat.mul_div_cancel' hde2
            · intro g hg
              have hg_dvd : g ∣ S.prodPrimes / d := (Nat.mem_divisors.mp hg).1
              have hmain : d * g ∣ d * (S.prodPrimes / d) :=
                (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hd0)).mpr hg_dvd
              have hdvd : d * g ∣ S.prodPrimes := by rwa [Nat.mul_div_cancel' hd] at hmain
              refine ⟨d * g, ?_, ?_⟩
              · rw [Finset.mem_filter]
                exact ⟨Nat.mem_divisors.mpr ⟨hdvd, hP0⟩, dvd_mul_right d g⟩
              · rw [mul_comm]
                exact Nat.mul_div_cancel g (Nat.pos_of_ne_zero hd0)
            · intro e he
              rw [Finset.mem_filter] at he
              rcases he with ⟨heP, hde⟩
              rw [Nat.mul_div_cancel' hde]
    _ = f d * (∑ g ∈ (S.prodPrimes / d).divisors, f g) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro g hg
            have hg_dvd : g ∣ S.prodPrimes / d := (Nat.mem_divisors.mp hg).1
            have hmain : d * g ∣ d * (S.prodPrimes / d) :=
              (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hd0)).mpr hg_dvd
            have hdvd : d * g ∣ S.prodPrimes := by rwa [Nat.mul_div_cancel' hd] at hmain
            have hsq_dg : Squarefree (d * g) :=
              Squarefree.squarefree_of_dvd hdvd S.prodPrimes_squarefree
            have hcop : d.Coprime g := Nat.coprime_of_squarefree_mul hsq_dg
            exact hf_mul hcop

/-- Pointwise multiplicativity of `ν·μ`:
`(νμ)(m·n) = (νμ)(m)·(νμ)(n)` for coprime `m,n`. -/
private lemma nu_mul_moebius_mul {S : BoundingSieve} {m n : ℕ} (hcop : m.Coprime n) :
    S.nu (m * n) * (μ (m * n) : ℝ) =
      (S.nu m * (μ m : ℝ)) * (S.nu n * (μ n : ℝ)) := by
  have hν := S.nu_mult.map_mul_of_coprime hcop
  have hμ := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have hμR : ((μ (m * n) : ℤ) : ℝ) = ((μ m : ℤ) : ℝ) * ((μ n : ℤ) : ℝ) := by
    exact_mod_cast hμ
  rw [hν, hμR]
  ring

/-- For squarefree `m`,
`Σ_{f|m} ν(f)·μ(f) = ∏_{q|m}(1−ν(q))`. -/
private lemma sum_nu_mul_moebius_factors (S : BoundingSieve) (m : ℕ) (hm : Squarefree m) :
    (∑ f ∈ m.divisors, S.nu f * (μ f : ℝ)) =
      ∏ q ∈ m.primeFactors, (1 - S.nu q) := by
  let F : ArithmeticFunction ℝ :=
    { toFun := fun d : ℕ => S.nu d * (μ d : ℝ), map_zero' := by simp }
  have hF : F.IsMultiplicative := by
    constructor
    · simp [F, S.nu_mult.map_one]
    · intro a b hab
      have h := nu_mul_moebius_mul (S := S) hab
      simpa [F] using h
  have hfac := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree hF hm
  change (∑ f ∈ m.divisors, F f) = ∏ q ∈ m.primeFactors, (1 - S.nu q)
  rw [← hfac]
  apply Finset.prod_congr rfl
  intro q hq
  have hq_p : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hμq : ((μ q : ℤ) : ℝ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree hq_p.squarefree]
    have hΩ : ArithmeticFunction.cardFactors q = 1 :=
      ArithmeticFunction.cardFactors_apply_prime hq_p
    rw [hΩ]
    norm_num
  simp [F, hμq]
  ring

/-- **Moebius weights satisfy the optimal diagonal equations**:
`Σ_{d : l|d|P} ν(d)·μ(d) = x*_l = g(l)·μ(l)·T`. -/
theorem sum_nu_mul_moebius_over_supersets (S : BoundingSieve) (l : ℕ) (hl : l ∣ S.prodPrimes) :
    (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * (μ d : ℝ) else 0) =
      S.selbergTerms l * (μ l : ℝ) * selbergMainTerm S := by
  have hsup := sum_multiplicative_over_supersets (S := S) (d := l) hl
    (fun d => S.nu d * (μ d : ℝ)) (fun {m n} hcop => nu_mul_moebius_mul hcop)
  have hfact : (∑ f ∈ (S.prodPrimes / l).divisors, S.nu f * (μ f : ℝ)) =
      ∏ q ∈ (S.prodPrimes / l).primeFactors, (1 - S.nu q) := by
    exact sum_nu_mul_moebius_factors S (S.prodPrimes / l)
      (Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hl) S.prodPrimes_squarefree)
  have hR : S.selbergTerms l * (μ l : ℝ) * selbergMainTerm S =
      (μ l : ℝ) * S.nu l * (∏ q ∈ (S.prodPrimes / l).primeFactors, (1 - S.nu q)) := by
    have hsq_l : Squarefree l := Squarefree.squarefree_of_dvd hl S.prodPrimes_squarefree
    have hl0 : l ≠ 0 := Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hl (Nat.pos_of_ne_zero S.prodPrimes_ne_zero))
    have hPd0 : S.prodPrimes / l ≠ 0 :=
      Nat.ne_of_gt (Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hl) (Nat.pos_of_ne_zero S.prodPrimes_ne_zero))
    have hg : S.selbergTerms l = S.nu l * ∏ q ∈ l.primeFactors, (1 - S.nu q)⁻¹ := by
      rw [BoundingSieve.selbergTerms_apply]
    have hT : selbergMainTerm S = ∏ q ∈ S.prodPrimes.primeFactors, (1 - S.nu q) := by
      unfold selbergMainTerm
      rw [selbergSum_eq_prod_inv]
      rw [Finset.prod_inv_distrib]
      rw [inv_inv]
    have hsplit : (∏ q ∈ S.prodPrimes.primeFactors, (1 - S.nu q)) =
        (∏ q ∈ l.primeFactors, (1 - S.nu q)) *
          (∏ q ∈ (S.prodPrimes / l).primeFactors, (1 - S.nu q)) := by
      have heq : S.prodPrimes = l * (S.prodPrimes / l) := (Nat.mul_div_cancel' hl).symm
      have hcop : l.Coprime (S.prodPrimes / l) := by
        have hsq : Squarefree (l * (S.prodPrimes / l)) := by
          rw [← heq]
          exact S.prodPrimes_squarefree
        exact Nat.coprime_of_squarefree_mul hsq
      calc
        (∏ q ∈ S.prodPrimes.primeFactors, (1 - S.nu q))
            = (∏ q ∈ (l * (S.prodPrimes / l)).primeFactors, (1 - S.nu q)) := by
                conv_lhs => rw [heq]
        _ = (∏ q ∈ l.primeFactors, (1 - S.nu q)) *
              (∏ q ∈ (S.prodPrimes / l).primeFactors, (1 - S.nu q)) := by
                rw [Nat.primeFactors_mul hl0 hPd0,
                  Finset.prod_union (Nat.Coprime.disjoint_primeFactors hcop)]
    have hneA : (∏ q ∈ l.primeFactors, (1 - S.nu q)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro q hq
      have hq_p : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hq_dvd : q ∣ S.prodPrimes := (Nat.dvd_of_mem_primeFactors hq).trans hl
      linarith [S.nu_lt_one_of_prime q hq_p hq_dvd]
    calc
      S.selbergTerms l * (μ l : ℝ) * selbergMainTerm S
          = ((μ l : ℝ) * S.nu l * ∏ q ∈ l.primeFactors, (1 - S.nu q)⁻¹) *
              (∏ q ∈ S.prodPrimes.primeFactors, (1 - S.nu q)) := by
              rw [hg, hT]
              ring
      _ = (μ l : ℝ) * S.nu l *
              (∏ q ∈ l.primeFactors, (1 - S.nu q))⁻¹ *
              (∏ q ∈ l.primeFactors, (1 - S.nu q)) *
              (∏ q ∈ (S.prodPrimes / l).primeFactors, (1 - S.nu q)) := by
              rw [hsplit]
              rw [Finset.prod_inv_distrib]
              ring
      _ = (μ l : ℝ) * S.nu l *
              (∏ q ∈ (S.prodPrimes / l).primeFactors, (1 - S.nu q)) := by
              field_simp [hneA]
  have hL : (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * (μ d : ℝ) else 0) =
      (μ l : ℝ) * S.nu l * (∏ q ∈ (S.prodPrimes / l).primeFactors, (1 - S.nu q)) := by
    calc
      (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * (μ d : ℝ) else 0)
          = (S.nu l * (μ l : ℝ)) *
              (∑ g ∈ (S.prodPrimes / l).divisors, S.nu g * (μ g : ℝ)) := hsup
      _ = (S.nu l * (μ l : ℝ)) * (∏ q ∈ (S.prodPrimes / l).primeFactors, (1 - S.nu q)) := by
              rw [hfact]
      _ = (μ l : ℝ) * S.nu l * (∏ q ∈ (S.prodPrimes / l).primeFactors, (1 - S.nu q)) := by
              ring
  rw [hL, hR]

/-- **Main term for Moebius weights**:
`mainSum(Λ²μ) = (Σ_{d|P} selbergTerms d)⁻¹`. -/
theorem mainSum_lambdaSquared_moebius_eq (S : BoundingSieve) :
    S.mainSum (BoundingSieve.lambdaSquared (fun d => (μ d : ℝ))) = selbergMainTerm S := by
  rw [mainSum_diag_via_mathlib]
  have hx : ∀ l ∈ S.prodPrimes.divisors,
      (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * (μ d : ℝ) else 0) =
        optimalSelbergX S l := by
    intro l hl
    exact sum_nu_mul_moebius_over_supersets S l ((Nat.mem_divisors.mp hl).1)
  have hsum1 : (∑ l ∈ S.prodPrimes.divisors,
        (S.selbergTerms l)⁻¹ *
          (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * (μ d : ℝ) else 0) ^ 2) =
      ∑ l ∈ S.prodPrimes.divisors, (S.selbergTerms l)⁻¹ * (optimalSelbergX S l) ^ 2 := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [← hx l hl]
  rw [hsum1]
  have hsum2 : (∑ l ∈ S.prodPrimes.divisors,
        (S.selbergTerms l)⁻¹ * (optimalSelbergX S l) ^ 2) =
      (selbergMainTerm S) ^ 2 * (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have hg : S.selbergTerms l ≠ 0 := (S.selbergTerms_pos ((Nat.mem_divisors.mp hl).1)).ne'
    have hsq := S.squarefree_of_mem_divisors_prodPrimes hl
    have hμsq : ((μ l : ℝ) ^ 2) = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    unfold optimalSelbergX
    have hx2 : (S.selbergTerms l * (μ l : ℝ) * selbergMainTerm S) ^ 2 =
        (S.selbergTerms l) ^ 2 * ((μ l : ℝ) ^ 2) * (selbergMainTerm S) ^ 2 := by ring
    rw [hx2, hμsq]
    field_simp [hg]
  rw [hsum2]
  unfold selbergMainTerm
  have hsum_ne : (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l) ≠ 0 := by
    have h1mem : (1 : ℕ) ∈ S.prodPrimes.divisors :=
      Nat.mem_divisors.mpr ⟨one_dvd S.prodPrimes, S.prodPrimes_ne_zero⟩
    have hpos1 : 0 < S.selbergTerms 1 := by
      rw [BoundingSieve.selbergTerms_apply]
      have hν1 : S.nu 1 = 1 := S.nu_mult.map_one
      simp [hν1]
    exact ne_of_gt (Finset.sum_pos
      (fun l hl => S.selbergTerms_pos ((Nat.mem_divisors.mp hl).1)) ⟨1, h1mem⟩)
  field_simp [hsum_ne]

/-- **Moebius-weight Selberg upper bound**: with `w=μ`,
`siftedSum ≤ totalMass·(Σ selbergTerms)⁻¹ + errSum(Λ²μ)`;
the coefficients satisfy `|μ| ≤ 1`. -/
theorem selberg_upper_bound_moebius (S : BoundingSieve) :
    S.siftedSum ≤ S.totalMass * (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l)⁻¹ +
      S.errSum (BoundingSieve.lambdaSquared (fun d => (μ d : ℝ))) := by
  have h := omega_upper_bound_via_mathlib S (fun d => (μ d : ℝ)) (by simp)
  rw [mainSum_lambdaSquared_moebius_eq S] at h
  simpa [selbergMainTerm] using h

/-- **Selberg upper bound with the remainder grouped by modulus**:
for the optimal full-divisor Moebius Λ² weights,
`siftedSum ≤ totalMass·(Σ_{d|P} selbergTerms d)⁻¹
 + Σ_{d|P} 3^{ω(d)}·|rem d|`.
This is the exact finite `S ≤ X/G(z) + Σ 3^{ω(d)}|Δ(d)|` form.
The Chen application controls the main term using
Mertens/singular-series estimates and the remainder using
the weighted Pan input. -/
theorem selberg_upper_bound_moebius_pan (S : BoundingSieve) :
    S.siftedSum ≤ S.totalMass * (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l)⁻¹ +
      weightedPanRemainder S (fun d => (3 : ℝ) ^ d.primeFactors.card) := by
  have h := selberg_upper_bound_moebius S
  have hE : S.errSum (BoundingSieve.lambdaSquared (fun d => (μ d : ℝ))) ≤
      weightedPanRemainder S (fun d => (3 : ℝ) ^ d.primeFactors.card) :=
    errSum_lambdaSquared_le_threeOmegaWeightedPanRemainder (S := S)
      (w := fun d => (μ d : ℝ)) (by
        intro d
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one : |μ d| ≤ 1))
  linarith

/-! ## 4. Uniform finite Selberg upper bound -/

/-- **Uniform Selberg upper-bound proposition**.
The classical shape (Halberstam--Richert Ch. 3, Chen application)
for sufficiently large even `N` is
`S(A,z) ≤ X/G(z) + Σ |R_d|`, with `G(z)=Σ_{d|P}g(d)`.
The finite formulation asks for `N₀` such that for every even
`N ≥ N₀` there is a sequence `w`, `w 1 = 1`, satisfying
`siftedSum ≤ totalMass·(Σ_{d|P}g(d))⁻¹ + errSum(Λ²w)`.

The threshold precedes `∀ N`. `selberg_upper_bound_optimal`
proves this for every `BoundingSieve` family without additional
analytic assumptions (`uniformSelbergUpperBound`).
The numerical Chen bound `3.9404·𝔖(N)·N/log²N` still requires
Mertens/singular-series main-term control of the indicated
`(Σg)⁻¹ ≈ 8𝔖(N)/log N` shape and a weighted Pan error estimate
`errSum = O(N/log^A N)`; see `WeightedPan`. -/
def UniformSelbergUpperBound (SP : ℕ → BoundingSieve) : Prop :=
  ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ w : ℕ → ℝ,
        w 1 = 1 ∧
          (SP N).siftedSum ≤
            (SP N).totalMass *
                (∑ l ∈ (SP N).prodPrimes.divisors, (SP N).selbergTerms l)⁻¹ +
              (SP N).errSum (BoundingSieve.lambdaSquared w)

/-- Optimal Selberg weights give the uniform finite upper bound
for every sieve family. -/
theorem uniformSelbergUpperBound (SP : ℕ → BoundingSieve) :
    UniformSelbergUpperBound SP := by
  refine ⟨0, ?_⟩
  intro N hN₀ hEven
  exact selberg_upper_bound_optimal (SP N)

/-! ## 5. Numerical coefficient in Chen's theorem -/

/-- `8 × 0.49254 = 3.94032`: the arithmetic behind the main-term
coefficient in the Chen upper bound for `Ω`, combining the
numerical integral `0.49254` in Chen 1973, equation (28),
with the Selberg diagonalization coefficient 8. -/
theorem coefficient_product : (8 : ℝ) * 0.49254 = 3.94032 := by
  norm_num

end AnalyticNumberTheory.Sieve
