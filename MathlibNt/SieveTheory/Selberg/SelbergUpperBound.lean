import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.GCD
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Exp
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem
import AnalyticNumberTheory.Sieve.SelbergUpperBound

/-!
# MathlibNt.SieveTheory.SelbergUpperBound

## Selberg sieve and the target bound Ω ≤ 3.9404 𝔖(N) N/log²N

The Selberg sieve is a central tool for the upper bound on Ω in Chen's theorem.
Selberg upper-bound weights λ_d lead to a main term M₁ and a remainder R.

**Classical proof outline** (Liu 2022, §III):

1. **Selberg weights** (Lemma 3): construct λ_d with
   - λ₁ = 1 and λ_d = 0 for d > z or d ∤ Q;
   - |λ_d| ≤ 1;
   - Σ_{d₁,d₂} λ_{d₁}λ_{d₂}/φ([d₁,d₂]) = [8 + O(ε)] 𝔖(N)/log N.

2. **Numerical integration** (Lemma 4):
   Σ_a f(a)/(a log(N/a)) ≤ 0.49254/log N.

3. **Main term**: for suitably controlled ε,
   M₁ ≤ [8 + O(ε)] · 0.49254 · 𝔖(N) N/log²N ≤ 3.94033 𝔖(N) N/log²N.

4. **Remainder**: R ≪ N/log^A N, using Pan's mean-value theorem.

5. **Combination**: Ω ≤ M₁ + |R| ≤ 3.9404 𝔖(N) N/log²N.

This module connects the development to `Mathlib.NumberTheory.SelbergSieve`
and proves finite algebraic and divisor-sum results. The interfaces for the
numerical main and error terms below allow constants depending on a fixed N;
they do not establish the uniform optimized bounds in this classical outline.

References:
  - Selberg, A. (1947), Norske Vid. Selsk. Forh. Trondheim 19, 75-79
  - Liu, Z. (2022), arXiv:2203.07871, Lemma 3-4, §III
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 3
  - Mathlib `SelbergSieve.lean`: BoundingSieve, SelbergSieve, Λ² sieve
-/

namespace MathlibNt.SieveTheory.SelbergUpperBound

open Real Finset
open MathlibNt.SieveTheory.MertensTheorem

open scoped Classical
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

/-! ## 1. Selberg sieve weights (Lemma 3) -/

/-- Q is the product of primes ≤ z = N^(1/4 - ε/2) that do not divide N. -/
noncomputable def selbergQ (N : ℕ) (ε : ℝ) : ℕ :=
  ((Finset.range ((Nat.floor ((N : ℝ) ^ (1/4 - ε/2))) + 1)).filter
    (fun p => p.Prime ∧ ¬ p ∣ N)).prod id

/-- **Selberg weight conditions** (Lemma 3, Liu 2022).
The structure records:

1. λ₁ = 1
2. λ_d = 0 when d > z or d ∤ Q
3. |λ_d| ≤ 1

The classical optimized weights additionally satisfy
Σ_{d₁,d₂} λ_{d₁}λ_{d₂}/φ([d₁,d₂]) = [8 + O(ε)] 𝔖(N)/log N;
this quadratic-form estimate is not a field of the structure. -/
structure SelbergWeights (N : ℕ) (ε : ℝ) where
  /-- The weight function λ_d. -/
  lambda : ℕ → ℝ
  /-- λ₁ = 1 -/
  lambda_one : lambda 1 = 1
  /-- λ_d = 0 when d > z or d ∤ Q. -/
  lambda_support : ∀ d : ℕ, d > (Nat.floor ((N : ℝ) ^ (1/4 - ε/2))) ∨
    ¬ d ∣ selbergQ N ε → lambda d = 0
  /-- |λ_d| ≤ 1 -/
  lambda_bounded : ∀ d : ℕ, |lambda d| ≤ 1

/-- **Pointwise interface for Selberg weights**, motivated by Lemma 3:

 Σ_{d₁,d₂} λ_{d₁}λ_{d₂}/φ([d₁,d₂]) = [8 + O(ε)] 𝔖(N)/log N

The uniform version is a key ingredient in estimating the main term M₁ for Ω.

The constant `C` here has no uniformity, positivity, or compatibility
requirements with other sieve data. Explicit δ₁ weights therefore suffice,
with `C` absorbing the difference. This is not the optimized Selberg-weight
estimate of Liu/Wang, which needs a controlled error suitable for comparing
main terms. -/
theorem selberg_sieve_weights_exist (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1/2)
    (hN : 2 ≤ N) :
    ∃ (SW : SelbergWeights N ε) (C : ℝ),
      abs ((selbergQ N ε).divisors.sum (fun d₁ =>
          (selbergQ N ε).divisors.sum (fun d₂ =>
            SW.lambda d₁ * SW.lambda d₂ / Nat.totient (Nat.lcm d₁ d₂)) -
        8 * (1 : ℝ) / log N)) ≤
        C * ε / log N := by
  have hexp : 0 ≤ 1 / 4 - ε / 2 := by linarith
  have hfloor : 1 ≤ Nat.floor ((N : ℝ) ^ (1 / 4 - ε / 2)) := by
    rw [Nat.one_le_floor_iff]
    calc
      (1 : ℝ) = 1 ^ (1 / 4 - ε / 2 : ℝ) := by simp
      _ ≤ (N : ℝ) ^ (1 / 4 - ε / 2 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) (by exact_mod_cast (by omega : 1 ≤ N)) hexp
  let SW : SelbergWeights N ε :=
    { lambda := fun d => if d = 1 then 1 else 0
      lambda_one := by simp
      lambda_support := by
        intro d hd
        by_cases hd1 : d = 1
        · subst d
          exfalso
          rcases hd with hlarge | hndvd
          · exact (not_lt_of_ge hfloor) hlarge
          · exact hndvd (Nat.one_dvd _)
        · simp [hd1]
      lambda_bounded := by
        intro d
        by_cases hd1 : d = 1 <;> simp [hd1] }
  have hlog : 0 < log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  set E : ℝ := abs ((selbergQ N ε).divisors.sum (fun d₁ =>
      (selbergQ N ε).divisors.sum (fun d₂ =>
        SW.lambda d₁ * SW.lambda d₂ / Nat.totient (Nat.lcm d₁ d₂)) -
      8 * (1 : ℝ) / log N))
  refine ⟨SW, E * log N / ε, ?_⟩
  change E ≤ E * log (N : ℝ) / ε * ε / log (N : ℝ)
  field_simp
  rfl

/-! ## 2. Numerical integration (Lemma 4) -/

/-- **Pointwise interface motivated by Lemma 4 (Liu 2022)**.
For the indicator f(a) of a = p₁p₂ satisfying the range conditions, the
classical target is

  Σ_a f(a)/(a log(N/a)) ≤ 0.49254 / log N

Partial summation leads to the double-integral expression
  = (1/log N) ∫_{1/10}^{1/3} dα/α ∫_{1/3}^{(1-α)/2} dβ/(β(1-α-β))
  < 0.49254 / log N

Here `C` may depend on the individual N, with no uniformity requirement.
This interface gives only the algebraic existence of a pointwise remainder,
not a formalization of the uniform analytic integral estimate above. -/
theorem lemma4_numerical_bound (N : ℕ) (hN : 2 ≤ N) :
    ∃ C : ℝ,
      (Finset.range (N + 1)).sum (fun a =>
        (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
            (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
            (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
            a = p₁ * p₂ then (1 : ℝ) else 0) /
          (a * log ((N : ℝ) - a))) ≤
        0.49254 / log N + C / (log N) ^ 2 := by
  let S : ℝ := (Finset.range (N + 1)).sum (fun a =>
    (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
        (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
        (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
        a = p₁ * p₂ then (1 : ℝ) else 0) /
      (a * log ((N : ℝ) - a)))
  let K : ℝ := 0.49254 / log N
  refine ⟨(S - K) * (log N) ^ 2, ?_⟩
  change S ≤ K + (S - K) * (log (N : ℝ)) ^ 2 / (log (N : ℝ)) ^ 2
  have hlog : log (N : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < N)))
  field_simp
  ring_nf
  rfl

/-- Numerical margin used by the Lemma 4 interface: `0.49253 < 0.49254`.

This theorem does **not** formalize the motivating double integral.
The integral estimate in the literature requires a separate formalization
using `MeasureTheory` / `IntervalIntegral`. -/
theorem integral_margin :
    (0.49253 : ℝ) < 0.49254 := by
  norm_num

/-! ## 3. Estimating the main term M₁ -/

/-- The logarithmic-integral approximation term used here. -/
noncomputable def logarithmicIntegral_approx_term (x : ℝ) : ℝ := x / log x

/-- Interface with the shape of li(x) = x/log x + O(x/log²x).

Since `logarithmicIntegral_approx_term x = x / log x` by definition,
the difference is zero and C = 0 suffices. This is not an estimate of the
analytic logarithmic integral. -/
theorem logarithmicIntegral_approx (x : ℝ) (hx : 2 ≤ x) :
    ∃ C : ℝ, |logarithmicIntegral_approx_term x - x / log x| ≤ C * x / (log x) ^ 2 := by
  refine ⟨0, ?_⟩
  unfold logarithmicIntegral_approx_term
  rw [sub_self, abs_zero]
  positivity

/-- A pointwise big-O interface is algebraic once its scale is positive. -/
private lemma exists_multiplicative_error (x b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, x ≤ C * b := by
  refine ⟨x / b, ?_⟩
  rw [div_mul_cancel₀ _ (ne_of_gt hb)]

/-- Version with an explicit main term. -/
private lemma exists_additive_error (x m b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, x ≤ m + C * b := by
  refine ⟨(x - m) / b, ?_⟩
  rw [div_mul_cancel₀ _ (ne_of_gt hb)]
  linarith

/-- **Main term M₁, with a pointwise remainder**:
  M₁ = Σ_{d₁,d₂} λ_{d₁}λ_{d₂}/φ([d₁,d₂]) · Σ_a f(a) · li(N/a)

The classical Lemmas 3 and 4, with controlled errors, would give
  M₁ ≤ [8 + O(ε)] 𝔖(N)/log N · 0.49254 N/log N
     ≤ 3.94033 𝔖(N) N/log²N.

`SelbergWeights` encodes normalization, support, and `|lambda d| ≤ 1`,
but not optimality or the quadratic-form estimate above. These structural
hypotheses do not imply a remainder-free `3.94033` bound for arbitrary `SW`.
This theorem retains the existence of an additive remainder for fixed N;
a uniform controlled `C` requires the actual Selberg quadratic-form estimate. -/
theorem main_term_bound (N : ℕ) (ε : ℝ) (_hε : 0 < ε) (_hε' : ε < 1/2)
    (hN : 2 ≤ N) (SW : SelbergWeights N ε) :
    ∃ C : ℝ,
      (selbergQ N ε).divisors.sum (fun d₁ =>
        (selbergQ N ε).divisors.sum (fun d₂ =>
          SW.lambda d₁ * SW.lambda d₂ / Nat.totient (Nat.lcm d₁ d₂) *
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ then (1 : ℝ) else 0) *
            logarithmicIntegral_approx_term ((N : ℝ) / a)))) ≤
        3.94033 * (1 : ℝ) * (N : ℝ) / (log N) ^ 2 +
          C * (N : ℝ) / (log N) ^ 10 := by
  have hlog : 0 < log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hscale : 0 < (N : ℝ) / (log N) ^ 10 :=
    div_pos (by exact_mod_cast (by omega : 0 < N)) (pow_pos hlog 10)
  simp only [mul_div_assoc]
  exact exists_additive_error _ _ _ hscale

/-- 8 × 0.49254 = 3.94032 -/
theorem coefficient_product : (8 : ℝ) * 0.49254 = 3.94032 := by
  norm_num

/-! ## 4. Estimating the remainder R -/

/-- Local definition: π(x; q, l) = |{p ≤ x : p prime, p ≡ l (mod q)}|. -/
def primesInAP (x q l : ℕ) : ℕ :=
  ((range (x + 1)).filter (fun p => p.Prime ∧ p ≡ l [MOD q])).card

/-- **Remainder R**: the Selberg sieve expansion leads to

  |R| ≤ Σ_{d|Q, d ≤ N^(1/2-ε)} 3^ω(d) |Σ_a f(a) Δ(N; a, d, N)|

The factor 3^ω(d) counts pairs (d₁,d₂) with [d₁,d₂] = d.
The intended uniform estimate R ≪ N/log^A N uses Pan's mean-value theorem.

The quantifiers here allow `C` to depend on the individual N and the entire
error sum. This establishes only a pointwise algebraic interface, not the
uniform constant required by Pan's mean-value theorem. -/
theorem error_term_bound (N : ℕ) (ε : ℝ) (A : ℝ) (_hA : 0 < A) (_hε : 0 < ε)
    (hN : 2 ≤ N) (_SW : SelbergWeights N ε) :
    ∃ C : ℝ,
      abs (((selbergQ N ε).divisors.filter (fun (d : ℕ) =>
          (d : ℝ) ≤ (N : ℝ) ^ (1/2 - ε))).sum (fun (d : ℕ) =>
        3 ^ (d.primeFactors.card) *
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ then (1 : ℝ) else 0) *
            ((primesInAP N d (N % d) : ℝ) -
              logarithmicIntegral_approx_term ((N : ℝ) / a) / Nat.totient d)))) ≤
        C * (N : ℝ) / (log N) ^ A := by
  have hlog : 0 < log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hscale : 0 < (N : ℝ) / (log N) ^ A :=
    div_pos (by exact_mod_cast (by omega : 0 < N)) (Real.rpow_pos_of_pos hlog A)
  simp only [mul_div_assoc]
  exact exists_multiplicative_error _ _ hscale

/-- Origin of 3^ω(d): the number of pairs (d₁, d₂) with [d₁, d₂] = d is 3^ω(d).

**This holds only for squarefree d**. At each prime factor p of d,
where v_p(d) = 1, the exponents in (d₁, d₂) have three possibilities:
  (0, 1), (1, 0), (1, 1)
and hence the total is 3^ω(d).

For nonsquarefree d, the formula is ∏_p (2v_p(d) + 1), not 3^ω(d).
For example, d = 4 gives 5 pairs, whereas 3^1 = 3.
In Chen's sieve, d | Q and Q is a product of distinct primes, so d is squarefree.

A strong-induction proof has the following structure:
- Base: d = 1 gives count = 1 = 3^0.
- Step: d = p · d', with p prime and gcd(p, d') = 1.
  - divisors(d) = divisors(d') ⊔ (p · divisors(d')), by coprimality.
  - Three cases each give f(d') pairs:
    A) p|d₁, p|d₂: lcm(pa, pb) = p·lcm(a,b) = p·d' ⟺ lcm(a,b) = d'
    B) p|d₁, p∤d₂: lcm(pa, b) = p·lcm(a,b), since gcd(p,b)=1; as above
    C) p∤d₁, p|d₂: symmetric to B
    D) p∤d₁, p∤d₂: impossible, since then p ∤ lcm(d₁,d₂) = d
  - Thus f(d) = 3·f(d') = 3·3^ω(d') = 3^(ω(d')+1) = 3^ω(d).
The proof below applies Mathlib's existing counting theorem. -/
theorem lcm_pair_count (d : ℕ) (_hd : d ≠ 0) (hsq : Squarefree d) :
    ((d.divisors ×ˢ d.divisors).filter (fun ⟨d₁, d₂⟩ => Nat.lcm d₁ d₂ = d)).card =
      3 ^ d.primeFactors.card := by
  -- Apply Mathlib's Nat.card_pair_lcm_eq (Mathlib.Algebra.Order.Antidiag.Nat):
  -- for squarefree n, #{(d₁,d₂) ∈ divisors(n)² | lcm(d₁,d₂) = n} = 3^ω(n),
  -- where ω(n) = ArithmeticFunction.cardDistinctFactors n = n.primeFactorsList.dedup.length.
  -- For squarefree n, primeFactorsList has no repetitions, so ω(n) = n.primeFactors.card.
  have hω : d.primeFactors.card = ArithmeticFunction.cardDistinctFactors d := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
      Nat.toFinset_factors]
  rw [hω, ← Nat.card_pair_lcm_eq hsq]

/-! ## 5. Combined upper-bound interfaces for Ω -/

/-- **Combined pointwise interface for Ω**, motivated by the target
Ω ≤ M₁ + |R| ≤ 3.9404 𝔖(N) N/log²N.

Classical proof outline:
  1. Ω ≤ Σ_a f(a) Σ_{ap ≤ N, (N-ap, Q)=1} 1 + N^(2/3) z, by prime factorization.
  2. Bound this by Σ_a f(a) Σ_{ap ≤ N} (Σ_d λ_d)² + N^(11/12),
     using the Selberg upper sieve.
  3. Exchange the sums to obtain the main term M₁ and remainder R.
  4. Bound M₁ ≤ 3.94033 𝔖(N) N/log²N, using Lemmas 3 and 4.
  5. Bound |R| ≪ N/log^A N, using Pan's mean-value theorem.
  6. Combine to get Ω ≤ 3.9404 𝔖(N) N/log²N.

The conclusion below allows `C` to depend on the individual N. It therefore
establishes an interface with a pointwise additive remainder, not the uniform
remainder-free conclusion in this outline. -/
theorem chenOmega_complete_bound (N : ℕ) (ε : ℝ) (_hε : 0 < ε) (_hε' : ε < 1/2)
    (_hN : Even N) (hN_large : 2 ≤ N) :
    ∃ C : ℝ,
      (Finset.range (N + 1)).sum (fun a =>
        (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
            (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
            (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
            a = p₁ * p₂ then (1 : ℝ) else 0) *
          (Finset.range (N + 1)).sum (fun p₃ =>
            if p₃.Prime ∧ a * p₃ ≤ N ∧ (N - a * p₃).Prime then 1 else 0)) ≤
        3.9404 * (1 : ℝ) * (N : ℝ) / (log N) ^ 2 + C * (N : ℝ) / (log N) ^ 10 := by
  have hlog : 0 < log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hscale : 0 < (N : ℝ) / (log N) ^ 10 :=
    div_pos (by exact_mod_cast (by omega : 0 < N)) (pow_pos hlog 10)
  simp only [mul_div_assoc]
  exact exists_additive_error _ _ _ hscale

/-- **Pointwise form without the ε parameter**.

Take ε = 1/4 in `chenOmega_complete_bound`. Since its C may depend on
the fixed N, the additive remainder must be retained. A uniform
remainder-free 3.9404 bound requires optimized Selberg weights and
a uniform version of Pan's mean-value theorem. -/
theorem chenOmega_simple_bound (N : ℕ) (hN : Even N) (hN_large : 1000 ≤ N) :
    ∃ C : ℝ,
      (Finset.range (N + 1)).sum (fun a =>
        (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
            (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
            (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
            a = p₁ * p₂ then (1 : ℝ) else 0) *
          (Finset.range (N + 1)).sum (fun p₃ =>
            if p₃.Prime ∧ a * p₃ ≤ N ∧ (N - a * p₃).Prime then 1 else 0)) ≤
        3.9404 * (1 : ℝ) * (N : ℝ) / (log N) ^ 2 +
          C * (N : ℝ) / (log N) ^ 10 := by
  exact chenOmega_complete_bound N (1 / 4) (by norm_num) (by norm_num) hN
    (by omega)

/-! ## 6. Correspondence with Mathlib's Selberg sieve -/

/-
`Mathlib.NumberTheory.SelbergSieve` provides:
  - `BoundingSieve`: the general sieve setup;
  - `SelbergSieve`: a structure adding a level parameter;
  - `IsUpperMoebius`: the upper Möbius condition;
  - `siftedSum_le_mainSum_errSum_of_upperMoebius`: the basic upper-sieve theorem;
  - `lambdaSquared`: Λ² sieve weights;
  - `upperMoebius_lambdaSquared`: the upper Möbius property of the Λ² sieve;
  - `mainSum_lambdaSquared_eq_sum_mul_sum_sq`: diagonalization of the main term;
  - `selbergTerms`: the Selberg terms g(d) = ν(d) Π_{p|d} (1-ν(p))⁻¹.

This section connects these Mathlib objects to `SelbergWeights`.
-/

open BoundingSieve

/-- Construct Mathlib's `lambdaSquared` weights from `SelbergWeights`.

Mathlib: `lambdaSquared weights d = Σ_{d₁|d} Σ_{d₂|d} if d = lcm(d₁,d₂) then weights(d₁)·weights(d₂) else 0`

Here `SW.lambda` supplies Mathlib's `weights` parameter, and
`lambdaSquared` gives the Selberg coefficients
λ_d = Σ_{[d₁,d₂]=d} λ_{d₁}·λ_{d₂}. -/
def selbergLambdaSquared {N : ℕ} {ε : ℝ} (SW : SelbergWeights N ε) : ℕ → ℝ :=
  BoundingSieve.lambdaSquared SW.lambda

/-- **Bridge theorem 1**: `lambdaSquared` constructed from the Selberg weights
is upper Möbius.

Apply Mathlib's `upperMoebius_lambdaSquared`: if `weights 1 = 1`,
then `lambdaSquared weights` satisfies `IsUpperMoebius`.

The field `SelbergWeights.lambda_one` supplies exactly `lambda 1 = 1`. -/
theorem selberg_lambda_is_upper_moebius {N : ℕ} {ε : ℝ} (SW : SelbergWeights N ε) :
    BoundingSieve.IsUpperMoebius (selbergLambdaSquared SW) := by
  exact BoundingSieve.upperMoebius_lambdaSquared SW.lambda SW.lambda_one

/-- **Bridge theorem 2**: Mathlib's
`siftedSum_le_mainSum_errSum_of_upperMoebius` gives the generic upper sieve bound.

For a `BoundingSieve` encoding the sieve problem, any weights w with w 1 = 1
give upper Möbius coefficients `lambdaSquared w`, and hence
  siftedSum ≤ totalMass · mainSum(lambdaSquared w) + errSum(lambdaSquared w)

The target Chen bound Ω ≤ 3.9404 𝔖(N) N/log²N additionally requires
an optimized estimate of mainSum(lambdaSquared w) on the scale
8 𝔖(N)/log N and errSum(lambdaSquared w) ≪ N/log^A N.
Selberg diagonalization and Pan's mean-value theorem motivate these two inputs;
the pointwise interfaces `selberg_sieve_weights_exist` and `error_term_bound`
do not by themselves supply their uniform versions. -/
theorem omega_upper_bound_via_mathlib
    (S : BoundingSieve) (w : ℕ → ℝ) (hw : w 1 = 1) :
    S.siftedSum ≤ S.totalMass * S.mainSum (BoundingSieve.lambdaSquared w) +
      S.errSum (BoundingSieve.lambdaSquared w) := by
  exact BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius _
    (BoundingSieve.upperMoebius_lambdaSquared w hw)

/-- **Bridge theorem 3**: diagonalization of the main term via Mathlib's
`mainSum_lambdaSquared_eq_sum_mul_sum_sq`.

For any weights w, Mathlib proves
  mainSum(lambdaSquared w) = Σ_{l | P} (selbergTerms l)⁻¹ · (Σ_{l|d|P} ν(d)·w(d))²

This underlies the choice of optimal Selberg weights: minimizing the quadratic
form gives mainSum = (Σ_{l|P} selbergTerms l)⁻¹ in the unrestricted divisor setup.

For Chen's theorem, the corresponding level-restricted optimization and
analytic estimates are the basis of Lemma 3's mainSum bound at scale
8 𝔖(N)/log N; diagonalization alone does not prove that estimate. -/
theorem mainSum_diag_via_mathlib
    (S : BoundingSieve) (w : ℕ → ℝ) :
    S.mainSum (BoundingSieve.lambdaSquared w) =
      ∑ l ∈ S.prodPrimes.divisors, (S.selbergTerms l)⁻¹ *
        (∑ d ∈ S.prodPrimes.divisors,
          if l ∣ d then S.nu d * w d else 0) ^ 2 := by
  exact S.mainSum_lambdaSquared_eq_sum_mul_sum_sq w

/-- **Bridge theorem 4**: the Selberg-sieve Cauchy-Schwarz lower bound.

For the diagonal variables x_l = Σ_{l|d|P} ν(d)·w(d),
Möbius inversion and w(1) = 1 give Σ_l μ(l)x_l = 1.
Cauchy-Schwarz, with a_l = (selbergTerms l)⁻¹, gives
  Σ_l a_l x_l² ≥ (Σ_l μ(l)x_l)² / (Σ_l μ(l)²/a_l).
All l | P are squarefree, so μ(l)² = 1. Therefore
  mainSum ≥ 1 / (Σ_l selbergTerms l).

The signed Möbius identity is essential: no positivity assumption on w
justifies replacing it by a claim that x_1 ≥ 1.

Equality characterizes the optimal Selberg weights on the relevant divisors,
for which mainSum = (Σ_{l|P} selbergTerms l)⁻¹.

The classical Chen calculation seeks the corresponding level-restricted estimate
  Σ_{l|P} selbergTerms l ≈ log N / (8 𝔖(N))
and hence the optimized mainSum scale 8 𝔖(N) / log N (Lemma 3).

Cauchy-Schwarz gives a **lower** bound, not an upper bound:
mainSum ≥ (Σ selbergTerms)⁻¹ for every normalized w, with equality only
for optimal weights. The theorem below proves this finite lower bound. -/
theorem mainSum_cauchy_schwarz_lower_bound
    (S : BoundingSieve) (w : ℕ → ℝ) (hw : w 1 = 1) :
    (S.prodPrimes.divisors.sum (fun l => S.selbergTerms l))⁻¹ ≤
      S.mainSum (BoundingSieve.lambdaSquared w) := by
  exact AnalyticNumberTheory.Sieve.mainSum_cauchy_schwarz_lower_bound S w hw

/-! ## 7. Auxiliary definition: π(x; a, q, l) -/

/-- π(x; a, q, l) = |{p ≤ x : ap prime, ap ≡ l (mod q)}|. -/
def primesInAP_weighted (x a q l : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun p =>
    (a * p).Prime ∧ (a * p) ≡ l [MOD q])).card

/-- Δ(x; a, q, l) = π(x; a, q, l) - li(x/a)/φ(q) -/
noncomputable def weightedDistributionError (x a q l : ℕ) : ℝ :=
  (primesInAP_weighted x a q l : ℝ) -
    logarithmicIntegral_approx_term ((x : ℝ) / a) / Nat.totient q

/-! ## 6.5a. Ingredients for `divisor_sum_bound` -/

/-- Weight f(d) = A^{ω(d)}/φ(d), with f(0) = 0. -/
noncomputable def divisorWeight (A : ℝ) : ArithmeticFunction ℝ where
  toFun d := (A : ℝ) ^ d.primeFactors.card / Nat.totient d
  map_zero' := by simp [Nat.totient_zero]

/-- The real-valued zeta arithmetic function: 1 on positive integers, 0 at zero. -/
noncomputable def zetaR : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else 1
  map_zero' := by simp

private lemma zetaR_apply_ne {n : ℕ} (hn : n ≠ 0) : zetaR n = 1 := by
  simp [zetaR, hn]

private lemma zetaR_multiplicative : zetaR.IsMultiplicative := by
  constructor
  · simp [zetaR]
  · intro m n hmn
    by_cases h : m * n = 0
    · rcases Nat.mul_eq_zero.mp h with hm | hn
      · subst m
        have hn1 : n = 1 := (Nat.coprime_zero_left n).mp hmn
        simp [zetaR, hn1]
      · subst n
        have hm1 : m = 1 := (Nat.coprime_zero_right m).mp hmn
        simp [zetaR, hm1]
    · have hm : m ≠ 0 := left_ne_zero_of_mul h
      have hn : n ≠ 0 := right_ne_zero_of_mul h
      simp [zetaR, hm, hn]

private lemma omega_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hcop : a.Coprime b) :
    (a * b).primeFactors.card = a.primeFactors.card + b.primeFactors.card := by
  rw [Nat.primeFactors_mul ha hb]
  have hdisj : Disjoint a.primeFactors b.primeFactors := by
    rw [Finset.disjoint_left]
    intro p hpa hpb
    have hpa' : p ∣ a := Nat.dvd_of_mem_primeFactors hpa
    have hpb' : p ∣ b := Nat.dvd_of_mem_primeFactors hpb
    have hg : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa' hpb'
    have hg1 : a.gcd b = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
    have h1 : p ∣ 1 := by simpa [hg1] using hg
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hpa
    have hp1 : p = 1 := Nat.dvd_one.mp h1
    exact Nat.not_prime_one (by simpa [hp1] using hp_prime)
  rw [Finset.card_union_of_disjoint hdisj]

private lemma divisorWeight_multiplicative (A : ℝ) : (divisorWeight A).IsMultiplicative := by
  constructor
  · simp [divisorWeight, Nat.totient_one]
  · intro m n hmn
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    · change (A : ℝ) ^ (m * n).primeFactors.card / Nat.totient (m * n) =
        ((A : ℝ) ^ m.primeFactors.card / Nat.totient m) *
          ((A : ℝ) ^ n.primeFactors.card / Nat.totient n)
      rw [omega_mul hm hn hmn, Nat.totient_mul hmn, pow_add]
      have hφm : Nat.totient m ≠ 0 := by
        have : 0 < Nat.totient m := (Nat.totient_pos).2 (Nat.pos_of_ne_zero hm)
        omega
      have hφn : Nat.totient n ≠ 0 := by
        have : 0 < Nat.totient n := (Nat.totient_pos).2 (Nat.pos_of_ne_zero hn)
        omega
      field_simp [hφm, hφn]
      norm_num [Nat.cast_mul]
      ring

private lemma zetaR_mul_apply (f : ArithmeticFunction ℝ) (x : ℕ) :
    (zetaR * f) x = ∑ i ∈ x.divisors, f i := by
  rw [ArithmeticFunction.mul_apply]
  calc
    (∑ a ∈ x.divisorsAntidiagonal, zetaR a.1 * f a.2)
        = (∑ a ∈ x.divisorsAntidiagonal, f a.2) := by
          apply Finset.sum_congr rfl
          intro a ha
          have h : a.1 * a.2 = x ∧ x ≠ 0 := Nat.mem_divisorsAntidiagonal.mp ha
          have ha1 : a.1 ≠ 0 := by
            intro h0
            exact h.2 (by simpa [h0] using h.1.symm)
          simp [zetaR_apply_ne ha1]
    _ = (x.divisors).sum f := by
          refine Finset.sum_bij (fun a _ => a.2) ?_ ?_ ?_ ?_
          · intro a ha
            have h := Nat.mem_divisorsAntidiagonal.mp ha
            exact Nat.mem_divisors.mpr ⟨⟨a.1, by simpa [mul_comm] using h.1.symm⟩, h.2⟩
          · intro a ha b hb hab
            have hda : a.1 * a.2 = x := (Nat.mem_divisorsAntidiagonal.mp ha).1
            have hdb : b.1 * b.2 = x := (Nat.mem_divisorsAntidiagonal.mp hb).1
            have hx : x ≠ 0 := (Nat.mem_divisorsAntidiagonal.mp ha).2
            have ha2 : a.2 ≠ 0 := by
              intro h0
              exact hx (by simpa [h0] using hda.symm)
            have hb2 : b.2 ≠ 0 := by
              intro h0
              exact hx (by simpa [h0] using hdb.symm)
            have hmain : a.1 * a.2 = b.1 * a.2 := by
              rw [← hab] at hdb
              exact hda.trans hdb.symm
            have h1 : a.1 = b.1 := by
              exact mul_left_cancel₀ ha2 (by simpa [mul_comm] using hmain)
            ext <;> assumption
          · intro b hb
            have h := Nat.mem_divisors.mp hb
            refine ⟨(x / b, b), ?_, ?_⟩
            · exact Nat.mem_divisorsAntidiagonal.mpr
                ⟨Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hb), h.2⟩
            · rfl
          · intro a ha
            rfl

private lemma omega_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (p ^ k).primeFactors.card = 1 := by
  rw [Nat.primeFactors_prime_pow (by omega : k ≠ 0) hp]
  simp

/-- Σ_{d|n} f(d) = ∏_{p|n} (1 + Σ_{k≥1} f(p^k)) (f = A^{ω}/φ). -/
private lemma divisor_sum_expansion (A : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (n.divisors).sum (fun d => (A : ℝ) ^ d.primeFactors.card / Nat.totient d) =
      ∏ p ∈ n.primeFactors, (1 + ∑ k ∈ Finset.range (n.factorization p),
        (A : ℝ) / Nat.totient (p ^ (k + 1))) := by
  let F : ArithmeticFunction ℝ := zetaR * divisorWeight A
  have hF : F.IsMultiplicative :=
    ArithmeticFunction.IsMultiplicative.mul zetaR_multiplicative (divisorWeight_multiplicative A)
  have hconv : ∀ m : ℕ, F m = (m.divisors).sum (fun d => divisorWeight A d) :=
    fun m => zetaR_mul_apply (divisorWeight A) m
  have hfac := ArithmeticFunction.IsMultiplicative.multiplicative_factorization F hF hn
  have hpp (p k : ℕ) (hp : p.Prime) : F (p ^ k) =
      1 + ∑ j ∈ Finset.range k, (A : ℝ) / Nat.totient (p ^ (j + 1)) := by
    rw [hconv]
    have hdiv : (p ^ k).divisors = (Finset.range (k + 1)).image (fun j => p ^ j) :=
      by simpa [Finset.map_eq_image] using Nat.divisors_prime_pow hp k
    rw [hdiv]
    rw [Finset.sum_image (by
      intro j hj j' hj' h
      exact Nat.pow_right_injective hp.two_le h)]
    rw [Finset.sum_range_succ']
    have hf0 : divisorWeight A (p ^ 0) = 1 := by simp [divisorWeight, Nat.totient_one]
    rw [hf0]
    rw [add_comm]
    apply congrArg (fun x : ℝ => 1 + x)
    apply Finset.sum_congr rfl
    intro j hj
    have hw : (p ^ (j + 1)).primeFactors.card = 1 :=
      omega_prime_pow hp (by omega : 0 < j + 1)
    change (A : ℝ) ^ (p ^ (j + 1)).primeFactors.card / Nat.totient (p ^ (j + 1)) =
      (A : ℝ) / Nat.totient (p ^ (j + 1))
    rw [hw, pow_one]
  calc
    (n.divisors).sum (fun d => (A : ℝ) ^ d.primeFactors.card / Nat.totient d)
        = F n := (hconv n).symm
    _ = n.factorization.prod (fun p k => F (p ^ k)) := hfac
    _ = ∏ p ∈ n.primeFactors, (1 + ∑ k ∈ Finset.range (n.factorization p),
          (A : ℝ) / Nat.totient (p ^ (k + 1))) := by
          rw [Finsupp.prod, Nat.support_factorization]
          apply Finset.prod_congr rfl
          intro p hp
          exact hpp p (n.factorization p) (Nat.prime_of_mem_primeFactors hp)

/-- Prime-power weight sum:
1 + Σ_{j=1}^{k} A/φ(p^j) ≤ exp(A/(p-1) + A/(p-1)²). -/
private lemma prime_power_weight_sum_bound (A : ℝ) (hA : 0 ≤ A) (p k : ℕ) (hp : p.Prime) :
    1 + (∑ j ∈ Finset.range k, (A : ℝ) / Nat.totient (p ^ (j + 1))) ≤
      Real.exp (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2) := by
  have hφ (j : ℕ) : Nat.totient (p ^ (j + 1)) = p ^ j * (p - 1) :=
    Nat.totient_prime_pow_succ hp j
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : ((p : ℝ) - 1) ≠ 0 := by
    have : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
    linarith
  have hterm (j : ℕ) : (A : ℝ) / Nat.totient (p ^ (j + 1)) =
      (A / ((p : ℝ) - 1)) * (1 / (p : ℝ)) ^ j := by
    rw [hφ j]
    push_cast
    have hpj : ((p : ℝ) ^ j) ≠ 0 := pow_ne_zero j hp0
    have hp1n : (↑(p - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (by have : 2 ≤ p := hp.two_le; omega : (p - 1 : ℕ) ≠ 0)
    rw [one_div, inv_pow]
    field_simp [hp0, hp1n, hpj]
    rw [Nat.cast_sub (by have : 2 ≤ p := hp.two_le; omega : 1 ≤ p)]
    ring
  have hgeo : (∑ j ∈ Finset.range k, (1 / (p : ℝ)) ^ j) ≤ (p : ℝ) / ((p : ℝ) - 1) := by
    have hx : 1 / (p : ℝ) ≠ 1 := by
      have : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
      have hdiv : (1 : ℝ) / p < 1 := (div_lt_one (by positivity : 0 < (p : ℝ))).2 this
      linarith
    have hx0 : 0 ≤ 1 / (p : ℝ) := by positivity
    have hx1 : 1 / (p : ℝ) ≤ 1 := by
      have : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
      exact (div_le_one (by positivity : 0 < (p : ℝ))).2 this.le
    have hxk : (1 / (p : ℝ)) ^ k ≤ 1 := pow_le_one₀ hx0 hx1
    have hden : 0 < 1 - 1 / (p : ℝ) := by
      have : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
      have hdiv : (1 : ℝ) / p < 1 := (div_lt_one (by positivity : 0 < (p : ℝ))).2 this
      linarith
    have hnum : 1 - (1 / (p : ℝ)) ^ k ≤ 1 := by
      have hk0 : 0 ≤ (1 / (p : ℝ)) ^ k := pow_nonneg hx0 k
      linarith
    calc
      (∑ j ∈ Finset.range k, (1 / (p : ℝ)) ^ j)
          = ((1 / (p : ℝ)) ^ k - 1) / ((1 / (p : ℝ)) - 1) := geom_sum_eq hx k
      _ = (1 - (1 / (p : ℝ)) ^ k) / (1 - 1 / (p : ℝ)) := by
            have hneg1 : (1 / (p : ℝ)) ^ k - 1 = -(1 - (1 / (p : ℝ)) ^ k) := by ring
            have hneg2 : (1 / (p : ℝ)) - 1 = -(1 - 1 / (p : ℝ)) := by ring
            rw [hneg1, hneg2]
            exact neg_div_neg_eq (a := 1 - (1 / (p : ℝ)) ^ k) (b := 1 - 1 / (p : ℝ))
      _ ≤ 1 / (1 - 1 / (p : ℝ)) := by
            exact div_le_div_of_nonneg_right hnum (le_of_lt hden)
      _ = (p : ℝ) / ((p : ℝ) - 1) := by
            field_simp
  have hsum : (∑ j ∈ Finset.range k, (A : ℝ) / Nat.totient (p ^ (j + 1))) ≤
      A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2 := by
    calc
      (∑ j ∈ Finset.range k, (A : ℝ) / Nat.totient (p ^ (j + 1)))
          = (∑ j ∈ Finset.range k, (A / ((p : ℝ) - 1)) * (1 / (p : ℝ)) ^ j) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hterm j
      _ = (A / ((p : ℝ) - 1)) * (∑ j ∈ Finset.range k, (1 / (p : ℝ)) ^ j) := by
            rw [← Finset.mul_sum]
      _ ≤ (A / ((p : ℝ) - 1)) * ((p : ℝ) / ((p : ℝ) - 1)) := by
            have hA' : 0 ≤ A / ((p : ℝ) - 1) := by
              have hpos : 0 < (p : ℝ) - 1 := by
                have : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
                linarith
              exact div_nonneg hA (le_of_lt hpos)
            exact mul_le_mul_of_nonneg_left hgeo hA'
      _ = A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2 := by
            field_simp [hp1]
            ring
  have hle : 1 + (∑ j ∈ Finset.range k, (A : ℝ) / Nat.totient (p ^ (j + 1))) ≤
      1 + (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2) := by
    simpa [add_comm] using (add_le_add_left hsum 1)
  exact hle.trans (by simpa [add_comm] using
    (Real.add_one_le_exp (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2)))

/-- The sums Σ_{p|n} 1/(p-1)² are uniformly bounded:
the bound Σ_{p ≤ y} 1/p² ≤ K₀ gives the constant 4K₀. -/
private lemma prime_inv_sq_minus_one_sum_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2) ≤ K := by
  obtain ⟨K, hK0, hK⟩ := prime_inv_sq_bound
  refine ⟨4 * K, mul_nonneg (by norm_num) hK0, ?_⟩
  intro n
  have hle (p : ℕ) (hp : p ∈ n.primeFactors) : 1 / ((p : ℝ) - 1) ^ 2 ≤ 4 / (p : ℝ) ^ 2 := by
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : 2 ≤ p := hp'.two_le
    have hpcast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hpos : 0 < (p : ℝ) := by exact_mod_cast hp'.pos
    have hpm1 : (p : ℝ) - 1 ≥ (p : ℝ) / 2 := by nlinarith
    have hpm1pos : 0 < (p : ℝ) - 1 := by linarith
    -- 1/(p−1)² ≤ 1/(p/2)² = 4/p²
    have hsq : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
    have hle_inv : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / ((p : ℝ) / 2) ^ 2 := by
      gcongr
    calc
      1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / ((p : ℝ) / 2) ^ 2 := hle_inv
      _ = 4 / (p : ℝ) ^ 2 := by field_simp [hpos.ne']; ring
  have hsubset : n.primeFactors ⊆ (Finset.range (n + 1)).filter Nat.Prime := by
    intro p hp
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hple : p ≤ n := by
      by_cases hn0 : n = 0
      · subst n
        simp at hp
      · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpdvd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega : p < n + 1), hp'⟩
  have h1 : (∑ p ∈ n.primeFactors, 4 / (p : ℝ) ^ 2) ≤
      (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, 4 / (p : ℝ) ^ 2) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun p _hp _hnot => by positivity)
  have h2 : (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, 4 / (p : ℝ) ^ 2) ≤ 4 * K := by
    calc
      (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, 4 / (p : ℝ) ^ 2)
          = 4 * (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, 1 / (p : ℝ) ^ 2) := by
            rw [Finset.mul_sum (s := (Finset.range (n + 1)).filter Nat.Prime)
              (f := fun p : ℕ => 1 / (p : ℝ) ^ 2) (a := (4 : ℝ))]
            apply Finset.sum_congr rfl
            intro p hp
            ring
      _ ≤ 4 * K := by
            exact mul_le_mul_of_nonneg_left (hK n) (by norm_num)
  calc
    (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2)
        ≤ (∑ p ∈ n.primeFactors, 4 / (p : ℝ) ^ 2) := by
          exact Finset.sum_le_sum (fun p hp => hle p hp)
    _ ≤ 4 * K := le_trans h1 h2

/-- ω(n) ≤ log n / log 2 (n ≥ 2). -/
private lemma omega_le_log (n : ℕ) (hn : 2 ≤ n) :
    (n.primeFactors.card : ℝ) ≤ log (n : ℝ) / log 2 := by
  have hpow : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
    calc
      2 ^ n.primeFactors.card = ∏ p ∈ n.primeFactors, (2 : ℕ) := by
        rw [Finset.prod_const]
      _ ≤ ∏ p ∈ n.primeFactors, p := by
        exact Finset.prod_le_prod (fun p hp => by norm_num)
          (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have hprod_le : ∏ p ∈ n.primeFactors, p ≤ n := by
    exact Nat.le_of_dvd (by omega : 0 < n) (Nat.prod_primeFactors_dvd n)
  have hpow_le : 2 ^ n.primeFactors.card ≤ n := le_trans hpow hprod_le
  have hcast : ((2 ^ n.primeFactors.card : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpow_le
  have hncast : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog : (n.primeFactors.card : ℝ) * log 2 ≤ log (n : ℝ) := by
    have hlogpow : log (((2 ^ n.primeFactors.card : ℕ) : ℝ)) ≤ log (n : ℝ) :=
      Real.log_le_log (by positivity : 0 < ((2 ^ n.primeFactors.card : ℕ) : ℝ)) hcast
    -- log (2^card : ℝ) = card·log 2
    have hlog2pow : log (((2 ^ n.primeFactors.card : ℕ) : ℝ)) =
        (n.primeFactors.card : ℝ) * log 2 := by
      rw [show ((2 ^ n.primeFactors.card : ℕ) : ℝ) =
          (2 : ℝ) ^ n.primeFactors.card by norm_num]
      rw [Real.log_pow]
    rwa [hlog2pow] at hlogpow
  rw [le_div_iff₀ hlog2]
  exact hlog

/-- Σ_{p|n} 1/(p-1) ≤ log(log(log 3n)) + C for a uniform constant C
and n ≥ 3, by splitting at u. -/
private lemma prime_inv_pminus1_over_primeFactors_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 3 ≤ n →
      (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) ≤
        log (log (log (3 * n : ℝ))) + C := by
  obtain ⟨C₀, hC₀, h₀⟩ := prime_inv_pminus1_bound
  refine ⟨C₀ + (log 2 + 1) + 4 / log 2 + 1, by positivity, ?_⟩
  intro n hn
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog6 : 1 < log 6 := by
    have h := le_log_one_add_of_nonneg (x := 5) (by norm_num)
    norm_num at h
    linarith
  have hlog9 : 2 < log 9 := by
    -- exp 1 < 3 ⟹ exp 2 < 9 ⟹ 2 < log 9
    have hE : Real.exp 1 < 3 := by
      convert exp_lt_two_add_div_two_sub (x := (1 : ℝ)) (by norm_num) (by norm_num) using 1
      norm_num
    have hE2 : Real.exp 2 < 9 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      have hEp : 0 < Real.exp 1 := Real.exp_pos _
      nlinarith [hE, hEp]
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 9)]
    exact hE2
  have hlog3n_gt2 : 2 < log (3 * n : ℝ) := by
    have h9le : (9 : ℝ) ≤ 3 * n := by nlinarith
    have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 9) (by linarith : (9 : ℝ) ≤ 3 * n)
    linarith
  have hloglog3n : log 2 ≤ log (log (3 * n : ℝ)) := by
    have hpos : 0 < log (3 * n : ℝ) := by
      have : 1 ≤ log (3 * n : ℝ) := by
        have h3 : (3 : ℝ) ≤ 3 * n := by nlinarith
        have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by linarith : (3 : ℝ) ≤ 3 * n)
        -- log 3 ≥ 1 follows from le_log_one_add_of_nonneg at x = 2.
        have hlog3 : 1 ≤ log 3 := by
          have hh := le_log_one_add_of_nonneg (x := 2) (by norm_num)
          norm_num at hh
          linarith
        linarith
      linarith
    exact Real.log_le_log (by norm_num : (0 : ℝ) < 2) (le_of_lt hlog3n_gt2)
  -- u = ⌈log(3n)⌉₊
  let u : ℕ := Nat.ceil (log (3 * n : ℝ))
  have hu1 : (u : ℝ) < log (3 * n : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity : 0 ≤ log (3 * n : ℝ))
  have hu2 : log (3 * n : ℝ) ≤ (u : ℝ) := Nat.le_ceil (log (3 * n : ℝ))
  have hu3 : 3 ≤ u := by
    have : (2 : ℝ) < (u : ℝ) := lt_of_lt_of_le hlog3n_gt2 hu2
    have : 2 < u := by exact_mod_cast this
    omega
  -- Small-prime part: p ≤ u.
  have hsmall : (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ (u : ℝ)),
      1 / ((p : ℝ) - 1)) ≤ log (log (u : ℝ)) + C₀ := by
    have hsub : n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ (u : ℝ)) ⊆
        (Finset.range (u + 1)).filter Nat.Prime := by
      intro p hp
      have hpmem := (Finset.mem_filter.mp hp).1
      have hple : (p : ℝ) ≤ (u : ℝ) := (Finset.mem_filter.mp hp).2
      have hp' : p.Prime := Nat.prime_of_mem_primeFactors hpmem
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (by exact_mod_cast hple)), hp'⟩
    have hsum_le : (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ (u : ℝ)),
        1 / ((p : ℝ) - 1)) ≤
        (∑ p ∈ (Finset.range (u + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p _hp _hnot => by
          have hp' : p.Prime := (Finset.mem_filter.mp _hp).2
          have : 0 < (p : ℝ) - 1 := by
            have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp'.one_lt
            linarith
          exact div_nonneg zero_le_one (le_of_lt this))
    exact hsum_le.trans (h₀ u hu3)
  -- Large-prime part: p > u, using the bound on ω(n).
  have hlarge : (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ)),
      1 / ((p : ℝ) - 1)) ≤ 4 / log 2 := by
    have hden (p : ℕ) (hp : p ∈ n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ))) :
        1 / ((p : ℝ) - 1) ≤ 1 / ((u : ℝ) - 1) := by
      have hpu : (u : ℝ) < (p : ℝ) := (Finset.mem_filter.mp hp).2
      have hden_pos : 0 < (p : ℝ) - 1 := by
        have : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
        linarith
      have hden_pos' : 0 < (u : ℝ) - 1 := by
        have : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
        linarith
      exact (one_div_le_one_div hden_pos hden_pos').2 (by nlinarith)
    have hsum_bnd : (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ)),
        1 / ((p : ℝ) - 1)) ≤
        (n.primeFactors.card : ℝ) / ((u : ℝ) - 1) := by
      calc
        (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ)), 1 / ((p : ℝ) - 1))
            ≤ (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ)), 1 / ((u : ℝ) - 1)) := by
              exact Finset.sum_le_sum (fun p hp => hden p hp)
        _ = (n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ))).card / ((u : ℝ) - 1) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
        _ ≤ (n.primeFactors.card : ℝ) / ((u : ℝ) - 1) := by
              have hcard : (n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ))).card ≤ n.primeFactors.card :=
                Finset.card_le_card (Finset.filter_subset _ _)
              have hdenb : 0 < (u : ℝ) - 1 := by
                have : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
                linarith
              exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (le_of_lt hdenb)
    have homega : (n.primeFactors.card : ℝ) ≤ log (n : ℝ) / log 2 := omega_le_log n (by omega)
    have hdenb : (u : ℝ) - 1 ≥ log (3 * n : ℝ) / 2 := by
      have hlog3n2 : 2 ≤ log (3 * n : ℝ) := le_of_lt hlog3n_gt2
      nlinarith [hu2]
    have hb : (n.primeFactors.card : ℝ) / ((u : ℝ) - 1) ≤ 4 / log 2 := by
      -- (log n/log 2)/(log 3n/2) = 2·log n/(log 2·log 3n) ≤ 2/log 2
      have hlog2pos : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      have hlog2pos' : 0 < log 2 := hlog2pos
      have hln : log (n : ℝ) ≤ log (3 * n : ℝ) := by
        exact Real.log_le_log (by positivity : 0 < (n : ℝ)) (by nlinarith : (n : ℝ) ≤ 3 * n)
      have hden : 0 < log (3 * n : ℝ) := by linarith
      calc
        (n.primeFactors.card : ℝ) / ((u : ℝ) - 1)
            ≤ (log (n : ℝ) / log 2) / ((u : ℝ) - 1) := by
              have hdenu : 0 ≤ (u : ℝ) - 1 := by
                have : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
                linarith
              exact div_le_div_of_nonneg_right homega hdenu
        _ ≤ (log (3 * n : ℝ) / log 2) / (log (3 * n : ℝ) / 2) := by
              have h1 : log (n : ℝ) / log 2 ≤ log (3 * n : ℝ) / log 2 := by
                exact div_le_div_of_nonneg_right hln (le_of_lt hlog2pos')
              have hxpos : 0 < (u : ℝ) - 1 := by
                have : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
                linarith
              have hypos : 0 < log (3 * n : ℝ) / 2 := by
                have : 0 < log (3 * n : ℝ) := by linarith
                positivity
              rw [div_le_div_iff₀ hxpos hypos]
              have hbpos : 0 ≤ log (3 * n : ℝ) / log 2 := by positivity
              exact mul_le_mul h1 hdenb (le_of_lt hypos) hbpos
        _ = 2 / log 2 := by field_simp [hden.ne', hlog2pos.ne']
        _ ≤ 4 / log 2 := by
              have : (2 : ℝ) ≤ 4 := by norm_num
              exact div_le_div_of_nonneg_right this (le_of_lt hlog2pos')
    exact hsum_bnd.trans hb
  -- Combine the small-prime and large-prime contributions.
  have hsplit : (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) =
      (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ (u : ℝ)), 1 / ((p : ℝ) - 1)) +
        (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ)), 1 / ((p : ℝ) - 1)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := n.primeFactors)
      (p := fun p : ℕ => (p : ℝ) ≤ (u : ℝ))
      (f := fun p : ℕ => 1 / ((p : ℝ) - 1))]
    congr 1
    apply Finset.sum_congr
    · ext p
      simp [not_le]
    · intro p hp
      rfl
  -- log(log u) ≤ log(log log 3n) + log 2 + 1 (u ≤ log 3n + 1)
  have hsmall2 : log (log (u : ℝ)) ≤ log (log (log (3 * n : ℝ))) + (log 2 + 1) := by
    have hu_le : (u : ℝ) ≤ log (3 * n : ℝ) + 1 := by linarith [hu1]
    have hlogu : log (u : ℝ) ≤ log (log (3 * n : ℝ)) + log 2 := by
      -- log u ≤ log(log 3n + 1) ≤ log(2·log 3n) = log log 3n + log 2
      have hposu : 0 < (u : ℝ) := by
        have : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
        linarith
      have hposll : 0 < log (3 * n : ℝ) := by linarith
      have h2ll : 2 * log (3 * n : ℝ) ≥ log (3 * n : ℝ) + 1 := by
        have : 1 ≤ log (3 * n : ℝ) := by linarith
        nlinarith
      have h1 : log (3 * n : ℝ) + 1 ≤ 2 * log (3 * n : ℝ) := by linarith
      have hle1 : log (u : ℝ) ≤ log (log (3 * n : ℝ) + 1) := by
        -- u ≤ log 3n + 1 and log 3n + 1 > 0.
        have hpos : 0 < log (3 * n : ℝ) + 1 := by linarith
        exact Real.log_le_log (by linarith : 0 < (u : ℝ)) (by linarith : (u : ℝ) ≤ log (3 * n : ℝ) + 1)
      have hle2 : log (log (3 * n : ℝ) + 1) ≤ log (2 * log (3 * n : ℝ)) := by
        have hpos2 : 0 < 2 * log (3 * n : ℝ) := by positivity
        exact Real.log_le_log (by linarith : 0 < log (3 * n : ℝ) + 1) h1
      have hle3 : log (2 * log (3 * n : ℝ)) = log (log (3 * n : ℝ)) + log 2 := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hposll.ne']
        ring
      linarith
    have hloglogu : log (log (u : ℝ)) ≤ log (log (log (3 * n : ℝ)) + log 2) := by
      have hposu2 : 0 < log (u : ℝ) := by
        have : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
        have : 1 < (u : ℝ) := by linarith
        exact Real.log_pos (by linarith : 1 < (u : ℝ))
      have hposll2 : 0 < log (log (3 * n : ℝ)) := by
        have : 1 < log (3 * n : ℝ) := by linarith
        exact Real.log_pos (by linarith : 1 < log (3 * n : ℝ))
      exact Real.log_le_log hposu2 (by linarith : log (u : ℝ) ≤ log (log (3 * n : ℝ)) + log 2)
    have hle : log (log (log (3 * n : ℝ)) + log 2) ≤ log (log (log (3 * n : ℝ))) + log 2 := by
      -- log(x + log 2) ≤ log x + log 2 ⟺ x + log 2 ≤ 2x ⟺ log 2 ≤ x
      have hposx : 0 < log (log (3 * n : ℝ)) := by
        have : 1 < log (3 * n : ℝ) := by linarith
        exact Real.log_pos (by linarith : 1 < log (3 * n : ℝ))
      have hx : log 2 ≤ log (log (3 * n : ℝ)) := hloglog3n
      have hsum : log (log (3 * n : ℝ)) + log 2 ≤ 2 * log (log (3 * n : ℝ)) := by nlinarith
      have h1 : log (log (log (3 * n : ℝ)) + log 2) ≤ log (2 * log (log (3 * n : ℝ))) := by
        have hpos : 0 < log (log (3 * n : ℝ)) + log 2 := by
          have : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
          positivity
        have hpos2 : 0 < 2 * log (log (3 * n : ℝ)) := by positivity
        exact Real.log_le_log hpos hsum
      have h2 : log (2 * log (log (3 * n : ℝ))) = log (log (log (3 * n : ℝ))) + log 2 := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hposx.ne']
        ring
      linarith
    linarith
  calc
    (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1))
        = (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ (u : ℝ)), 1 / ((p : ℝ) - 1)) +
            (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ)), 1 / ((p : ℝ) - 1)) := hsplit
    _ ≤ (log (log (u : ℝ)) + C₀) + 4 / log 2 := add_le_add hsmall hlarge
    _ ≤ (log (log (log (3 * n : ℝ))) + (log 2 + 1) + C₀) + 4 / log 2 := by
          nlinarith [hsmall2]
    _ ≤ log (log (log (3 * n : ℝ))) + (C₀ + (log 2 + 1) + 4 / log 2 + 1) := by
          linarith

/-! ## 6.5. Lemma 2 (divisor-sum bound) -/

/-- **Divisor-sum bound strengthening Lemma 2 (Liu 2022)**.
For A > 0 and n ≥ 1, the source statement is
  Σ_{d|n} μ²(d) A^ω(d)/φ(d) ≪ (log log 3n)^A

The theorem below proves the stronger bound without μ²(d).
In particular, if n is a product of distinct primes ≤ y and y ≥ 3,
the sum is ≪ (log y)^A.

This gives the estimate Σ 3^ω(d)/φ(d) ≪ (log N)³ used for the remainder R₁. -/
theorem divisor_sum_bound (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (n.divisors).sum (fun d =>
        (A : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) ≤
      C * (log (log (3 * n))) ^ A := by
  have hA0 : 0 ≤ A := le_of_lt hA
  obtain ⟨C₁, hC₁0, hC₁⟩ := prime_inv_pminus1_over_primeFactors_le
  obtain ⟨K, hK0, hK⟩ := prime_inv_sq_minus_one_sum_le
  have hll3_pos : 0 < log (log 3) := by
    have hlog3le : 1 ≤ log 3 := by
      have h := le_log_one_add_of_nonneg (x := 2) (by norm_num)
      norm_num at h
      linarith
    have hlog3ne : log 3 ≠ 1 := by
      intro h1
      have hE : Real.exp 1 < 3 := by
        convert exp_lt_two_add_div_two_sub (x := (1 : ℝ)) (by norm_num) (by norm_num) using 1
        norm_num
      have hE3 : Real.exp 1 = 3 := by
        rw [← h1, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      linarith
    exact Real.log_pos (lt_of_le_of_ne hlog3le hlog3ne.symm)
  have hll6_pos : 0 < log (log 6) := by
    have hlog6 : 1 < log 6 := by
      have h := le_log_one_add_of_nonneg (x := 5) (by norm_num)
      norm_num at h
      linarith
    exact Real.log_pos hlog6
  let Csmall : ℝ := max (1 / (log (log 3)) ^ A) ((1 + A) / (log (log 6)) ^ A)
  let C : ℝ := max (Real.exp (A * (C₁ + K))) Csmall
  refine ⟨C, ?_⟩
  intro n hn
  by_cases hn1 : n = 1
  · subst n
    have hsum : ((1 : ℕ).divisors).sum (fun d =>
        (A : ℝ) ^ d.primeFactors.card / Nat.totient d) = 1 := by
      simp [Nat.totient_one]
    have hC : (1 / (log (log 3)) ^ A) ≤ C := by
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hpowpos : 0 < (log (log 3)) ^ A := by positivity
    rw [hsum]
    have h : 1 ≤ C * (log (log 3)) ^ A := by
      have hC' : (1 / (log (log 3)) ^ A) * (log (log 3)) ^ A = 1 := by
        field_simp [hpowpos.ne']
      nlinarith
    simpa [show ((3 * 2 : ℕ) : ℝ) = 6 by norm_num] using h
  by_cases hn2 : n = 2
  · subst n
    have hsum : ((2 : ℕ).divisors).sum (fun d =>
        (A : ℝ) ^ d.primeFactors.card / Nat.totient d) = 1 + A := by
      have hdiv : (2 : ℕ).divisors = ({1, 2} : Finset ℕ) := Nat.prime_two.divisors
      rw [hdiv]
      have hpf : (2 : ℕ).primeFactors = {2} := by
        change (2 ^ 1).primeFactors = {2}
        exact Nat.primeFactors_prime_pow (by norm_num : (1 : ℕ) ≠ 0) (by exact Nat.prime_two)
      simp [Nat.totient_two, Nat.totient_one, hpf]
    have hC : ((1 + A) / (log (log 6)) ^ A) ≤ C := by
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hpowpos : 0 < (log (log 6)) ^ A := by positivity
    rw [hsum]
    have h : 1 + A ≤ C * (log (log 6)) ^ A := by
      have hC' : ((1 + A) / (log (log 6)) ^ A) * (log (log 6)) ^ A = 1 + A := by
        field_simp [hpowpos.ne']
      nlinarith
    change 1 + A ≤ C * (log (log (3 * (2 : ℝ)))) ^ A
    norm_num
    exact h
  · have hn3 : 3 ≤ n := by omega
    have hn0 : n ≠ 0 := by omega
    have hExp := divisor_sum_expansion A n hn0
    have hpp (p : ℕ) (hp : p ∈ n.primeFactors) :
        1 + (∑ k ∈ Finset.range (n.factorization p),
          (A : ℝ) / Nat.totient (p ^ (k + 1))) ≤
          Real.exp (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2) :=
      prime_power_weight_sum_bound A hA0 p (n.factorization p)
        (Nat.prime_of_mem_primeFactors hp)
    have hprod : ∏ p ∈ n.primeFactors,
        (1 + ∑ k ∈ Finset.range (n.factorization p),
          (A : ℝ) / Nat.totient (p ^ (k + 1))) ≤
        Real.exp (A * ((∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) +
          (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2))) := by
      have hle1 : ∏ p ∈ n.primeFactors,
          (1 + ∑ k ∈ Finset.range (n.factorization p),
            (A : ℝ) / Nat.totient (p ^ (k + 1))) ≤
          ∏ p ∈ n.primeFactors,
            Real.exp (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2) := by
        exact Finset.prod_le_prod (fun p hp => by positivity) (fun p hp => hpp p hp)
      have hle2 : ∏ p ∈ n.primeFactors,
          Real.exp (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2) =
          Real.exp (∑ p ∈ n.primeFactors,
            (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2)) := by
        rw [Real.exp_sum]
      have hle3 : (∑ p ∈ n.primeFactors,
          (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2)) =
          A * ((∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) +
            (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2)) := by
        calc
          (∑ p ∈ n.primeFactors, (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2))
              = (∑ p ∈ n.primeFactors, A * (1 / ((p : ℝ) - 1) + 1 / ((p : ℝ) - 1) ^ 2)) := by
                apply Finset.sum_congr rfl
                intro p hp
                ring
          _ = A * (∑ p ∈ n.primeFactors,
                (1 / ((p : ℝ) - 1) + 1 / ((p : ℝ) - 1) ^ 2)) := by
                rw [← Finset.mul_sum (s := n.primeFactors)
                  (f := fun p : ℕ => (1 / ((p : ℝ) - 1) + 1 / ((p : ℝ) - 1) ^ 2)) (a := A)]
          _ = A * ((∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) +
              (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2)) := by
                rw [Finset.sum_add_distrib]
      rw [← hle3, ← hle2]
      exact hle1
    have hbound : (n.divisors).sum (fun d =>
        (A : ℝ) ^ d.primeFactors.card / Nat.totient d) ≤
        Real.exp (A * ((∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) +
          (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2))) := by
      rw [hExp]
      exact hprod
    have hS1 : (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) ≤
        log (log (log (3 * n : ℝ))) + C₁ := hC₁ n hn3
    have hS2 : (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2) ≤ K := hK n
    have hExp2 : Real.exp (A * ((∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) +
        (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2))) ≤
        Real.exp (A * (log (log (log (3 * n : ℝ))) + C₁ + K)) := by
      apply Real.exp_le_exp.2
      nlinarith [hS1, hS2, hA0]
    have hLLpos : 0 < log (log (3 * n : ℝ)) := by
      have hlog3n : 1 < log (3 * n : ℝ) := by
        have h6le : (6 : ℝ) ≤ 3 * n := by exact_mod_cast (by omega : (6 : ℕ) ≤ 3 * n)
        have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 6)
          (by linarith : (6 : ℝ) ≤ 3 * n)
        have hlog6 : 1 < log 6 := by
          have hh := le_log_one_add_of_nonneg (x := 5) (by norm_num)
          norm_num at hh
          linarith
        linarith
      exact Real.log_pos hlog3n
    have hExp3 : Real.exp (A * (log (log (log (3 * n : ℝ))) + C₁ + K)) =
        (log (log (3 * n : ℝ))) ^ A * Real.exp (A * (C₁ + K)) := by
      have hEL : Real.exp (A * log (log (log (3 * n : ℝ)))) =
          (log (log (3 * n : ℝ))) ^ A := by
        rw [mul_comm]
        rw [← (Real.rpow_def_of_pos hLLpos A)]
      have h1 : A * (log (log (log (3 * n : ℝ))) + C₁ + K) =
          A * log (log (log (3 * n : ℝ))) + A * (C₁ + K) := by ring
      rw [h1, Real.exp_add, hEL]
    have hC : Real.exp (A * (C₁ + K)) ≤ C := le_max_left _ _
    calc
      (n.divisors).sum (fun d => (A : ℝ) ^ d.primeFactors.card / Nat.totient d)
          ≤ Real.exp (A * ((∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) +
              (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2))) := hbound
      _ ≤ Real.exp (A * (log (log (log (3 * n : ℝ))) + C₁ + K)) := hExp2
      _ = (log (log (3 * n : ℝ))) ^ A * Real.exp (A * (C₁ + K)) := hExp3
      _ ≤ (log (log (3 * n : ℝ))) ^ A * C := by
            exact mul_le_mul_of_nonneg_left hC (Real.rpow_nonneg (le_of_lt hLLpos) A)
      _ = C * (log (log (3 * n : ℝ))) ^ A := by ring

/-- **Source form of Lemma 2 (Liu 2022)**:
Σ_{d|n} μ²(d)·A^{ω(d)}/φ(d) ≪ (log log 3n)^A.

The notation matches Liu 2022, Lemma 2, arXiv:2203.07871:
  - ω(d) is the number of distinct prime factors of d (`d.primeFactors.card`);
  - φ(d) is Euler's totient function (`Nat.totient d`);
  - μ²(d) is the square of the Möbius function, the squarefree indicator;
  - the upper-bound scale is (log log 3n)^A, for fixed A > 0.

`divisor_sum_bound` proves the stronger version without μ², summing over all
divisors. Since every summand is nonnegative and μ²(d) ∈ {0,1}, that version
implies the source statement. -/
theorem divisor_sum_bound_mu2 (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (n.divisors).sum (fun d =>
        ((ArithmeticFunction.moebius d : ℤ) ^ 2 : ℝ) *
          ((A : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d)) ≤
      C * (log (log (3 * n))) ^ A := by
  obtain ⟨C, hC⟩ := divisor_sum_bound A hA
  refine ⟨C, ?_⟩
  intro n hn
  have hA0 : 0 ≤ A := le_of_lt hA
  have hle (d : ℕ) (hd : d ∈ n.divisors) :
      ((ArithmeticFunction.moebius d : ℤ) ^ 2 : ℝ) *
        ((A : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) ≤
        (A : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d := by
    have hμ : (ArithmeticFunction.moebius d : ℤ) ^ 2 ≤ 1 := by
      rcases ArithmeticFunction.moebius_eq_or d with h0 | h1 | h1'
      · rw [h0]
        norm_num
      · rw [h1]
        norm_num
      · rw [h1']
        norm_num
    have hφ : 0 < Nat.totient d := (Nat.totient_pos).2 (Nat.pos_of_mem_divisors hd)
    have hx : 0 ≤ (A : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d := by
      have hφ' : (0 : ℝ) < (Nat.totient d : ℝ) := by exact_mod_cast hφ
      exact div_nonneg (pow_nonneg hA0 _) (le_of_lt hφ')
    have hμ' : (((ArithmeticFunction.moebius d : ℤ) ^ 2 : ℤ) : ℝ) ≤ (1 : ℝ) := by
      exact_mod_cast hμ
    simpa [mul_comm] using (mul_le_of_le_one_right hx hμ')
  exact (Finset.sum_le_sum (fun d hd => hle d hd)).trans (hC n hn)

/-- Divisor-sum weight f(d) = A^{ω(d)}/φ(d), as an arithmetic function with f(0) = 0. -/
noncomputable def chenDivisorWeight (A : ℝ) : ArithmeticFunction ℝ where
  toFun d := A ^ (d.primeFactors.card : ℕ) / Nat.totient d
  map_zero' := by simp [Nat.totient_zero]

private lemma primeFactors_card_eq_cardDistinctFactors (d : ℕ) :
    d.primeFactors.card = ArithmeticFunction.cardDistinctFactors d := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors]

private lemma chenDivisorWeight_mul (A : ℝ) {m n : ℕ} (_hm : m ≠ 0) (_hn : n ≠ 0)
    (hmn : m.Coprime n) :
    chenDivisorWeight A (m * n) = chenDivisorWeight A m * chenDivisorWeight A n := by
  -- Both public weight definitions have the same arithmetic-function values.
  change divisorWeight A (m * n) = divisorWeight A m * divisorWeight A n
  exact (divisorWeight_multiplicative A).2 hmn


private lemma chenDivisorWeight_isMultiplicative (A : ℝ) :
    (chenDivisorWeight A).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · unfold chenDivisorWeight
    simp
  · intro m n hm hn hmn
    exact chenDivisorWeight_mul A hm hn hmn

/-- A product of distinct primes is squarefree. -/
private lemma squarefree_prod_of_primes {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) : Squarefree (s.prod id) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have haP : a.Prime := hs a (by simp [ha])
      have hcop : a.Coprime (s.prod id) := by
        have ha_dvd : ¬ a ∣ s.prod id := by
          intro h
          have hprod_ne : s.prod id ≠ 0 := by
            exact Finset.prod_ne_zero_iff.mpr
              (fun p hp => (Nat.Prime.ne_zero (hs p (by simp [hp]))))
          have hmem : a ∈ (s.prod id).primeFactors :=
            (Nat.mem_primeFactors).2 ⟨haP, h, hprod_ne⟩
          have hpf : (s.prod id).primeFactors = s :=
            Nat.primeFactors_prod (fun p hp => hs p (by simp [hp]))
          rw [hpf] at hmem
          exact ha hmem
        exact (haP.coprime_iff_not_dvd).2 ha_dvd
      rw [Finset.prod_insert ha]
      change Squarefree (a * s.prod id)
      rw [Nat.squarefree_mul hcop]
      exact ⟨haP.squarefree, ih (fun p hp => hs p (by simp [hp]))⟩

/-- **Special case of Lemma 2**: if n is a product of distinct primes ≤ y
(that is, `Squarefree n` and all prime factors are ≤ y), with y ≥ 3,
then Σ_{d|n} A^ω(d)/φ(d) ≪ (log y)^A.

Proof:
  1. The weight f(d) = A^{ω(d)}/φ(d) is multiplicative, so
     `prodPrimeFactors_one_add_of_squarefree` gives
     Σ_{d|n} f(d) = ∏_{p|n}(1 + f p).
  2. At a prime p, f p = A/(p-1), hence
     ∏_{p|n}(1 + A/(p-1)) ≤ exp(A·Σ_{p|n} 1/(p-1)).
  3. Mertens' theorem (`prime_inv_pminus1_bound`) gives
     Σ_{p|n} 1/(p-1) ≤ Σ_{p≤y} 1/(p-1) ≤ log(log y) + C.
  4. exp(A·(log(log y) + C)) = e^{AC}·(log y)^A.

The hypotheses explicitly include `Squarefree n` and `3 ≤ y`.
Allowing y = 1 would make the right side zero while the left side is at least 1. -/
theorem divisor_sum_bound_squarefree (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ n y : ℕ, 1 ≤ n →
      Squarefree n →
      (∀ p : ℕ, p.Prime → p ∣ n → p ≤ y) →
      3 ≤ y →
      (n.divisors).sum (fun d =>
        (A : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) ≤
      C * (log y) ^ A := by
  obtain ⟨C0, hC00, hC0⟩ := MertensTheorem.prime_inv_pminus1_bound
  refine ⟨exp (A * C0), ?_⟩
  intro n y hn hsq hle hy
  have hlogy : 0 < log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  -- Σ_{d|n} f(d) = ∏_{p|n}(1 + f p)
  have hprod := (chenDivisorWeight_isMultiplicative A).prodPrimeFactors_one_add_of_squarefree hsq
  have hfp : ∀ p ∈ n.primeFactors, chenDivisorWeight A p = A / ((p : ℝ) - 1) := by
    intro p hp
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    unfold chenDivisorWeight
    change A ^ p.primeFactors.card / ↑p.totient = A / (↑p - 1)
    have hω : p.primeFactors.card = 1 := by
      have hpf : p.primeFactors = {p} := by
        ext q
        constructor
        · intro hq
          have hqP : q.Prime := Nat.prime_of_mem_primeFactors hq
          have hqd : q ∣ p := Nat.dvd_of_mem_primeFactors hq
          rcases hp'.eq_one_or_self_of_dvd q hqd with hq1 | hqp
          · exact absurd hq1 hqP.ne_one
          · simp [hqp]
        · intro hq
          simp at hq
          subst hq
          simp [hp']
      rw [hpf]
      simp
    have hφ : Nat.totient p = p - 1 := Nat.totient_prime hp'
    rw [hω, hφ]
    have hcast : (↑(p - 1) : ℝ) = (p : ℝ) - 1 := by
      simpa using (Nat.cast_sub (by exact hp'.one_lt.le : 1 ≤ p))
    rw [hcast]
    simp
  have hsum_eq : (n.divisors).sum (fun d =>
        A ^ (d.primeFactors.card : ℕ) / Nat.totient d) =
      n.primeFactors.prod (fun p => 1 + chenDivisorWeight A p) := by
    change (n.divisors).sum (fun d => chenDivisorWeight A d) =
      n.primeFactors.prod (fun p => 1 + chenDivisorWeight A p)
    rw [← hprod]
  -- ∏(1 + f p) ≤ exp(A·Σ 1/(p-1))
  have hprod_le : n.primeFactors.prod (fun p => 1 + chenDivisorWeight A p) ≤
      exp (A * ((n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)))) := by
    calc
      n.primeFactors.prod (fun p => 1 + chenDivisorWeight A p)
          ≤ n.primeFactors.prod (fun p => exp (A * (1 / ((p : ℝ) - 1)))) := by
            apply Finset.prod_le_prod
            · intro p hp
              have hnonneg : 0 ≤ chenDivisorWeight A p := by
                unfold chenDivisorWeight
                exact div_nonneg (pow_nonneg (le_of_lt hA) _) (Nat.cast_nonneg _)
              linarith
            · intro p hp
              have hfp' : chenDivisorWeight A p = A / ((p : ℝ) - 1) := hfp p hp
              rw [hfp']
              have harg : A * (1 / ((p : ℝ) - 1)) = A / ((p : ℝ) - 1) := by
                rw [mul_one_div]
              rw [harg, add_comm]
              exact Real.add_one_le_exp (A / ((p : ℝ) - 1))
      _ = exp (A * ((n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)))) := by
            have hlin : A * (n.primeFactors.sum (fun p => 1 / ((p : ℝ) - 1))) =
                n.primeFactors.sum (fun p => A * (1 / ((p : ℝ) - 1))) := by
              rw [Finset.mul_sum]
            rw [hlin, Real.exp_sum]
  -- Σ_{p|n} 1/(p-1) ≤ log(log y) + C0
  have hsum_le : (n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)) ≤
      log (log y) + C0 := by
    have hsub : n.primeFactors ⊆ ((range (y + 1)).filter Nat.Prime) := by
      intro p hp
      have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      exact Finset.mem_filter.mpr ⟨by simp [mem_range, hle p hp' hpd], hp'⟩
    have hle1 : (n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)) ≤
        ((range (y + 1)).filter Nat.Prime).sum (fun p => 1 / ((p : ℝ) - 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _hnot => by
        have hp' : p.Prime := (mem_filter.mp hp).2
        have hpos : 0 < (p : ℝ) - 1 := by
          have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
          linarith
        exact div_nonneg zero_le_one (le_of_lt hpos))
    exact le_trans hle1 (hC0 y hy)
  -- exp(A·Σ) ≤ exp(A·(log log y + C0)) = exp(AC0)·(log y)^A
  have hfinal : exp (A * ((n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)))) ≤
      exp (A * C0) * (log y) ^ A := by
    have h1 : exp (A * (log (log y) + C0)) = exp (A * C0) * (log y) ^ A := by
      have hsplit : A * (log (log y) + C0) = A * log (log y) + A * C0 := by ring
      rw [hsplit, Real.exp_add]
      have hterm : exp (A * log (log y)) = (log y) ^ A := by
        calc exp (A * log (log y)) = exp (log (log y) * A) := by rw [mul_comm]
          _ = (exp (log (log y))) ^ A := by rw [Real.exp_mul]
          _ = (log y) ^ A := by
            rw [Real.exp_log (by linarith : 0 < log y)]
      rw [hterm]
      ring
    have hle : exp (A * ((n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)))) ≤
        exp (A * (log (log y) + C0)) := by
      have hmul : A * (n.primeFactors.sum (fun p => 1 / ((p : ℝ) - 1))) ≤
          A * (log (log y) + C0) :=
        mul_le_mul_of_nonneg_left hsum_le (le_of_lt hA)
      exact Real.exp_le_exp.mpr hmul
    rwa [h1] at hle
  -- Combine the estimates.
  have hmain : (n.divisors).sum (fun d =>
        A ^ (d.primeFactors.card : ℕ) / Nat.totient d) ≤
      exp (A * C0) * (log y) ^ A := by
    rw [hsum_eq]
    exact hprod_le.trans hfinal
  exact hmain

/-- **Application**: Σ_{d|Q} 3^ω(d)/φ(d) ≪ (log N)³.

In Chen's sieve, Q is a product of primes ≤ z = N^(1/4-ε/2).
Apply Lemma 2 with A = 3 and y = N to obtain the bound.

The hypotheses include `0 < ε` and `3 ≤ N`.
At N = 1, the right side would be zero while the left side is at least 1. -/
theorem divisor_sum_3_omega_bound (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hN : 3 ≤ N) :
    ∃ C : ℝ,
      ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) ≤
      C * (log N) ^ (3 : ℝ) := by
  -- Q is a product of distinct primes, hence squarefree, with prime factors ≤ z ≤ N.
  have hsq : Squarefree (selbergQ N ε) := by
    unfold selbergQ
    exact squarefree_prod_of_primes (fun p hp => (mem_filter.mp hp).2.1)
  have hQ1 : 1 ≤ selbergQ N ε := by
    unfold selbergQ
    have hQpos : 0 < ((Finset.range (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1)).filter
        (fun p => p.Prime ∧ ¬ p ∣ N)).prod id := by
      exact Finset.prod_pos (fun p hp => (Nat.Prime.pos (mem_filter.mp hp).2.1))
    omega
  have hle : ∀ p : ℕ, p.Prime → p ∣ selbergQ N ε → p ≤ N := by
    intro p hp hpd
    have hQne : selbergQ N ε ≠ 0 := by
      unfold selbergQ
      exact Finset.prod_ne_zero_iff.mpr (fun q hq => (Nat.Prime.ne_zero (mem_filter.mp hq).2.1))
    have hmem : p ∈ (selbergQ N ε).primeFactors :=
      (Nat.mem_primeFactors).2 ⟨hp, hpd, hQne⟩
    unfold selbergQ at hmem
    have hpf : (((Finset.range (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1)).filter
        (fun q => q.Prime ∧ ¬ q ∣ N)).prod id).primeFactors =
        (Finset.range (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1)).filter
          (fun q => q.Prime ∧ ¬ q ∣ N) := by
      exact Nat.primeFactors_prod (fun q hq => (mem_filter.mp hq).2.1)
    rw [hpf] at hmem
    -- p < z' + 1 → p ≤ z' ≤ N^(1/4-ε/2) ≤ N
    have hpz : p < Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1 :=
      mem_range.mp (mem_filter.mp hmem).1
    have hpz' : p ≤ Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) := by omega
    have hzle : (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤ (N : ℝ) ^ (1/4 - ε/2) :=
      Nat.floor_le (by positivity : 0 ≤ (N : ℝ) ^ (1/4 - ε/2))
    have hNge1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hpow : (N : ℝ) ^ (1/4 - ε/2) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
      have hε0 : 0 ≤ ε := le_of_lt hε
      have hexp : 1 / 4 - ε / 2 ≤ (1 / 4 : ℝ) := by
        have h2 : 0 ≤ ε / 2 := div_nonneg hε0 (by norm_num)
        linarith
      exact Real.rpow_le_rpow_of_exponent_le hNge1 hexp
    have hpow2 : (N : ℝ) ^ (1 / 4 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le hNge1 (by norm_num)
    have hpow3 : (N : ℝ) ^ (1 : ℝ) = (N : ℝ) := Real.rpow_one _
    have hzN : (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤ (N : ℝ) := by
      calc (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤ (N : ℝ) ^ (1/4 - ε/2) := hzle
        _ ≤ (N : ℝ) ^ (1/4) := hpow
        _ ≤ (N : ℝ) ^ (1 : ℝ) := hpow2
        _ = (N : ℝ) := hpow3
    have hp_le : (p : ℝ) ≤ (N : ℝ) := le_trans (by exact_mod_cast hpz') hzN
    exact_mod_cast hp_le
  obtain ⟨C', hC'⟩ := divisor_sum_bound_squarefree (3 : ℝ) (by norm_num)
  have hmain : ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) ≤
      C' * (log N) ^ (3 : ℝ) :=
    hC' (selbergQ N ε) N hQ1 hsq hle hN
  exact ⟨C', hmain⟩

/-! ## 6.6. Liu's correction: the case (a,d)>1 (Section IV) -/

/-- **(a,d)>1 implies π(N;a,d,N) ≤ 1** for the local counting definition.

When (a,d) > 1 and a ≥ 1, we have a ≥ 2, so a*p can be prime only if p = 1.
Indeed, a | a*p, and primality gives a = 1 or a = a*p. The first case
contradicts a ≥ 2, and the second gives p = 1.
Thus at most one p satisfies the conditions, and the count is at most 1. -/
theorem coprime_condition_implies_bounded_ap
    (N a d : ℕ) (_hN : 2 ≤ N) (ha : 1 ≤ a) (_hd : 1 ≤ d)
    (h_not_coprime : 1 < Nat.gcd a d) :
    primesInAP_weighted N a d (N % d) ≤ 1 := by
  -- Step 1: gcd(a,d) > 1 and a ≥ 1 imply a ≥ 2, since gcd(1,d) = 1.
  have ha_ge_2 : 2 ≤ a := by
    by_contra h
    push Not at h
    have : a = 0 ∨ a = 1 := by omega
    cases this with
    | inl h0 => omega
    | inr h1 =>
      rw [h1] at h_not_coprime
      simp [] at h_not_coprime
  -- Step 2: for a ≥ 2, a*p can be prime only if p = 1.
  unfold primesInAP_weighted
  apply Finset.card_le_one.mpr
  intro p hp q hq
  simp only [Finset.mem_filter] at hp hq
  obtain ⟨_, hp_prime, _⟩ := hp
  obtain ⟨_, hq_prime, _⟩ := hq
  -- Auxiliary implication: a ≥ 2 and (a*r).Prime imply r = 1.
  have h_impl : ∀ r : ℕ, (a * r).Prime → r = 1 := by
    intro r hr
    by_contra hr_ne_1
    by_cases hr0 : r = 0
    · -- r = 0: a * 0 = 0 is not prime.
      rw [hr0, mul_zero] at hr
      exact absurd hr (by decide)
    · -- r ≥ 2: a is a proper divisor of a*r (2 ≤ a < a*r), so a*r is not prime.
      have h_dvd : a ∣ a * r := dvd_mul_right a r
      have h_r_ge_2 : 2 ≤ r := by omega
      have h_lt : a < a * r := by nlinarith [h_r_ge_2, ha_ge_2]
      exact absurd hr (Nat.not_prime_of_dvd_of_lt h_dvd ha_ge_2 h_lt)
  -- p = 1 and q = 1, hence p = q.
  rw [h_impl p hp_prime, h_impl q hq_prime]

/-- **Lemma for R₁**: for d | Q,
Σ_{N^(1/10) < p₁ ≤ N^(1/3), p₁|d} 1/p₁ is bounded uniformly in d.

The sum is at most Σ_{N^(1/10) < p ≤ N^(1/3)} 1/p. Lemma 1,
`prime_reciprocal_sum_bounded` with α = 1/10 and β = 1/3,
bounds this by C₀ independently of d. -/
lemma prime_divisor_recip_sum_bounded_real (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hN8 : 8 ≤ N) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ d : ℕ,
      d ∣ selbergQ N ε →
        ((d.primeFactors.filter (fun p₁ : ℕ => (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧
            (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ))).sum (fun p₁ => 1 / (p₁ : ℝ))) ≤ C₀ := by
  obtain ⟨C₀, hC₀⟩ := prime_reciprocal_sum_bounded (1/10 : ℝ) (1/3 : ℝ) (by norm_num) (by norm_num)
  have hC₀nonneg : 0 ≤ C₀ := by
    have hb := hC₀ 8 (by norm_num)
    have hnonneg : (0 : ℝ) ≤
        ((Finset.range (8 + 1)).filter (fun p : ℕ =>
          Nat.Prime p ∧ ((8 : ℝ) ^ (1/10 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (8 : ℝ) ^ (1/3 : ℝ)))).sum
          (fun p => 1 / (p : ℝ)) := by
      exact Finset.sum_nonneg (fun p hp => by positivity)
    have hleabs : ((Finset.range (8 + 1)).filter (fun p : ℕ =>
          Nat.Prime p ∧ ((8 : ℝ) ^ (1/10 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (8 : ℝ) ^ (1/3 : ℝ)))).sum
          (fun p => 1 / (p : ℝ)) ≤
        |((Finset.range (8 + 1)).filter (fun p : ℕ =>
          Nat.Prime p ∧ ((8 : ℝ) ^ (1/10 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (8 : ℝ) ^ (1/3 : ℝ)))).sum
          (fun p => 1 / (p : ℝ))| := le_abs_self _
    exact le_trans hnonneg (le_trans hleabs hb)
  -- For every x ≥ 2, |Σ| ≤ C₀; since Σ ≥ 0, this gives Σ ≤ C₀.
  refine ⟨C₀, hC₀nonneg, ?_⟩
  intro d hd
  have hx2 : 2 ≤ N := by omega
  have hbN := hC₀ N hx2
  have hle : ((d.primeFactors.filter (fun p₁ : ℕ => (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧
        (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ))).sum (fun p₁ => 1 / (p₁ : ℝ))) ≤
      ((Finset.range (N + 1)).filter (fun p : ℕ =>
        Nat.Prime p ∧ ((N : ℝ) ^ (1/10 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ)))).sum
        (fun p => 1 / (p : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p₁ hp₁
      simp only [Finset.mem_filter, Finset.mem_range] at hp₁ ⊢
      -- hp₁ : p₁ ∈ d.primeFactors ∧ cond
      have hp₁f : p₁ ∈ d.primeFactors := hp₁.1
      have hp₁r : (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) := hp₁.2
      have hp₁prime : p₁.Prime := (Nat.mem_primeFactors.mp hp₁f).1
      have hp₁dvd : p₁ ∣ d := (Nat.mem_primeFactors.mp hp₁f).2.1
      have hdvdQ : d ∣ selbergQ N ε := hd
      have hQne : selbergQ N ε ≠ 0 := by
        unfold selbergQ
        exact Finset.prod_ne_zero_iff.mpr
          (fun q hq => (Nat.Prime.ne_zero (mem_filter.mp hq).2.1))
      -- p₁ | d | Q and all prime factors of Q are ≤ N, so p₁ ∈ range (N+1).
      have hp₁leN : p₁ ≤ N := by
        have hp₁dvdQ : p₁ ∣ selbergQ N ε := dvd_trans hp₁dvd hdvdQ
        have hmem : p₁ ∈ (selbergQ N ε).primeFactors :=
          (Nat.mem_primeFactors).2 ⟨hp₁prime, hp₁dvdQ, hQne⟩
        unfold selbergQ at hmem
        have hpfQ : (((Finset.range (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1)).filter
            (fun q => q.Prime ∧ ¬ q ∣ N)).prod id).primeFactors =
            (Finset.range (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1)).filter
              (fun q => q.Prime ∧ ¬ q ∣ N) := by
          exact Nat.primeFactors_prod (fun q hq => (mem_filter.mp hq).2.1)
        rw [hpfQ] at hmem
        have hpz : p₁ < Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1 :=
          mem_range.mp (mem_filter.mp hmem).1
        have hpz' : p₁ ≤ Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) := by omega
        have hzle : (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤
            (N : ℝ) ^ (1/4 - ε/2) :=
          Nat.floor_le (by positivity : 0 ≤ (N : ℝ) ^ (1/4 - ε/2))
        have hNge1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
        have hexp : 1/4 - ε/2 ≤ (1/4 : ℝ) := by linarith
        have hpow : (N : ℝ) ^ (1/4 - ε/2) ≤ (N : ℝ) ^ (1/4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hNge1 hexp
        have hpow2 : (N : ℝ) ^ (1/4 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hNge1 (by norm_num)
        have hpow3 : (N : ℝ) ^ (1 : ℝ) = (N : ℝ) := Real.rpow_one _
        have hzN : (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤ (N : ℝ) := by
          calc (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤
              (N : ℝ) ^ (1/4 - ε/2) := hzle
            _ ≤ (N : ℝ) ^ (1/4 : ℝ) := hpow
            _ ≤ (N : ℝ) ^ (1 : ℝ) := hpow2
            _ = (N : ℝ) := hpow3
        have hp_le : (p₁ : ℝ) ≤ (N : ℝ) := le_trans (by exact_mod_cast hpz') hzN
        exact_mod_cast hp_le
      exact ⟨Nat.lt_succ_of_le hp₁leN, hp₁prime, hp₁r⟩
    · intro p₁ hp₁ h₁
      positivity
  exact le_trans hle (abs_le.mp hbN).2

/-- **Lemma for R₁**: for p₁ with N^(1/10) < p₁ ≤ N^(1/3),
the sum Σ_{N^(1/3) < p₂ ≤ (N/p₁)^(1/2)} 1/p₂ is uniformly bounded.

Since p₁ > N^(1/10), we have (N/p₁)^(1/2) < N^(9/20).
The inner sum is therefore at most Σ_{N^(1/3) < p₂ < N^(9/20)} 1/p₂,
which Lemma 1 bounds by C₁ using α = 1/3 and β = 9/20. -/
private lemma prime_recip_sum_inner_bounded (N : ℕ) (hN8 : 8 ≤ N) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ p₁ : ℕ, (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) →
      (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) →
      2 ≤ p₁ →
        (∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
          Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
            (p₂ : ℝ) ≤ (N : ℝ) ^ (1/2 : ℝ) / (↑p₁ : ℝ) ^ (1/2 : ℝ)),
          1 / (p₂ : ℝ)) ≤ C₁ := by
  obtain ⟨C₁, hC₁⟩ := prime_reciprocal_sum_bounded (1/3 : ℝ) (9/20 : ℝ) (by norm_num) (by norm_num)
  have hC₁nonneg : 0 ≤ C₁ := by
    have hb := hC₁ 8 (by norm_num)
    have hnonneg : (0 : ℝ) ≤
        ((Finset.range (8 + 1)).filter (fun p : ℕ =>
          Nat.Prime p ∧ ((8 : ℝ) ^ (1/3 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (8 : ℝ) ^ (9/20 : ℝ)))).sum
          (fun p => 1 / (p : ℝ)) := by
      exact Finset.sum_nonneg (fun p hp => by positivity)
    have hleabs : ((Finset.range (8 + 1)).filter (fun p : ℕ =>
          Nat.Prime p ∧ ((8 : ℝ) ^ (1/3 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (8 : ℝ) ^ (9/20 : ℝ)))).sum
          (fun p => 1 / (p : ℝ)) ≤
        |((Finset.range (8 + 1)).filter (fun p : ℕ =>
          Nat.Prime p ∧ ((8 : ℝ) ^ (1/3 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (8 : ℝ) ^ (9/20 : ℝ)))).sum
          (fun p => 1 / (p : ℝ))| := le_abs_self _
    exact le_trans hnonneg (le_trans hleabs hb)
  refine ⟨C₁, hC₁nonneg, ?_⟩
  intro p₁ hp₁low hp₁high hp₁2
  have hx2 : 2 ≤ N := by omega
  have hbN := hC₁ N hx2
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNge1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hp1pos : 0 < (p₁ : ℝ) := by
    have h2 : (2 : ℝ) ≤ (p₁ : ℝ) := by exact_mod_cast hp₁2
    linarith
  -- (N/p₁)^(1/2) ≤ N^(9/20)
  have hsqrt : (N : ℝ) ^ (1/2 : ℝ) / (p₁ : ℝ) ^ (1/2 : ℝ) ≤ (N : ℝ) ^ (9/20 : ℝ) := by
    have hpow1 : (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) := hp₁low
    have hbase : 0 ≤ (N : ℝ) ^ (1/10 : ℝ) :=
      Real.rpow_nonneg (by exact_mod_cast (by omega : 0 ≤ N)) (1/10 : ℝ)
    have hbase2 : 0 < (N : ℝ) ^ (1/10 : ℝ) := Real.rpow_pos_of_pos hNpos (1/10 : ℝ)
    have hpowp : (N : ℝ) ^ ((1/10 : ℝ) * (1/2 : ℝ)) < (p₁ : ℝ) ^ (1/2 : ℝ) := by
      -- Use (N^(1/10))^(1/2) < p₁^(1/2) and simplify (1/10)·(1/2) = 1/20.
      have h1 : ((N : ℝ) ^ (1/10 : ℝ)) ^ (1/2 : ℝ) < (p₁ : ℝ) ^ (1/2 : ℝ) := by
        exact Real.rpow_lt_rpow hbase hpow1 (by norm_num : 0 < (1/2 : ℝ))
      have h2 : (N : ℝ) ^ ((1/10 : ℝ) * (1/2 : ℝ)) = ((N : ℝ) ^ (1/10 : ℝ)) ^ (1/2 : ℝ) := by
        exact Real.rpow_mul (by positivity : 0 ≤ (N : ℝ)) (1/10 : ℝ) (1/2 : ℝ)
      rw [h2]
      exact h1
    have hpowp' : (N : ℝ) ^ (1/20 : ℝ) < (p₁ : ℝ) ^ (1/2 : ℝ) := by
      have hexp : (1/10 : ℝ) * (1/2 : ℝ) = 1/20 := by norm_num
      have h1 : ((N : ℝ) ^ (1/10 : ℝ)) ^ (1/2 : ℝ) < (p₁ : ℝ) ^ (1/2 : ℝ) := by
        exact Real.rpow_lt_rpow hbase hpow1 (by norm_num : 0 < (1/2 : ℝ))
      have h2 : (N : ℝ) ^ ((1/10 : ℝ) * (1/2 : ℝ)) = ((N : ℝ) ^ (1/10 : ℝ)) ^ (1/2 : ℝ) := by
        exact Real.rpow_mul (by positivity : 0 ≤ (N : ℝ)) (1/10 : ℝ) (1/2 : ℝ)
      rw [hexp] at h2
      -- h2 : N^(1/20) = (N^(1/10))^(1/2); apply h1.
      rwa [← h2] at h1
    have hdiv : (N : ℝ) ^ (1/2 : ℝ) / (p₁ : ℝ) ^ (1/2 : ℝ) <
        (N : ℝ) ^ (1/2 : ℝ) / (N : ℝ) ^ (1/20 : ℝ) := by
      exact div_lt_div_of_pos_left
        (Real.rpow_pos_of_pos hNpos (1/2 : ℝ))
        (Real.rpow_pos_of_pos hNpos (1/20 : ℝ)) hpowp'
    have hsub : (N : ℝ) ^ (1/2 : ℝ) / (N : ℝ) ^ (1/20 : ℝ) = (N : ℝ) ^ (9/20 : ℝ) := by
      rw [← Real.rpow_sub hNpos]
      congr 1
      norm_num
    exact le_of_lt (by rwa [hsub] at hdiv)
  have hle : (∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
        Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
          (p₂ : ℝ) ≤ (N : ℝ) ^ (1/2 : ℝ) / (p₁ : ℝ) ^ (1/2 : ℝ)),
        1 / (p₂ : ℝ)) ≤
      (∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
        Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
          (p₂ : ℝ) ≤ (N : ℝ) ^ (9/20 : ℝ)),
        1 / (p₂ : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p₂ hp₂
      simp only [Finset.mem_filter] at hp₂ ⊢
      -- Required: p₂ < N+1 ∧ p₂.Prime ∧ N^(1/3) < p₂ ∧ p₂ ≤ N^(9/20).
      exact ⟨hp₂.1, hp₂.2.1, hp₂.2.2.1, le_trans hp₂.2.2.2 hsqrt⟩
    · intro p₂ hp₂ h₁
      positivity
  exact le_trans hle (abs_le.mp hbN).2

/-- **Auxiliary bound**: all prime factors of d | Q are ≤ N^(1/3),
since those of Q are ≤ z = N^(1/4-ε/2) ≤ N^(1/3). -/
private lemma prime_factor_lt_cuberoot (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hN : 2 ≤ N) {d p : ℕ} (hp_prime : p.Prime)
    (hd : d ∣ selbergQ N ε) (hp : p ∣ d) :
    (p : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) := by
  have hQne : selbergQ N ε ≠ 0 := by
    unfold selbergQ
    exact Finset.prod_ne_zero_iff.mpr (fun q hq => (Nat.Prime.ne_zero (mem_filter.mp hq).2.1))
  have hp_dvdQ : p ∣ selbergQ N ε := dvd_trans hp hd
  have hmem : p ∈ (selbergQ N ε).primeFactors :=
    (Nat.mem_primeFactors).2 ⟨hp_prime, hp_dvdQ, hQne⟩
  unfold selbergQ at hmem
  have hpf : (((Finset.range (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1)).filter
      (fun q => q.Prime ∧ ¬ q ∣ N)).prod id).primeFactors =
      (Finset.range (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1)).filter
        (fun q => q.Prime ∧ ¬ q ∣ N) := by
    exact Nat.primeFactors_prod (fun q hq => (mem_filter.mp hq).2.1)
  rw [hpf] at hmem
  have hpz : p < Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1 :=
    mem_range.mp (mem_filter.mp hmem).1
  have hpz' : p ≤ Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) := by omega
  have hzle : (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤ (N : ℝ) ^ (1/4 - ε/2) :=
    Nat.floor_le (by positivity : 0 ≤ (N : ℝ) ^ (1/4 - ε/2))
  have hNge1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hexp : 1/4 - ε/2 ≤ (1/4 : ℝ) := by
    have hε0 : 0 ≤ ε := le_of_lt hε
    have h2 : 0 ≤ ε / 2 := div_nonneg hε0 (by norm_num)
    linarith
  have hpow : (N : ℝ) ^ (1/4 - ε/2) ≤ (N : ℝ) ^ (1/4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNge1 hexp
  have hpow2 : (N : ℝ) ^ (1/4 : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNge1 (by norm_num)
  have hzN : (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) := by
    calc (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤ (N : ℝ) ^ (1/4 - ε/2) := hzle
      _ ≤ (N : ℝ) ^ (1/4 : ℝ) := hpow
      _ ≤ (N : ℝ) ^ (1/3 : ℝ) := hpow2
  have hpzR : (p : ℝ) ≤ (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) := by
    exact_mod_cast hpz'
  exact le_trans hpzR hzN

/-- **Auxiliary implication**: (a,d)>1 with a = p₁p₂ and large p₂ implies p₁ | d.

Since p₂ > N^(1/3) while prime factors of d | Q are ≤ N^(1/3), p₂ ∤ d.
Any prime factor of gcd(p₁p₂,d) must therefore be p₁, so p₁ | d. -/
private lemma prime_pair_gcd_imp_dvd (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hN : 2 ≤ N) {a d p₁ p₂ : ℕ}
    (hd : d ∣ selbergQ N ε)
    (hp₁prime : p₁.Prime) (hp₂prime : p₂.Prime)
    (hp₂low : (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ))
    (ha : a = p₁ * p₂)
    (hgcd : 1 < Nat.gcd a d) :
    p₁ ∣ d := by
  by_contra h
  have h1 : 1 < Nat.gcd (p₁ * p₂) d := by simpa [ha] using hgcd
  rcases Nat.exists_prime_and_dvd (by omega : Nat.gcd (p₁ * p₂) d ≠ 1) with ⟨q, hqprime, hqdvd⟩
  have hqdvd2 : q ∣ p₁ * p₂ := dvd_trans hqdvd (Nat.gcd_dvd_left (p₁ * p₂) d)
  have hq : q ∣ p₁ ∨ q ∣ p₂ := (hqprime.dvd_mul).mp hqdvd2
  rcases hq with hq1 | hq2
  · exfalso
    have hqdvd' : q ∣ d := dvd_trans hqdvd (Nat.gcd_dvd_right (p₁ * p₂) d)
    have hqeq : q = p₁ :=
      (prime_dvd_prime_iff_eq (Nat.prime_iff.mp hqprime) (Nat.prime_iff.mp hp₁prime)).mp hq1
    exact h (by simpa [hqeq] using hqdvd')
  · have hqeq : q = p₂ :=
      (prime_dvd_prime_iff_eq (Nat.prime_iff.mp hqprime) (Nat.prime_iff.mp hp₂prime)).mp hq2
    have hp₂dvd : p₂ ∣ d := by
      rw [← hqeq]
      exact dvd_trans hqdvd (Nat.gcd_dvd_right (p₁ * p₂) d)
    have hp₂lt := prime_factor_lt_cuberoot N ε hε hN hp₂prime hd hp₂dvd
    exact (not_lt_of_ge hp₂lt) hp₂low

/-- **Auxiliary bound for R₁**: p₂ ≤ (N/p₁)^(1/2) implies p₂² ≤ N/p₁,
by monotonicity of squaring and the real-power identities. -/
private lemma r1_pair_sq_bound (N : ℕ) {p₁ p₂ : ℕ}
    (hp₂high : (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)) :
    (p₂ : ℝ) ^ 2 ≤ (N : ℝ) / (p₁ : ℝ) := by
  have hbnonneg : 0 ≤ (N : ℝ) / (p₁ : ℝ) := by positivity
  have hxnonneg : 0 ≤ (p₂ : ℝ) := by positivity
  have hle : (p₂ : ℝ) ^ 2 ≤ (((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)) ^ (2 : ℝ) := by
    have h' : (p₂ : ℝ) ^ (2 : ℝ) ≤ (((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)) ^ (2 : ℝ) :=
      Real.rpow_le_rpow hxnonneg hp₂high (by norm_num : 0 ≤ (2 : ℝ))
    simpa [Real.rpow_two] using h'
  rw [← Real.rpow_mul hbnonneg (1/2 : ℝ) (2 : ℝ)] at hle
  norm_num at hle
  exact hle

/-- **Auxiliary bound for R₁**: p₂ ≥ 2 and p₁p₂² ≤ N imply p₁p₂ ≤ N/2. -/
private lemma r1_pair_prod_le_half (N : ℕ) {p₁ p₂ : ℕ} (hp₂ge2 : 2 ≤ p₂)
    (hp₁sq : (p₁ : ℝ) * (p₂ : ℝ) ^ 2 ≤ (N : ℝ)) :
    (p₁ : ℝ) * (p₂ : ℝ) ≤ (N : ℝ) / 2 := by
  have hp₂ge2r : (2 : ℝ) ≤ (p₂ : ℝ) := by exact_mod_cast hp₂ge2
  have hp₂half : (p₂ : ℝ) ≤ (p₂ : ℝ) ^ 2 / 2 := by nlinarith [hp₂ge2r]
  calc
    (p₁ : ℝ) * (p₂ : ℝ) ≤ (p₁ : ℝ) * ((p₂ : ℝ) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hp₂half (by positivity : 0 ≤ (p₁ : ℝ))
    _ ≤ (N : ℝ) / 2 := by nlinarith [hp₁sq]

/-- **Auxiliary bound for R₁**: for positive p₁, p₂,
p₁p₂ ≤ N/2 implies N/(p₁p₂) ≥ 2. -/
private lemma r1_pair_x_ge_two (N : ℕ) {p₁ p₂ : ℕ} (hp₁ : 1 ≤ p₁) (hp₂ : 1 ≤ p₂)
    (hprod : (p₁ : ℝ) * (p₂ : ℝ) ≤ (N : ℝ) / 2) :
    (2 : ℝ) ≤ (N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ) := by
  have hdenpos : 0 < ((p₁ * p₂ : ℕ) : ℝ) := by
    exact_mod_cast (mul_pos (by omega : 0 < p₁) (by omega : 0 < p₂))
  rw [le_div_iff₀ hdenpos]
  have hcast : ((p₁ * p₂ : ℕ) : ℝ) = (p₁ : ℝ) * (p₂ : ℝ) := by norm_cast
  rw [hcast]
  nlinarith [hprod]

/-- **Auxiliary uniqueness for R₁**: for prime pairs satisfying
p₁ ≤ N^(1/3) < p₂ and p₁' ≤ N^(1/3) < p₂', equal products imply
equal pairs, by uniqueness of prime factorization. -/
private lemma r1_pair_unique (N : ℕ) {p₁ p₂ q₁ q₂ : ℕ}
    (hp₁prime : p₁.Prime) (_hp₂prime : p₂.Prime)
    (hq₁prime : q₁.Prime) (hq₂prime : q₂.Prime)
    (hp₁high : (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ))
    (_hp₂low : (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ))
    (_hq₁high : (q₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ))
    (hq₂low : (N : ℝ) ^ (1/3 : ℝ) < (q₂ : ℝ))
    (h : p₁ * p₂ = q₁ * q₂) :
    p₁ = q₁ ∧ p₂ = q₂ := by
  have hpdvd : p₁ ∣ q₁ * q₂ := by
    rw [← h]
    exact dvd_mul_right p₁ p₂
  rcases hp₁prime.dvd_mul.mp hpdvd with hq1 | hq2
  · have hpeq : p₁ = q₁ :=
      (prime_dvd_prime_iff_eq (Nat.prime_iff.mp hp₁prime) (Nat.prime_iff.mp hq₁prime)).mp hq1
    have hpq : p₂ * p₁ = q₂ * p₁ := by simpa [hpeq, mul_comm] using h
    have hq2eq : p₂ = q₂ := Nat.mul_right_cancel (Nat.Prime.pos hp₁prime) hpq
    exact ⟨hpeq, hq2eq⟩
  · have hpeq : p₁ = q₂ :=
      (prime_dvd_prime_iff_eq (Nat.prime_iff.mp hp₁prime) (Nat.prime_iff.mp hq₂prime)).mp hq2
    have hlt : (q₂ : ℝ) < (q₂ : ℝ) := by
      calc
        (q₂ : ℝ) = (p₁ : ℝ) := by exact_mod_cast hpeq.symm
        _ ≤ (N : ℝ) ^ (1/3 : ℝ) := hp₁high
        _ < (q₂ : ℝ) := hq₂low
    exact (lt_irrefl (q₂ : ℝ) hlt).elim

/-- **Sum reindexing**: Σ_a f(a)·G(a) = Σ_{p₁|d} Σ_{p₂} G(p₁·p₂).

Here f(a) indicates (a,d)>1 and a = p₁p₂ satisfying the range conditions.
The equivalence (a,d)>1 ⟺ p₁|d follows from `prime_pair_gcd_imp_dvd`
and the converse implication p₁|d ⟹ (a,d)>1.
The left sum is indexed by a and the right by (p₁,p₂). Each contributing a
has a unique pair, since p₁ ≤ N^(1/3) < p₂ and prime factorization is unique.
The bijection sends a to (p₁,p₂), with inverse (p₁,p₂) ↦ p₁p₂. -/
private lemma r1_sum_rewrite (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hN : 2 ≤ N)
    (d : ℕ) (hd : d ∣ selbergQ N ε) (G : ℕ → ℝ) :
    (Finset.range (N + 1)).sum (fun a =>
      (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
          (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
          (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
          a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) * G a) =
    ∑ p₁ ∈ d.primeFactors.filter (fun p₁ : ℕ => (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧
        (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ)),
      ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
        Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
          (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)),
        G (p₁ * p₂) := by
  -- Apply sum_bij between pairs (p₁,p₂) on the right and integers a on the left.
  -- First establish p₁p₂ ≤ N and that the product uniquely determines the pair.
  let S₁ : Finset ℕ := d.primeFactors.filter (fun p₁ : ℕ =>
      (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ))
  let S₂ : ℕ → Finset ℕ := fun p₁ => (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
      Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
        (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ))
  let cond : ℕ → Prop := fun a => ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
      (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
      (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧ (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ) ∧
      a = p₁ * p₂ ∧ 1 < Nat.gcd a d
  let A : Finset ℕ := (Finset.range (N + 1)).filter cond
  let P : Finset (Σ p₁ : ℕ, ℕ) := S₁.sigma S₂
  -- The left sum is the sum over A; terms outside the condition vanish.
  have hL : (Finset.range (N + 1)).sum (fun a =>
      (if cond a then (1 : ℝ) else 0) * G a) = A.sum G := by
    calc
      (Finset.range (N + 1)).sum (fun a => (if cond a then (1 : ℝ) else 0) * G a)
          = (Finset.range (N + 1)).sum (fun a => if cond a then G a else 0) := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : cond a
        · simp [h]
        · simp [h]
      _ = A.sum G := by
        exact (Finset.sum_filter cond G).symm
  -- The right sum is the sum over P, using the sigma decomposition.
  have hR : (∑ p₁ ∈ S₁, ∑ p₂ ∈ S₂ p₁, G (p₁ * p₂)) =
      P.sum (fun x => G (x.1 * x.2)) := by
    rw [Finset.sum_sigma]
  -- Bijection between A and P: a = p₁p₂.
  have hA : A.sum G = P.sum (fun x => G (x.1 * x.2)) := by
    refine (Finset.sum_bij (fun x hx => x.1 * x.2) ?_ ?_ ?_ ?_).symm
    · intro x hx
      -- x.1 ∈ S₁, x.2 ∈ S₂ x.1
      have hx₁S : x.1 ∈ S₁ := (Finset.mem_sigma.mp hx).1
      have hx₂S : x.2 ∈ S₂ x.1 := (Finset.mem_sigma.mp hx).2
      have hx₁f : x.1 ∈ d.primeFactors := (Finset.mem_filter.mp hx₁S).1
      have hx₁cond : (N : ℝ) ^ (1/10 : ℝ) < (x.1 : ℝ) ∧
          (x.1 : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) := (Finset.mem_filter.mp hx₁S).2
      have hx₁prime : (x.1).Prime := (Nat.mem_primeFactors.mp hx₁f).1
      have hx₁dvd : x.1 ∣ d := (Nat.mem_primeFactors.mp hx₁f).2.1
      have hx₂f : x.2 ∈ Finset.range (N + 1) := (Finset.mem_filter.mp hx₂S).1
      have hx₂cond : (x.2).Prime ∧ (N : ℝ) ^ (1/3 : ℝ) < (x.2 : ℝ) ∧
          (x.2 : ℝ) ≤ ((N : ℝ) / (x.1 : ℝ)) ^ (1/2 : ℝ) := (Finset.mem_filter.mp hx₂S).2
      have hx₂prime : (x.2).Prime := hx₂cond.1
      have hx₂low : (N : ℝ) ^ (1/3 : ℝ) < (x.2 : ℝ) := hx₂cond.2.1
      have hx₂high : (x.2 : ℝ) ≤ ((N : ℝ) / (x.1 : ℝ)) ^ (1/2 : ℝ) := hx₂cond.2.2
      -- x.1*x.2 ≤ N
      have hx₂sq : (x.2 : ℝ) ^ 2 ≤ (N : ℝ) / (x.1 : ℝ) := r1_pair_sq_bound N hx₂high
      have hx₁mul : (x.1 : ℝ) * (x.2 : ℝ) ^ 2 ≤ (N : ℝ) := by
        calc
          (x.1 : ℝ) * (x.2 : ℝ) ^ 2 ≤ (x.1 : ℝ) * ((N : ℝ) / (x.1 : ℝ)) :=
            mul_le_mul_of_nonneg_left hx₂sq (by positivity : 0 ≤ (x.1 : ℝ))
          _ = (N : ℝ) := by
            rw [mul_comm]
            exact div_mul_cancel₀ (N : ℝ)
              (ne_of_gt (by exact_mod_cast (Nat.Prime.pos hx₁prime) : 0 < (x.1 : ℝ)))
      have hx₂ge2 : 2 ≤ x.2 := hx₂prime.two_le
      have hx₂ge1 : 1 ≤ x.2 := by omega
      have hx₂ge1r : (1 : ℝ) ≤ (x.2 : ℝ) := by exact_mod_cast hx₂ge1
      have hx₂le : (x.2 : ℝ) ≤ (x.2 : ℝ) ^ 2 := by nlinarith [hx₂ge1r]
      have hxprodN : (x.1 : ℝ) * (x.2 : ℝ) ≤ (N : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_left hx₂le (by positivity : 0 ≤ (x.1 : ℝ))) hx₁mul
      have hxprod_le : x.1 * x.2 ≤ N := by exact_mod_cast hxprodN
      -- gcd(x.1*x.2, d) > 1
      have hg : x.1 ∣ Nat.gcd (x.1 * x.2) d :=
        Nat.dvd_gcd (dvd_mul_right x.1 x.2) hx₁dvd
      have hgcd_ne0 : Nat.gcd (x.1 * x.2) d ≠ 0 := by
        intro h0
        have hd0 : d = 0 := by
          exact Nat.eq_zero_of_zero_dvd (by simpa [h0] using (Nat.gcd_dvd_right (x.1 * x.2) d))
        have hzero : 0 ∣ selbergQ N ε := by simpa [hd0] using hd
        have hQne : selbergQ N ε ≠ 0 := by
          unfold selbergQ
          exact Finset.prod_ne_zero_iff.mpr (fun q hq => (Nat.Prime.ne_zero (mem_filter.mp hq).2.1))
        exact hQne (Nat.eq_zero_of_zero_dvd hzero)
      have hgcd_ne1 : Nat.gcd (x.1 * x.2) d ≠ 1 := by
        intro h1
        have hx1dvd1 : x.1 ∣ 1 := by simpa [h1] using hg
        have hx1eq : x.1 = 1 := Nat.dvd_one.mp hx1dvd1
        have hx1ge2 : 2 ≤ x.1 := hx₁prime.two_le
        exact (by omega : x.1 ≠ 1) hx1eq
      have hgcd : 1 < Nat.gcd (x.1 * x.2) d := by omega
      -- a = x.1*x.2 satisfies the conditions.
      have ha_mem : x.1 * x.2 ∈ Finset.range (N + 1) := by
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le hxprod_le
      have hcondA : cond (x.1 * x.2) :=
        ⟨x.1, x.2, hx₁prime, hx₂prime, hx₁cond.1, hx₁cond.2, hx₂low, hx₂high, rfl, hgcd⟩
      exact Finset.mem_filter.mpr ⟨ha_mem, hcondA⟩
    · intro x hx y hy hprod
      have hx₁S : x.1 ∈ S₁ := (Finset.mem_sigma.mp hx).1
      have hx₂S : x.2 ∈ S₂ x.1 := (Finset.mem_sigma.mp hx).2
      have hx₁f : x.1 ∈ d.primeFactors := (Finset.mem_filter.mp hx₁S).1
      have hx₁high : (x.1 : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) := (Finset.mem_filter.mp hx₁S).2.2
      have hx₁prime : (x.1).Prime := (Nat.mem_primeFactors.mp hx₁f).1
      have hx₂cond : (x.2).Prime ∧ (N : ℝ) ^ (1/3 : ℝ) < (x.2 : ℝ) ∧
          (x.2 : ℝ) ≤ ((N : ℝ) / (x.1 : ℝ)) ^ (1/2 : ℝ) := (Finset.mem_filter.mp hx₂S).2
      have hx₂prime : (x.2).Prime := hx₂cond.1
      have hx₂low : (N : ℝ) ^ (1/3 : ℝ) < (x.2 : ℝ) := hx₂cond.2.1
      have hy₁S : y.1 ∈ S₁ := (Finset.mem_sigma.mp hy).1
      have hy₂S : y.2 ∈ S₂ y.1 := (Finset.mem_sigma.mp hy).2
      have hy₁f : y.1 ∈ d.primeFactors := (Finset.mem_filter.mp hy₁S).1
      have hy₁high : (y.1 : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) := (Finset.mem_filter.mp hy₁S).2.2
      have hy₁prime : (y.1).Prime := (Nat.mem_primeFactors.mp hy₁f).1
      have hy₂cond : (y.2).Prime ∧ (N : ℝ) ^ (1/3 : ℝ) < (y.2 : ℝ) ∧
          (y.2 : ℝ) ≤ ((N : ℝ) / (y.1 : ℝ)) ^ (1/2 : ℝ) := (Finset.mem_filter.mp hy₂S).2
      have hy₂prime : (y.2).Prime := hy₂cond.1
      have hy₂low : (N : ℝ) ^ (1/3 : ℝ) < (y.2 : ℝ) := hy₂cond.2.1
      rcases r1_pair_unique N hx₁prime hx₂prime hy₁prime hy₂prime hx₁high hx₂low hy₁high
          hy₂low hprod with ⟨h₁, h₂⟩
      apply Sigma.ext
      · exact h₁
      · simpa using h₂
    · intro b hb
      have hb_cond : cond b := (Finset.mem_filter.mp hb).2
      rcases hb_cond with ⟨p₁, p₂, hp₁prime, hp₂prime, hp₁low, hp₁high, hp₂low, hp₂high,
          hb_eq, hgcd⟩
      have hQne : selbergQ N ε ≠ 0 := by
        unfold selbergQ
        exact Finset.prod_ne_zero_iff.mpr (fun q hq => (Nat.Prime.ne_zero (mem_filter.mp hq).2.1))
      have hdne : d ≠ 0 := by
        intro hd0
        have hzero : 0 ∣ selbergQ N ε := by simpa [hd0] using hd
        exact hQne (Nat.eq_zero_of_zero_dvd hzero)
      have hp₁dvd : p₁ ∣ d :=
        prime_pair_gcd_imp_dvd N ε hε hN hd hp₁prime hp₂prime hp₂low hb_eq hgcd
      have hp₁f : p₁ ∈ d.primeFactors := (Nat.mem_primeFactors).2 ⟨hp₁prime, hp₁dvd, hdne⟩
      have hp₁S₁ : p₁ ∈ S₁ := Finset.mem_filter.mpr ⟨hp₁f, ⟨hp₁low, hp₁high⟩⟩
      -- p₂ ∈ range (N+1): p₂ ≤ (N/p₁)^(1/2) ≤ N
      have hp₁ge2 : 2 ≤ p₁ := hp₁prime.two_le
      have hp₁ge1r : (1 : ℝ) ≤ (p₁ : ℝ) := by exact_mod_cast (by omega : 1 ≤ p₁)
      have hp₂sq : (p₂ : ℝ) ^ 2 ≤ (N : ℝ) / (p₁ : ℝ) := r1_pair_sq_bound N hp₂high
      have hdiv_le : (N : ℝ) / (p₁ : ℝ) ≤ (N : ℝ) := by
        calc
          (N : ℝ) / (p₁ : ℝ) = (N : ℝ) * (1 / (p₁ : ℝ)) := by ring
          _ ≤ (N : ℝ) * 1 := by
            apply mul_le_mul_of_nonneg_left
            · rw [div_le_iff₀ (by positivity : 0 < (p₁ : ℝ))]
              simpa using hp₁ge1r
            · positivity
          _ = (N : ℝ) := by ring
      have hp₂sq_le_N : (p₂ : ℝ) ^ 2 ≤ (N : ℝ) := le_trans hp₂sq hdiv_le
      have hp₂ge2 : 2 ≤ p₂ := hp₂prime.two_le
      have hp₂ge1 : 1 ≤ p₂ := by omega
      have hp₂ge1r : (1 : ℝ) ≤ (p₂ : ℝ) := by exact_mod_cast hp₂ge1
      have hp₂leN_r : (p₂ : ℝ) ≤ (N : ℝ) := by
        calc
          (p₂ : ℝ) ≤ (p₂ : ℝ) ^ 2 := by nlinarith [hp₂ge1r]
          _ ≤ (N : ℝ) := hp₂sq_le_N
      have hp₂leN : p₂ ≤ N := by exact_mod_cast hp₂leN_r
      have hp₂range : p₂ ∈ Finset.range (N + 1) := by
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le hp₂leN
      have hp₂S₂ : p₂ ∈ S₂ p₁ :=
        Finset.mem_filter.mpr ⟨hp₂range, ⟨hp₂prime, hp₂low, hp₂high⟩⟩
      refine ⟨⟨p₁, p₂⟩, Finset.mem_sigma.mpr ⟨hp₁S₁, hp₂S₂⟩, ?_⟩
      change p₁ * p₂ = b
      exact hb_eq.symm
    · intro x hx
      rfl
  change (Finset.range (N + 1)).sum (fun a => (if cond a then (1 : ℝ) else 0) * G a) =
      ∑ p₁ ∈ S₁, ∑ p₂ ∈ S₂ p₁, G (p₁ * p₂)
  rw [hL, hA, hR]

/-- **R₁ upper-bound interface** for the contribution with (a,d)>1:

  R₁ ≪ Σ_{d|Q} 3^ω(d)/φ(d) · max Σ_{(a,d)>1} f(a) · li(N/a)
     ≪ (log N)³ · N

**Limitation of an unrestricted divisor estimate**
(see the known-error discussion in `pan-wang-ding-1975.md`):
the estimate attributed there to Pan et al. (1975) and Liu (2022) is
  Σ_{p₁|d, p₁>N^(1/10)} 1/p₁ ≪ N^(-1/10),
leading to R₁ ≪ N^(9/10)(log N)³. Without a size restriction on d, that
reciprocal-sum estimate is false: for d = ∏_{N^(1/10)<p≤N^(1/4)} p,
the left side tends to the positive constant log(5/2), not to zero.
The bound used here instead applies Lemma 1 twice:
  Σ_{p₁|d, p₁∈(N^(1/10),N^(1/3)]} 1/p₁ ≤ C₀,
  Σ_{p₂∈(N^(1/3),(N/p₁)^(1/2)]} 1/p₂ ≤ C₁.
Since li(N/a) ≪ N/a, the inner sum is ≪ N, giving the scale
R₁ ≪ (log N)³·N. This suffices for the bound below, not for a uniform
N/log^A N error estimate. The theorem's constant is quantified after N. -/
theorem r1_upper_bound (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hN : ∃ N₀ : ℕ, N₀ ≤ N) :
    ∃ C : ℝ,
      ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d *
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) *
            (logarithmicIntegral_approx_term ((N : ℝ) / a)))) ≤
      C * (log N) ^ (3 : ℝ) * (N : ℝ) := by
  -- For N < 8, no prime p₁ satisfies 2 ≤ p₁ ≤ N^(1/3) < 2, so the sum is zero.
  by_cases hNlt8 : N < 8
  · -- Every (a,d) summand has an impossible condition, so the sum is zero.
    refine ⟨0, ?_⟩
    have hL0 : ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d *
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) *
            (logarithmicIntegral_approx_term ((N : ℝ) / a)))) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      have hinner : (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) *
            (logarithmicIntegral_approx_term ((N : ℝ) / a))) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        by_cases hcond : ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
            (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
            (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
            a = p₁ * p₂ ∧ 1 < Nat.gcd a d
        · exfalso
          rcases hcond with ⟨p₁, p₂, hp₁p, hp₂p, hp₁low, hp₁high, hp₂low, hp₂high, haeq, hgcd⟩
          have hp1ge2 : 2 ≤ p₁ := hp₁p.two_le
          -- N < 8 gives N^(1/3) < 8^(1/3) = 2, contradicting 2 ≤ p₁ ≤ N^(1/3).
          have hcube_lt : (N : ℝ) ^ (1/3 : ℝ) < (2 : ℝ) := by
            have hNlt : (N : ℝ) < 8 := by exact_mod_cast hNlt8
            have h8 : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
            have hNp : (N : ℝ) ^ (1/3 : ℝ) < (8 : ℝ) ^ (1/3 : ℝ) := by
              exact Real.rpow_lt_rpow (by positivity : 0 ≤ (N : ℝ)) hNlt (by norm_num)
            have h8p : (8 : ℝ) ^ (1/3 : ℝ) = (2 : ℝ) := by
              rw [h8]
              rw [← Real.rpow_natCast (2 : ℝ) 3]
              change ((2 : ℝ) ^ (3 : ℝ)) ^ (1/3 : ℝ) = 2
              rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)) 3 (1/3 : ℝ)]
              norm_num
            rwa [h8p] at hNp
          have hp1ge2r : (2 : ℝ) ≤ (p₁ : ℝ) := by exact_mod_cast hp1ge2
          have hlt : (2 : ℝ) < (2 : ℝ) := lt_of_le_of_lt hp1ge2r (lt_of_le_of_lt hp₁high hcube_lt)
          exact lt_irrefl (2 : ℝ) hlt
        · rw [if_neg hcond]
          ring
      rw [hinner]
      ring
    rw [hL0]
    norm_num
  -- The case N ≥ 8.
  · have hN8 : 8 ≤ N := by omega
    have hN3 : 3 ≤ N := by omega
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hNge1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    obtain ⟨C₀, hC₀nonneg, hC₀⟩ := prime_divisor_recip_sum_bounded_real N ε hε hN8
    obtain ⟨C₁, hC₁nonneg, hC₁⟩ := prime_recip_sum_inner_bounded N hN8
    let C₃ : ℝ := max (1 / log 2) 1
    have hC₃pos : 0 < C₃ := by
      unfold C₃
      have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      have h : 0 < 1 / log 2 := by positivity
      exact lt_of_lt_of_le h (le_max_left _ _)
    -- Inner sum S_d ≪ N: for each d, Σ_a [..]·li(N/a) ≤ C₃·C₁·C₀·N.
    have hS : ∀ d : ℕ, d ∈ (selbergQ N ε).divisors →
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) *
            (logarithmicIntegral_approx_term ((N : ℝ) / a))) ≤
        C₃ * C₁ * C₀ * (N : ℝ) := by
      intro d hd
      -- li(x) ≤ C₃·x for x ≥ 2, since li(x) = x/log x and log x ≥ log 2.
      have hli : ∀ x : ℝ, 2 ≤ x → logarithmicIntegral_approx_term x ≤ C₃ * x := by
        intro x hx
        have hxlog : 0 < log x := Real.log_pos (by linarith : (1 : ℝ) < x)
        have hlogge : log 2 ≤ log x := Real.log_le_log (by norm_num) hx
        have hpos : 0 < log 2 := by positivity
        have hle1 : logarithmicIntegral_approx_term x ≤ x / log x := by
          unfold logarithmicIntegral_approx_term
          rfl
        have hdiv : x / log x ≤ (1 / log 2) * x := by
          have h1 : 1 / log x ≤ 1 / log 2 := by
            exact one_div_le_one_div_of_le hpos hlogge
          calc x / log x = (1 / log x) * x := by ring
            _ ≤ (1 / log 2) * x := mul_le_mul_of_nonneg_right h1 (by positivity)
        unfold C₃
        have hposx : 0 ≤ x := by linarith
        have hlemax : (1 / log 2) * x ≤ max (1 / log 2) 1 * x := by
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hposx
        exact le_trans hle1 (le_trans hdiv hlemax)
      -- Main inequality: S_d ≤ C₃·N·(Σ_{p₁|d} 1/p₁)·(Σ_{p₂} 1/p₂).
      have hS_bound : (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) *
            (logarithmicIntegral_approx_term ((N : ℝ) / a))) ≤
          C₃ * C₁ * C₀ * (N : ℝ) := by
        -- Reindex: Σ_a f(a)·li(N/a) = Σ_{p₁,p₂} li(N/(p₁p₂)).
        have hdvd : d ∣ selbergQ N ε := (Nat.mem_divisors.mp hd).1
        have hN2 : 2 ≤ N := by omega
        rw [r1_sum_rewrite N ε hε hN2 d hdvd
          (fun a => logarithmicIntegral_approx_term ((N : ℝ) / (a : ℝ)))]
        -- Termwise bound: li(N/(p₁p₂)) ≤ C₃·N·(1/p₁)·(1/p₂).
        have hterm : ∀ p₁ : ℕ, p₁ ∈ d.primeFactors.filter (fun p₁ : ℕ =>
              (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ)) →
            ∀ p₂ : ℕ, p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
              Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)) →
            logarithmicIntegral_approx_term ((N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ)) ≤
              C₃ * (N : ℝ) * (1 / (p₁ : ℝ)) * (1 / (p₂ : ℝ)) := by
          intro p₁ hp₁ p₂ hp₂
          have hp₁prime : p₁.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp₁).1).1
          have hp₂prime : p₂.Prime := (Finset.mem_filter.mp hp₂).2.1
          have hp₂high : (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ) :=
            (Finset.mem_filter.mp hp₂).2.2.2
          have hp₁ge2 : 2 ≤ p₁ := hp₁prime.two_le
          have hp₂ge2 : 2 ≤ p₂ := hp₂prime.two_le
          have hp₁pos : 0 < (p₁ : ℝ) := by exact_mod_cast (Nat.Prime.pos hp₁prime)
          have hp₂pos : 0 < (p₂ : ℝ) := by exact_mod_cast (Nat.Prime.pos hp₂prime)
          have hp₂sq : (p₂ : ℝ) ^ 2 ≤ (N : ℝ) / (p₁ : ℝ) := r1_pair_sq_bound N hp₂high
          have hp₁mul : (p₁ : ℝ) * (p₂ : ℝ) ^ 2 ≤ (N : ℝ) := by
            calc
              (p₁ : ℝ) * (p₂ : ℝ) ^ 2 ≤ (p₁ : ℝ) * ((N : ℝ) / (p₁ : ℝ)) :=
                mul_le_mul_of_nonneg_left hp₂sq (by positivity : 0 ≤ (p₁ : ℝ))
              _ = (N : ℝ) := by
                rw [mul_comm]
                exact div_mul_cancel₀ (N : ℝ) (ne_of_gt hp₁pos)
          have hprodN2 : (p₁ : ℝ) * (p₂ : ℝ) ≤ (N : ℝ) / 2 :=
            r1_pair_prod_le_half N hp₂ge2 hp₁mul
          have hxge2 : (2 : ℝ) ≤ (N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ) :=
            r1_pair_x_ge_two N (by omega : 1 ≤ p₁) (by omega : 1 ≤ p₂) hprodN2
          have hli' := hli ((N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ)) hxge2
          calc
            logarithmicIntegral_approx_term ((N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ)) ≤
                C₃ * ((N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ)) := hli'
            _ = C₃ * (N : ℝ) * (1 / (p₁ : ℝ)) * (1 / (p₂ : ℝ)) := by
              norm_cast
              field_simp [ne_of_gt hp₁pos, ne_of_gt hp₂pos]
              norm_cast
        -- Inner sum: Σ_{p₂} li(N/(p₁p₂)) ≤ C₃·N·(1/p₁)·C₁.
        have hinner : ∀ p₁ : ℕ, p₁ ∈ d.primeFactors.filter (fun p₁ : ℕ =>
              (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ)) →
            (∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
              Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)),
              logarithmicIntegral_approx_term ((N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ))) ≤
              (C₃ * (N : ℝ) * C₁) * (1 / (p₁ : ℝ)) := by
          intro p₁ hp₁
          have hp₁prime : p₁.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp₁).1).1
          have hp₁low : (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) := (Finset.mem_filter.mp hp₁).2.1
          have hp₁high : (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) := (Finset.mem_filter.mp hp₁).2.2
          have hp₁2 : 2 ≤ p₁ := hp₁prime.two_le
          have hp₁pos : 0 < (p₁ : ℝ) := by exact_mod_cast (Nat.Prime.pos hp₁prime)
          have hb₁ := hC₁ p₁ hp₁low hp₁high hp₁2
          have hdivrpow : ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ) =
              (N : ℝ) ^ (1/2 : ℝ) / (p₁ : ℝ) ^ (1/2 : ℝ) :=
            Real.div_rpow (by positivity : 0 ≤ (N : ℝ)) (by positivity : 0 ≤ (p₁ : ℝ))
              (1/2 : ℝ)
          have hb₁' : (∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
                Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                  (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)),
              1 / (p₂ : ℝ)) ≤ C₁ := by
            rw [show (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
                Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                  (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)) =
                (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
                Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                  (p₂ : ℝ) ≤ (N : ℝ) ^ (1/2 : ℝ) / (p₁ : ℝ) ^ (1/2 : ℝ)) by
              apply Finset.filter_congr
              intro p₂ hp₂
              rw [hdivrpow]]
            exact hb₁
          calc
            (∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
                Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                  (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)),
              logarithmicIntegral_approx_term ((N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ))) ≤
                (∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
                  Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                    (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)),
                  C₃ * (N : ℝ) * (1 / (p₁ : ℝ)) * (1 / (p₂ : ℝ))) :=
              Finset.sum_le_sum (fun p₂ hp₂ => hterm p₁ hp₁ p₂ hp₂)
            _ = (C₃ * (N : ℝ) * (1 / (p₁ : ℝ))) * (∑ p₂ ∈ (Finset.range (N + 1)).filter
                  (fun p₂ : ℕ => Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                    (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)),
                1 / (p₂ : ℝ)) := by
              rw [← Finset.mul_sum]
            _ ≤ (C₃ * (N : ℝ) * (1 / (p₁ : ℝ))) * C₁ := by
              apply mul_le_mul_of_nonneg_left
              · exact hb₁'
              · positivity
            _ = (C₃ * (N : ℝ) * C₁) * (1 / (p₁ : ℝ)) := by ring
        -- Outer sum: Σ_{p₁} Σ_{p₂} li(N/(p₁p₂)) ≤ C₃·C₁·C₀·N.
        calc
          (∑ p₁ ∈ d.primeFactors.filter (fun p₁ : ℕ =>
              (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ)),
            ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
              Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)),
              logarithmicIntegral_approx_term ((N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ))) ≤
              (∑ p₁ ∈ d.primeFactors.filter (fun p₁ : ℕ =>
                (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ)),
                (C₃ * (N : ℝ) * C₁) * (1 / (p₁ : ℝ))) :=
            Finset.sum_le_sum (fun p₁ hp₁ => hinner p₁ hp₁)
          _ = (C₃ * (N : ℝ) * C₁) * (∑ p₁ ∈ d.primeFactors.filter (fun p₁ : ℕ =>
                (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ)),
              1 / (p₁ : ℝ)) := by
            rw [← Finset.mul_sum]
          _ ≤ (C₃ * (N : ℝ) * C₁) * C₀ := by
            apply mul_le_mul_of_nonneg_left
            · exact hC₀ d hdvd
            · positivity
          _ = C₃ * C₁ * C₀ * (N : ℝ) := by ring
      exact hS_bound
    -- Combine: Σ_d 3^ω(d)/φ(d) · S_d.
    obtain ⟨C', hC'⟩ := divisor_sum_3_omega_bound N ε hε hN3
    have hwpos : ∀ d : ℕ, d ∈ (selbergQ N ε).divisors → 0 ≤
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d := by
      intro d hd
      positivity
    have hsum : ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d *
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) *
            logarithmicIntegral_approx_term ((N : ℝ) / a))) ≤
        ((selbergQ N ε).divisors).sum (fun d =>
          (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) * (C₃ * C₁ * C₀ * (N : ℝ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (hS d hd) (hwpos d hd)
    have hC'le : ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) ≤ C' * (log N) ^ (3 : ℝ) :=
      hC'
    have hlog3pos : 0 < (log N) ^ (3 : ℝ) := by
      have hlog : 0 < log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      positivity
    have hsumle : ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) * (C₃ * C₁ * C₀ * (N : ℝ)) ≤
        C' * (log N) ^ (3 : ℝ) * (C₃ * C₁ * C₀ * (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hC'le (by positivity)
    refine ⟨C' * (C₃ * C₁ * C₀), ?_⟩
    calc
      ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d *
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) *
            logarithmicIntegral_approx_term ((N : ℝ) / a))) ≤
        ((selbergQ N ε).divisors).sum (fun d =>
          (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) * (C₃ * C₁ * C₀ * (N : ℝ)) := hsum
      _ ≤ C' * (log N) ^ (3 : ℝ) * (C₃ * C₁ * C₀ * (N : ℝ)) := hsumle
      _ = (C' * (C₃ * C₁ * C₀)) * (log N) ^ (3 : ℝ) * (N : ℝ) := by
        ring

/-- **Pointwise constant interface** at the scale N^(9/10) (log N)².

The constant C may depend on the individual N. A uniform Liu-type bound
would require the constant to be quantified before `∀ N`. -/
theorem r1_simplified_bound (N : ℕ) (ε : ℝ) (_hε : 0 < ε) (hN : 2 ≤ N) :
    ∃ C : ℝ,
      ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d *
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) *
            (logarithmicIntegral_approx_term ((N : ℝ) / a)))) ≤
      C * (N : ℝ) ^ (9/10 : ℝ) * (log N) ^ 2 := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hscale : 0 < (N : ℝ) ^ (9 / 10 : ℝ) * (log N) ^ 2 :=
    mul_pos (Real.rpow_pos_of_pos hNpos _) (pow_pos hlog 2)
  simp only [mul_assoc]
  exact exists_multiplicative_error _ _ hscale

/-- **Pointwise interface for the complete error**, motivated by Liu's
correction and the target R = R₀ + R₁ ≪ N/log^A N.

  - R₀ is the part with (a,d)=1, for which Pan's mean-value theorem supplies
    the intended estimate R₀ ≪ N/log^A N.
  - R₁ is the part with (a,d)>1. A uniform estimate
    R₁ ≪ N^(9/10) (log N)² would imply R₁ ≪ N/log^A N for sufficiently large N.

Liu (2022) addresses the omission of the case (a,d)>1 in Pan et al. (1975).

The quantifier order here still expresses only a pointwise error constant.
It does not establish the uniform estimates in this outline, and
`r1_simplified_bound` is also only a pointwise interface. -/
theorem complete_error_bound_corrected (N : ℕ) (ε : ℝ) (A : ℝ)
    (_hε : 0 < ε) (_hA : 0 < A) (hN : 2 ≤ N) :
    ∃ C : ℝ,
      ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) *
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ then (1 : ℝ) else 0) *
            ((primesInAP N d (N % d) : ℝ) -
              logarithmicIntegral_approx_term ((N : ℝ) / a) / Nat.totient d))) ≤
      C * (N : ℝ) / (log N) ^ A := by
  have hlog : 0 < log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hscale : 0 < (N : ℝ) / (log N) ^ A :=
    div_pos (by exact_mod_cast (by omega : 0 < N)) (Real.rpow_pos_of_pos hlog A)
  simp only [mul_div_assoc]
  exact exists_multiplicative_error _ _ hscale

/-! ## 8. Mathematical scope -/

/-
**Selberg upper-sieve definitions and bounds**:

1. **Definitions**:
   - `SelbergWeights`: normalization, support, and size conditions on λ_d
   - `selbergQ`: the product of primes below the cutoff that do not divide N
   - `selbergLambdaSquared`: a bridge to Mathlib's `lambdaSquared`
   - `primesInAP_weighted`: a local progression count requiring ap to be prime
   - `weightedDistributionError`: the weighted distribution error

2. **Fixed-parameter interfaces and finite algebraic results**:
   - `selberg_sieve_weights_exist` (Lemma 3 interface): weights with a pointwise remainder
   - `lemma4_numerical_bound`: a fixed-parameter remainder, not the classical integral bound
   - `integral_margin`: `0.49253 < 0.49254`, not a formalization of the integral estimate
   - `logarithmicIntegral_approx`: the local approximation term is x/log x by definition
   - `coefficient_product`: 8 × 0.49254 = 3.94032
   - `lcm_pair_count`: the combinatorial interpretation of 3^ω(d) for squarefree d
   - `divisor_sum_bound` and `divisor_sum_bound_mu2`: uniform divisor-sum bounds

3. **Pointwise bounds, distinct from classical uniform conclusions**:
   - `main_term_bound`: M₁ ≤ 3.94033 𝔖(N) N/log²N plus a pointwise remainder
   - `error_term_bound`: a fixed-parameter remainder on the N/log^A N scale,
     not Pan's mean-value theorem
   - `chenOmega_complete_bound`: Ω ≤ 3.9404 𝔖(N) N/log²N plus a remainder
   - `chenOmega_simple_bound`: the same pointwise shape without ε
   - `coprime_condition_implies_bounded_ap`: (a,d)>1 implies π ≤ 1 for the local count

4. **Mathlib correspondences**:
   - `selberg_lambda_is_upper_moebius`: Selberg weights give `IsUpperMoebius`
   - `omega_upper_bound_via_mathlib`: `siftedSum_le_mainSum_errSum_of_upperMoebius`
   - `mainSum_diag_via_mathlib`: `mainSum_lambdaSquared_eq_sum_mul_sum_sq`
   - `mainSum_cauchy_schwarz_lower_bound`: the finite Cauchy-Schwarz lower bound

5. **Requirements for the classical uniform bounds**:
   - Lemma 3 requires optimized Selberg weights and analytic estimates,
     beyond the Mathlib Λ²-sieve diagonalization and the bridges here.
   - Lemma 4 requires Mertens' theorem, partial summation, and the integral bound.
   - The error estimate requires Pan's mean-value theorem
     (see `BombieriVinogradov.lean`) and control of the noncoprime contribution.

6. **Numerical constants**:
   - 8 × 0.49254 = 3.94032 < 3.94033 (main-term coefficient with a margin)
   - 0.49254 (the integral upper bound in Chen 1973, equation (28))
   - 3.9404 = 3.94033 + 0.00007 (including the error margin)
-/

end MathlibNt.SieveTheory.SelbergUpperBound
