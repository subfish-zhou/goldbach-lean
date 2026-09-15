import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import AnalyticNumberTheory.Sieve.BombieriVinogradov

/-! # AnalyticNumberTheory.Sieve.WeightedPan

## Weighted Pan--Bombieri--Vinogradov input

The upper bound for `Ω` in Chen's theorem, and more general
Goldbach-type sieves, requires a weighted **average** distribution
condition, not a uniform bound for each modulus:
for each `A > 0`, a uniform constant `C` gives
`Σ_{d|P} 3^{ω(d)}·|Δ(d)| ≤ C·x/log^A x`.
Here `Δ(d)` is the difference between the congruence count and
`ν(d)·x/log x`. The weight counts pairs `(d₁,d₂)` with
`[d₁,d₂]=d` in the Selberg expansion (`lcmPairCount`).

This module supplies:

1. **Finite weight identities**: for squarefree `d`,
   `3^{ω(d)}` counts lcm pairs; hence
   `Σ_{d|Q}3^{ω(d)}f(d) = Σ_{d₁|Q}Σ_{d₂|Q}f([d₁,d₂])`
   for squarefree `Q` (`lcmPairWeightedSum`).
2. **Sieve application interface**: `WeightedPanCondition` for a
   family `S N : BoundingSieve` and scale `x N`.
   In the Chen specialization, `x N = N`,
   `S N = correctedChenBoundingSieve N`, and `w d = 3^{ω(d)}`;
   `|S.rem d|` is the absolute congruence-count error
   `|#{p∈support : p≡N [MOD d]} − ν(d)·N/log N|`.
3. **Weighted mean-value target**: `PanMeanValueUniform` has
   the classical logarithmic-saving shape
   `Σ_{q≤(x X)^{1/2}/log^B(x X)} μ²(q)·3^{ω(q)}
    ·max_{y≤x X} max_{0<l<q,(l,q)=1}
       |Σ_{a≤X,(a,q)=1} f(a)·Δ(y;a,q,l)|
    ≤ C·x X/log^A(x X)`,
   with constants preceding all sufficiently large `X`.

The large sieve and Vaughan's identity are analytic ingredients
for the classical Pan theorem (Pan 1963; Halberstam--Richert
1974 Ch. 10; Liu 2022 §III). This module fixes definitions and
proves finite bridges, not an unconditional uniform mean-value
theorem. The implemented main term uses the `x/log x` proxy;
connecting it to a classical logarithmic-integral formulation
and to sieve remainders requires additional main-term and support
analysis. The coarse polylogarithmic proposition is kept separate.

References:
  - Pan, C.D. (1963), Sci. Sinica 12, 465-473
  - Bombieri, E. (1965), Math. Ann. 157, 220-260
  - Vinogradov, A.I. (1965), Izv. Akad. Nauk SSSR 29, 903-934
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 10
  - Liu, Z. (2022), arXiv:2203.07871
-/

namespace AnalyticNumberTheory.Sieve

open Finset Real

open scoped Classical
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.omega

/-! ## 1. Origin of the weight: 3^{ω(d)} counts lcm pairs -/

/-- For squarefree `d`, exactly `3^{ω(d)}` divisor pairs
`(d₁,d₂)` satisfy `lcm d₁ d₂ = d`.
Each prime factor has three exponent choices:
`(0,1)`, `(1,0)`, and `(1,1)`. This is the exact source of
the Selberg upper-sieve weight `3^{ω(d)}`. -/
theorem lcmPairCount (d : ℕ) (hsq : Squarefree d) :
    ((d.divisors ×ˢ d.divisors).filter (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d)).card =
      3 ^ d.primeFactors.card := by
  have hω : d.primeFactors.card = ArithmeticFunction.cardDistinctFactors d := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
      Nat.toFinset_factors]
  rw [hω, ← Nat.card_pair_lcm_eq hsq]

/-- The lcm of two divisors of squarefree `Q` still divides `Q`,
by the defining divisibility property of the lcm. -/
private theorem lcm_dvd_of_squarefree {Q d₁ d₂ : ℕ} (_hQ : Squarefree Q)
    (h₁ : d₁ ∣ Q) (h₂ : d₂ ∣ Q) : Nat.lcm d₁ d₂ ∣ Q := by
  exact Nat.lcm_dvd h₁ h₂

/-- **Grouping the Selberg double sum**: for squarefree `Q`,
`Σ_{d|Q} 3^{ω(d)}·f(d) = Σ_{d₁|Q} Σ_{d₂|Q} f([d₁,d₂])`.
The weight counts pairs with lcm `d` (`lcmPairCount`).
This exact finite identity turns the lcm double sum into
the single weighted sum used by the Pan input. -/
theorem lcmPairWeightedSum (Q : ℕ) (hQ : Squarefree Q) (f : ℕ → ℝ) :
    ∑ d ∈ Q.divisors, (3 : ℝ) ^ d.primeFactors.card * f d =
      ∑ d₁ ∈ Q.divisors, ∑ d₂ ∈ Q.divisors, f (Nat.lcm d₁ d₂) := by
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ0
  calc
    ∑ d ∈ Q.divisors, (3 : ℝ) ^ d.primeFactors.card * f d
        = ∑ d ∈ Q.divisors,
            ∑ x ∈ (d.divisors ×ˢ d.divisors).filter
                (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d),
              f (Nat.lcm x.1 x.2) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdvd : d ∣ Q := (Nat.mem_divisors.mp hd).1
            have hd0 : d ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hdvd hQpos)
            have hsqd : Squarefree d := Squarefree.squarefree_of_dvd hdvd hQ
            calc
              (3 : ℝ) ^ d.primeFactors.card * f d
                  = ((d.divisors ×ˢ d.divisors).filter
                        (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d)).card * f d := by
                  rw [lcmPairCount d hsqd, Nat.cast_pow]
                  norm_num
              _ = ∑ x ∈ (d.divisors ×ˢ d.divisors).filter
                      (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d),
                    f d := by
                  simp [Finset.sum_const, nsmul_eq_mul]
              _ = ∑ x ∈ (d.divisors ×ˢ d.divisors).filter
                      (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d),
                    f (Nat.lcm x.1 x.2) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [(Finset.mem_filter.mp hx).2]
    _ = ∑ x ∈ Q.divisors.sigma
            (fun d => (d.divisors ×ˢ d.divisors).filter
              (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d)),
          f (Nat.lcm x.2.1 x.2.2) := by
          rw [Finset.sum_sigma]
    _ = ∑ x ∈ Q.divisors ×ˢ Q.divisors, f (Nat.lcm x.1 x.2) := by
          apply Finset.sum_nbij (fun x : (Σ d : ℕ, ℕ × ℕ) => x.2)
          · intro x hx
            rcases Finset.mem_sigma.mp hx with ⟨hxd, hx2⟩
            have hx2' : x.2 ∈ x.1.divisors ×ˢ x.1.divisors ∧
                Nat.lcm x.2.1 x.2.2 = x.1 := Finset.mem_filter.mp hx2
            have hprod : x.2 ∈ x.1.divisors ×ˢ x.1.divisors := hx2'.1
            have hx1dvd : x.1 ∣ Q := (Nat.mem_divisors.mp hxd).1
            have hdvd₁ : x.2.1 ∣ Q :=
              ((Nat.mem_divisors.mp (Finset.mem_product.mp hprod).1).1).trans hx1dvd
            have hdvd₂ : x.2.2 ∣ Q :=
              ((Nat.mem_divisors.mp (Finset.mem_product.mp hprod).2).1).trans hx1dvd
            exact Finset.mem_product.mpr
              ⟨Nat.mem_divisors.mpr ⟨hdvd₁, hQ0⟩, Nat.mem_divisors.mpr ⟨hdvd₂, hQ0⟩⟩
          · intro a₁ ha₁ a₂ ha₂ hpair
            rcases Finset.mem_sigma.mp ha₁ with ⟨_, ha₁₂⟩
            rcases Finset.mem_sigma.mp ha₂ with ⟨_, ha₂₂⟩
            have hlcm₁ : Nat.lcm a₁.2.1 a₁.2.2 = a₁.1 := (Finset.mem_filter.mp ha₁₂).2
            have hlcm₂ : Nat.lcm a₂.2.1 a₂.2.2 = a₂.1 := (Finset.mem_filter.mp ha₂₂).2
            cases a₁ with
            | mk d₁ x₁ =>
              cases a₂ with
            | mk d₂ x₂ =>
                have hx : x₁ = x₂ := by simpa using hpair
                subst x₂
                have hd₁ : d₁ = Nat.lcm x₁.1 x₁.2 := by simpa using hlcm₁.symm
                have hd₂ : d₂ = Nat.lcm x₁.1 x₁.2 := by simpa using hlcm₂.symm
                rw [hd₁, hd₂]
          · intro y hy
            rcases Finset.mem_product.mp hy with ⟨hy₁, hy₂⟩
            have hdvd₁ : y.1 ∣ Q := (Nat.mem_divisors.mp hy₁).1
            have hdvd₂ : y.2 ∣ Q := (Nat.mem_divisors.mp hy₂).1
            have hd₁0 : y.1 ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hdvd₁ hQpos)
            have hd₂0 : y.2 ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hdvd₂ hQpos)
            have hlcm0 : Nat.lcm y.1 y.2 ≠ 0 := Nat.lcm_ne_zero hd₁0 hd₂0
            refine ⟨⟨Nat.lcm y.1 y.2, y⟩, ?_, rfl⟩
            change ⟨Nat.lcm y.1 y.2, y⟩ ∈
              Q.divisors.sigma (fun d => (d.divisors ×ˢ d.divisors).filter
                (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d))
            rw [Finset.mem_sigma]
            constructor
            · exact Nat.mem_divisors.mpr ⟨lcm_dvd_of_squarefree hQ hdvd₁ hdvd₂, hQ0⟩
            · rw [Finset.mem_filter]
              constructor
              · rw [Finset.mem_product]
                constructor
                · exact Nat.mem_divisors.mpr ⟨Nat.dvd_lcm_left y.1 y.2, hlcm0⟩
                · exact Nat.mem_divisors.mpr ⟨Nat.dvd_lcm_right y.1 y.2, hlcm0⟩
              · rfl
          · intro x hx
            rfl
    _ = ∑ d₁ ∈ Q.divisors, ∑ d₂ ∈ Q.divisors, f (Nat.lcm d₁ d₂) := by
          rw [Finset.sum_product]

/-! ## 1b. Pan weight decomposition: 3^{ω(q)} = Σ_{d|q} 2^{ω(d)} -/

/-- Subset expansion of the binomial identity:
`Σ_{s∈t.powerset} 2^{|s|} = 3^{|t|} = (1+2)^{|t|}`.
For the squarefree Pan weight identity, each prime is either
absent from `d` or present with one of two choices counted
by `2^{ω(d)}`. -/
private theorem sum_powerset_pow_two {α : Type*} [DecidableEq α] (t : Finset α) :
    ∑ u ∈ t.powerset, (2 : ℕ) ^ u.card = 3 ^ t.card := by
  simpa using (Finset.sum_pow_mul_eq_add_pow (2 : ℕ) 1 t)

/-- **Pan weight decomposition** (Pan 1963; see also the weighted
form of Halberstam--Richert 1974 Lemma 10.3):
for squarefree `q`,
`3^{ω(q)} = Σ_{d|q} 2^{ω(d)} = Σ_{d|q} τ(d)`,
since `2^{ω(d)} = τ(d)` for squarefree `d`.
The three choices for each prime are regrouped by the divisor
`d` and its two inclusion choices. This divisor expansion is
the mechanism for handling the `3^{ω(q)}` weight in the outer
modulus sum of the weighted Pan argument. -/
theorem threeOmega_eq_sum_twoOmega_divisors {q : ℕ} (hq : Squarefree q) :
    (3 : ℕ) ^ q.primeFactors.card = ∑ d ∈ q.divisors, (2 : ℕ) ^ d.primeFactors.card := by
  rw [← sum_powerset_pow_two q.primeFactors]
  apply Finset.sum_bij (i := fun s _ => ∏ p ∈ s, p)
  · intro s hs
    rw [Nat.mem_divisors]
    constructor
    · rw [← Nat.prod_primeFactors_of_squarefree hq]
      exact Finset.prod_dvd_prod_of_subset s q.primeFactors (fun p => p)
        (Finset.mem_powerset.mp hs)
    · exact hq.ne_zero
  · intro s₁ hs₁ s₂ hs₂ h
    have hprime₁ : ∀ p ∈ s₁, p.Prime := by
      intro p hp
      exact (Nat.mem_primeFactors.mp ((Finset.mem_powerset.mp hs₁) hp)).1
    have hprime₂ : ∀ p ∈ s₂, p.Prime := by
      intro p hp
      exact (Nat.mem_primeFactors.mp ((Finset.mem_powerset.mp hs₂) hp)).1
    rw [← Nat.primeFactors_prod hprime₁, h, Nat.primeFactors_prod hprime₂]
  · intro d hd
    refine ⟨d.primeFactors, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hq.ne_zero
    · have hsqd : Squarefree d := hq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
      exact Nat.prod_primeFactors_of_squarefree hsqd
  · intro s hs
    have hprime : ∀ p ∈ s, p.Prime := by
      intro p hp
      exact (Nat.mem_primeFactors.mp ((Finset.mem_powerset.mp hs) hp)).1
    rw [Nat.primeFactors_prod hprime]

/-- **Regrouping Pan weights**: for squarefree `Q`,
`Σ_{q|Q}3^{ω(q)}f(q)
 = Σ_{d|Q}2^{ω(d)}·Σ_{m|Q/d}f(d·m)`.
Combine `3^{ω(q)} = Σ_{d|q}2^{ω(d)}` with the
divisibility-indexed bijection `(q,d) ↔ (d,m=q/d)`.
This replaces the `3^{ω(q)}`-weighted modulus sum by a
`2^{ω(d)}`-weighted double sum, as in Pan's classical
enlargement of the modulus sum (1963). -/
theorem threeOmegaWeightedSum_packaging (Q : ℕ) (hQ : Squarefree Q) (f : ℕ → ℝ) :
    (∑ q ∈ Q.divisors, (3 : ℝ) ^ q.primeFactors.card * f q) =
      ∑ d ∈ Q.divisors, (2 : ℝ) ^ d.primeFactors.card *
        (∑ m ∈ (Q / d).divisors, f (d * m)) := by
  rw [Finset.sum_congr rfl (by
    intro q hq
    have hsqq : Squarefree q := hQ.squarefree_of_dvd (Nat.dvd_of_mem_divisors hq)
    have hP : (3 : ℝ) ^ q.primeFactors.card =
        ∑ d ∈ q.divisors, (2 : ℝ) ^ d.primeFactors.card := by
      exact_mod_cast threeOmega_eq_sum_twoOmega_divisors hsqq
    rw [hP, Finset.sum_mul])]
  have hrhs : (∑ d ∈ Q.divisors, (2 : ℝ) ^ d.primeFactors.card *
        (∑ m ∈ (Q / d).divisors, f (d * m))) =
      ∑ d ∈ Q.divisors, ∑ m ∈ (Q / d).divisors, (2 : ℝ) ^ d.primeFactors.card * f (d * m) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
  rw [hrhs]
  rw [← Finset.sum_sigma (s := Q.divisors) (t := fun q => q.divisors)
    (f := fun x => (2 : ℝ) ^ x.2.primeFactors.card * f x.1)]
  rw [← Finset.sum_sigma (s := Q.divisors) (t := fun d => (Q / d).divisors)
    (f := fun x => (2 : ℝ) ^ x.1.primeFactors.card * f (x.1 * x.2))]
  apply Finset.sum_bij (i := fun x _ => ⟨x.2, x.1 / x.2⟩)
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hq, hd⟩
    have hqQ : x.1 ∣ Q := (Nat.mem_divisors.mp hq).1
    have hQ0 : Q ≠ 0 := (Nat.mem_divisors.mp hq).2
    have hdq : x.2 ∣ x.1 := (Nat.mem_divisors.mp hd).1
    have hdQ : x.2 ∣ Q := dvd_trans hdq hqQ
    rw [Finset.mem_sigma]
    constructor
    · rw [Nat.mem_divisors]
      exact ⟨hdQ, hQ0⟩
    · rw [Nat.mem_divisors]
      constructor
      · exact (Nat.dvd_div_iff_mul_dvd hdQ).2 (by simpa [Nat.mul_div_cancel' hdq] using hqQ)
      · exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hQ0) hdQ)
          (Nat.pos_of_dvd_of_pos hdQ (Nat.pos_of_ne_zero hQ0)))
  · intro a ha b hb h
    rcases Finset.mem_sigma.mp ha with ⟨ha₁, ha₂⟩
    rcases Finset.mem_sigma.mp hb with ⟨hb₁, hb₂⟩
    have hd₁q₁ : a.2 ∣ a.1 := (Nat.mem_divisors.mp ha₂).1
    have hd₂q₂ : b.2 ∣ b.1 := (Nat.mem_divisors.mp hb₂).1
    cases a with
    | mk q₁ d₁ =>
      cases b with
      | mk q₂ d₂ =>
          apply Sigma.ext
          · have hd : d₁ = d₂ := by simpa using congrArg Sigma.fst h
            have hq : q₁ / d₁ = q₂ / d₂ := by simpa using congrArg Sigma.snd h
            calc
              q₁ = d₁ * (q₁ / d₁) := (Nat.mul_div_cancel' hd₁q₁).symm
              _ = d₂ * (q₂ / d₂) := by rw [hq, hd]
              _ = q₂ := Nat.mul_div_cancel' hd₂q₂
          · exact heq_of_eq (by simpa using congrArg Sigma.fst h)
  · intro b hb
    rcases Finset.mem_sigma.mp hb with ⟨hd, hm⟩
    have hdQ : b.1 ∣ Q := (Nat.mem_divisors.mp hd).1
    have hQ0 : Q ≠ 0 := (Nat.mem_divisors.mp hd).2
    have hmQd : b.2 ∣ Q / b.1 := (Nat.mem_divisors.mp hm).1
    have hb1 : b.1 ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hdQ (Nat.pos_of_ne_zero hQ0))
    have hb2 : b.2 ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hmQd
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hQ0) hdQ)
        (Nat.pos_of_dvd_of_pos hdQ (Nat.pos_of_ne_zero hQ0))))
    refine ⟨⟨b.1 * b.2, b.1⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      constructor
      · rw [Nat.mem_divisors]
        constructor
        · exact (Nat.dvd_div_iff_mul_dvd hdQ).1 hmQd
        · exact hQ0
      · rw [Nat.mem_divisors]
        exact ⟨dvd_mul_right b.1 b.2, mul_ne_zero hb1 hb2⟩
    · simp [Nat.mul_div_cancel_left b.2 (Nat.pos_of_ne_zero hb1)]
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hq, hd⟩
    have hdq : x.2 ∣ x.1 := (Nat.mem_divisors.mp hd).1
    rw [Nat.mul_div_cancel' hdq]

/-! ## 2. Uniform weighted distribution interface for sieve applications -/

/-- Weighted remainder sum over sieve-product divisors:
`Σ_{d|P} w(d)·|rem d|`, where
`rem d = multSum d − ν(d)·totalMass` is the `BoundingSieve`
distribution remainder. -/
noncomputable def weightedPanRemainder (S : BoundingSieve) (w : ℕ → ℝ) : ℝ :=
  ∑ d ∈ S.prodPrimes.divisors, w d * |S.rem d|

/-- The `3^{ω(d)}`-weighted remainder is exactly the lcm
double sum `Σ_{d₁,d₂}|rem [d₁,d₂]|` in the Selberg expansion. -/
theorem weightedPanRemainder_eq_lcmDoubleSum (S : BoundingSieve) :
    weightedPanRemainder S (fun d => (3 : ℝ) ^ d.primeFactors.card) =
      ∑ d₁ ∈ S.prodPrimes.divisors, ∑ d₂ ∈ S.prodPrimes.divisors,
        |S.rem (Nat.lcm d₁ d₂)| := by
  unfold weightedPanRemainder
  exact lcmPairWeightedSum S.prodPrimes S.prodPrimes_squarefree (fun d => |S.rem d|)

/-- The counting-sieve error with coefficient sequence 1 is
bounded by the `3^{ω(d)}`-weighted remainder sum, generalizing
`correctedChenErrSum_le_panWeighted`. -/
theorem errSum_le_threeOmegaWeightedPanRemainder {S : BoundingSieve} :
    S.errSum (fun _ => 1) ≤
      weightedPanRemainder S (fun d => (3 : ℝ) ^ d.primeFactors.card) := by
  rw [BoundingSieve.errSum, weightedPanRemainder]
  apply Finset.sum_le_sum
  intro d hd
  have hw : (1 : ℝ) ≤ (3 : ℝ) ^ d.primeFactors.card := one_le_pow₀ (by norm_num)
  simpa using le_mul_of_one_le_left (abs_nonneg (S.rem d)) hw

/-- **Grouping the Λ²-weight remainder**: if `∀ d, |w d| ≤ 1`,
then `|Λ²w(d)| ≤ 3^{ω(d)}` for squarefree `d`, by the lcm-pair
count `lcmPairCount`. Therefore
`errSum(Λ²w) ≤ Σ_{d|P}3^{ω(d)}·|rem d|
 = weightedPanRemainder S 3^ω`.
This is the finite Selberg remainder `Σ 3^{ω(d)}|Δ(d)|`,
connecting a weighted Pan input to
`selberg_upper_bound_sieveProduct` in the Chen upper bound for `Ω`. -/
theorem errSum_lambdaSquared_le_threeOmegaWeightedPanRemainder
    {S : BoundingSieve} {w : ℕ → ℝ} (hw : ∀ d : ℕ, |w d| ≤ 1) :
    S.errSum (BoundingSieve.lambdaSquared w) ≤
      weightedPanRemainder S (fun d => (3 : ℝ) ^ d.primeFactors.card) := by
  rw [BoundingSieve.errSum, weightedPanRemainder]
  apply Finset.sum_le_sum
  intro d hd
  have hsq : Squarefree d := S.squarefree_of_mem_divisors_prodPrimes hd
  have hΛ : |BoundingSieve.lambdaSquared w d| ≤ (3 : ℝ) ^ d.primeFactors.card := by
    unfold BoundingSieve.lambdaSquared
    have hprod : (∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors,
          if d = Nat.lcm d₁ d₂ then w d₁ * w d₂ else 0) =
        ∑ x ∈ d.divisors ×ˢ d.divisors,
          if d = Nat.lcm x.1 x.2 then w x.1 * w x.2 else 0 := by
      simpa using (Finset.sum_product (s := d.divisors) (t := d.divisors)
        (f := fun p : ℕ × ℕ => if d = Nat.lcm p.1 p.2 then w p.1 * w p.2 else 0)).symm
    rw [hprod]
    calc
      |∑ x ∈ d.divisors ×ˢ d.divisors,
          if d = Nat.lcm x.1 x.2 then w x.1 * w x.2 else 0|
          ≤ ∑ x ∈ d.divisors ×ˢ d.divisors,
              |if d = Nat.lcm x.1 x.2 then w x.1 * w x.2 else 0| := by
              exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ d.divisors ×ˢ d.divisors,
              if d = Nat.lcm x.1 x.2 then (1 : ℝ) else 0 := by
              apply Finset.sum_le_sum
              intro x hx
              by_cases h : d = Nat.lcm x.1 x.2
              · simp [h]
                nlinarith [hw x.1, hw x.2, abs_nonneg (w x.1), abs_nonneg (w x.2),
                  abs_mul (w x.1) (w x.2)]
              · simp [h]
      _ = ((d.divisors ×ˢ d.divisors).filter
              (fun x : ℕ × ℕ => d = Nat.lcm x.1 x.2)).card := by
              rw [← Finset.sum_filter]
              rw [Finset.sum_const]
              simp
      _ = (3 : ℝ) ^ d.primeFactors.card := by
              have hc : ((d.divisors ×ˢ d.divisors).filter
                  (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d)).card = 3 ^ d.primeFactors.card :=
                lcmPairCount d hsq
              have hfilt : (d.divisors ×ˢ d.divisors).filter
                  (fun x : ℕ × ℕ => d = Nat.lcm x.1 x.2) =
                  (d.divisors ×ˢ d.divisors).filter
                    (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d) := by
                ext x
                simp [eq_comm]
              rw [hfilt, hc, Nat.cast_pow]
              norm_num
  exact mul_le_mul_of_nonneg_right hΛ (abs_nonneg (S.rem d))

/-- **Uniform weighted Pan distribution condition**:
for each `A > 0`, there is a uniform `C > 0` such that for
every even `N ≥ 1000`,
`Σ_{d|P(N)} w(d)·|rem(N,d)| ≤ C·x(N)/log^A x(N)`.

For `x N = N`, `S N = correctedChenBoundingSieve N`,
and `w d = 3^{ω(d)}`, the absolute remainder is
`|#{p∈support : p≡N [MOD d]} − ν(d)·N/log N|`,
the form in `CorrectedChenDistributionCondition`.
Once this input holds, `errSum_le_threeOmegaWeightedPanRemainder`
gives `errSum = O(N/log^A N)`. The constant precedes `∀ N`;
the threshold in this API is the fixed value 1000. -/
def WeightedPanCondition (x : ℕ → ℝ) (S : ℕ → BoundingSieve) (w : ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 1000 ≤ N → Even N →
      weightedPanRemainder (S N) w ≤ C * x N / (log (x N)) ^ A

/-- The `3^{ω(d)}`-weighted specialization needed in Chen's theorem. -/
def ThreeOmegaWeightedPanCondition (x : ℕ → ℝ) (S : ℕ → BoundingSieve) : Prop :=
  WeightedPanCondition x S (fun d => (3 : ℝ) ^ d.primeFactors.card)

/-! ## 3. Weighted Pan mean-value target -/

/-- `π(y;a,q,l)`: count primes `p` with `a·p ≤ y` and
`a·p ≡ l [MOD q]`, as in Liu 2022 §II for positive `a`.
The definition explicitly searches `p ≤ y`, including at `a = 0`.
The congruence is on the product `a·p`, not on `p`;
this is the scaled AP prime count in the error for the Ω bound. -/
def primesInAPBelow (y a q l : ℕ) : ℕ :=
  ((range (y + 1)).filter (fun p => p.Prime ∧ a * p ≤ y ∧ a * p ≡ l [MOD q])).card

/-- The scaled proxy error
`π(y; a, q, l) - logarithmicIntegral(y/a)/φ(q)`.

Here `logarithmicIntegral` is the `x / log x` proxy, not the
paper's true logarithmic integral. Source-facing Liu interfaces should
parameterize the main-term function instead of identifying the two. -/
noncomputable def panDistributionError (y a q l : ℕ) : ℝ :=
  (primesInAPBelow y a q l : ℝ) - logarithmicIntegral ((y : ℝ) / a) / Nat.totient q

/-- Weighted distribution-error sum modulo `q`:
`Σ_{(a,q)=1, a≤X} f(a)·Δ(y;a,q,l)`.
This is a signed sum, before taking absolute values.
The restriction `(a,q)=1` is essential to Liu §IV's correction. -/
noncomputable def panDistributionSum (y X q l : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ range (X + 1), if a.Coprime q then f a * panDistributionError y a q l else 0

/-- The unrestricted inner sum occurring before Liu's coprime/non-coprime
partition of the paper remainder `R`. -/
noncomputable def panDistributionFullSum (y X q l : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ range (X + 1), f a * panDistributionError y a q l

/-- The signed non-coprime part removed from `panDistributionSum`. -/
noncomputable def panDistributionNoncoprimeSum
    (y X q l : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ range (X + 1),
    if ¬a.Coprime q then f a * panDistributionError y a q l else 0

/-- The termwise absolute majorant of the non-coprime part. This is the finite
inner sum used in Liu's `R₁`, before the outer modulus weights are applied. -/
noncomputable def panDistributionNoncoprimeMajorant
    (y X q l : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ range (X + 1),
    if ¬a.Coprime q then |f a| * |panDistributionError y a q l| else 0

/-- Exact finite partition of the unrestricted paper sum into its coprime Pan
part and its signed non-coprime part. -/
theorem panDistributionFullSum_eq_coprime_add_noncoprime
    (y X q l : ℕ) (f : ℕ → ℝ) :
    panDistributionFullSum y X q l f =
      panDistributionSum y X q l f +
        panDistributionNoncoprimeSum y X q l f := by
  classical
  unfold panDistributionFullSum panDistributionSum panDistributionNoncoprimeSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hcop : a.Coprime q <;> simp [hcop]

/-- The signed non-coprime sum is bounded by Liu's termwise `R₁` majorant. -/
theorem abs_panDistributionNoncoprimeSum_le
    (y X q l : ℕ) (f : ℕ → ℝ) :
    |panDistributionNoncoprimeSum y X q l f| ≤
      panDistributionNoncoprimeMajorant y X q l f := by
  classical
  unfold panDistributionNoncoprimeSum panDistributionNoncoprimeMajorant
  calc
    |∑ a ∈ range (X + 1),
        (if ¬a.Coprime q then f a * panDistributionError y a q l else 0)|
        ≤ ∑ a ∈ range (X + 1),
            |if ¬a.Coprime q then f a * panDistributionError y a q l else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a ∈ range (X + 1),
          (if ¬a.Coprime q then |f a| * |panDistributionError y a q l| else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hcop : a.Coprime q <;> simp [hcop, abs_mul]

/-- Liu's finite `R = R_coprime + R_noncoprime` triangle bound. The first term
is the source-faithful Pan sum; the second is the still-separate `R₁`
majorant. -/
theorem abs_panDistributionFullSum_le_coprime_add_noncoprime
    (y X q l : ℕ) (f : ℕ → ℝ) :
    |panDistributionFullSum y X q l f| ≤
      |panDistributionSum y X q l f| +
        panDistributionNoncoprimeMajorant y X q l f := by
  rw [panDistributionFullSum_eq_coprime_add_noncoprime]
  exact le_trans (abs_add_le _ _)
    (add_le_add_right (abs_panDistributionNoncoprimeSum_le y X q l f) _)

/-- Canonical representatives of the reduced residue classes modulo `q`.
For `q = 1` this is the singleton `{0}`; for `q = 0` it is empty. -/
def unitResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun l => l.Coprime q)

@[simp] theorem unitResidues_zero : unitResidues 0 = ∅ := by
  simp [unitResidues]

@[simp] theorem unitResidues_one : unitResidues 1 = {0} := by
  simp [unitResidues]

/-- For a nontrivial modulus, the canonical representatives agree with the
traditional interval `1 ≤ l ≤ q - 1`. -/
theorem unitResidues_eq_Icc_filter {q : ℕ} (hq : 1 < q) :
    unitResidues q = (Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q) := by
  ext l
  simp only [unitResidues, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hlq, hlcop⟩
    have hl0 : l ≠ 0 := by
      intro hl
      subst l
      simp_all
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hl0, by omega⟩, hlcop⟩
  · rintro ⟨⟨hl1, hlq⟩, hlcop⟩
    exact ⟨by omega, hlcop⟩

/-- `max_{0≤l<q,(l,q)=1} |panDistributionSum y X q l f|`, with the unique
class modulo `1` represented by `0`; the empty `q = 0` maximum is `0`. -/
noncomputable def panMaxL (y X q : ℕ) (f : ℕ → ℝ) : ℝ :=
  let S : Finset ℕ := unitResidues q
  if h : S.Nonempty then
    (S.image (fun l => |panDistributionSum y X q l f|)).max' (Finset.image_nonempty.mpr h)
  else 0

@[simp] theorem panMaxL_zero (y X : ℕ) (f : ℕ → ℝ) :
    panMaxL y X 0 f = 0 := by
  simp [panMaxL]

@[simp] theorem panMaxL_one (y X : ℕ) (f : ℕ → ℝ) :
    panMaxL y X 1 f = |panDistributionSum y X 1 0 f| := by
  simp [panMaxL]

/-- `max_{y≤x} panMaxL y X q f`: uniform maximum over
the truncation parameter `y`, as in Liu Theorem 2. -/
noncomputable def panMaxY (X q x : ℕ) (f : ℕ → ℝ) : ℝ :=
  ((Finset.range (x + 1)).image (fun y => panMaxL y X q f)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

@[simp] theorem panMaxY_zero (X x : ℕ) (f : ℕ → ℝ) :
    panMaxY X 0 x f = 0 := by
  unfold panMaxY
  apply le_antisymm
  · apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    simp
  · simpa using Finset.le_max'
      ((Finset.range (x + 1)).image (fun y => panMaxL y X 0 f))
      (panMaxL 0 X 0 f) (Finset.mem_image.mpr ⟨0, by simp, rfl⟩)

theorem panMaxY_one (X x : ℕ) (f : ℕ → ℝ) :
    panMaxY X 1 x f =
      ((Finset.range (x + 1)).image
        (fun y => |panDistributionSum y X 1 0 f|)).max'
          (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
  simp only [panMaxY, panMaxL_one]

/-- **Coarse pure-li bound**: the polylogarithmic result of
separating the positive main term and taking its absolute value
in the coarse Vaughan chain. It is not Liu 2022 Theorem 2
and cannot supply `WeightedPanCondition`. This separate
proposition records exactly the scope of the coarse reductions. -/
def PanMeanValueUniformCrude (x : ℕ → ℝ) (f : ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) /
            (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panMaxY X q (Nat.floor (x X)) f ≤
        C * x X * (log (x X)) ^ (A + 7)

/-- **Weighted Pan mean-value target**, with the quantifier and
signed-sum structure of Liu 2022 Theorem 2:
for each `A > 0`, there are `C > 0`, `B`, and `x₀` such that
for all `X ≥ x₀`,

  Σ_{q ≤ (x X)^{1/2}/log^B(x X)} μ²(q)·3^{ω(q)}·
    max_{y ≤ x X} max_{0<l<q,(l,q)=1}
      |Σ_{(a,q)=1, a≤X} f(a)·Δ(y;a,q,l)| ≤ C·x X/log^A(x X).

Here `Δ(y;a,q,l) = π(y;a,q,l) − li(y/a)/φ(q)`, with the
implemented `li` name denoting the `x/log x` proxy.
Three structural features are essential (see `PAN_PROOF_ATLAS.md`):
the inner coprimality restriction, the maximum over `y`, and the
absolute value around the **whole signed sum**, not `Σ f·|Δ|`.
Dropping coprimality fails for the Chen weights: Liu §IV's
`R₁` correction depends on the specific weight and sieve product
and is handled in the Chen application.

The inverse logarithm bounds the signed distribution error,
not a pure absolute-`li` block. The coarse split gives only
`PanMeanValueUniformCrude`. A classical proof retains `li`
and the Vaughan middle/small terms inside one absolute value,
while the nondecaying Selberg main term remains in the Chen
main-term estimate; this is Liu §III's `M = M₁ + R` separation.

This proposition is an analytic input, not an unconditional theorem
proved here. The classical error estimate for `Ω` uses the
large sieve and Vaughan's identity (Pan 1963; Halberstam--Richert
1974 Ch. 10; Liu 2022 §III).
Connecting it to `WeightedPanCondition` additionally requires
support truncation and main-term comparison, including the
classical relation `li(x) = x/log x + O(x/log²x)` with the
genuine logarithmic integral. -/
def PanMeanValueUniform (x : ℕ → ℝ) (f : ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) /
            (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panMaxY X q (Nat.floor (x X)) f ≤
        C * x X / (log (x X)) ^ A

/-! ## From the Pan expression to sieve remainders

At `a = 1`, `primesInAPBelow y a q l` is the ordinary count
`#{p≤y : p is prime, p≡l [MOD q]}`.
This identifies the source of the sieve remainder
`#{p∈support : p≡N [MOD d]}`. Further comparison hypotheses
are needed to bound the sieve's weighted remainder sum
by the `3^{ω(q)}`-weighted `panMaxY` sum.

`WeightedPanCondition` requires `C·xN/log^A(xN)` for every
`A > 0`; the switching sieve and error absorption need
arbitrarily large logarithmic savings.
`PanMeanValueUniformCrude`, with right side
`C·xX·(log xX)^{A+7}`, cannot meet that requirement.
`PanMeanValueUniform` retains the inverse-log target and is
assembled only under analytic inputs such as
`PanSourceFaithfulSignedMainBound`.

The generic absolute-value chain under `|f| ≤ 1` cannot provide
the saving. The inner pure-main-term sum has a refined
`y·(1+log log y)` shape in suitable ranges, or the coarse bound
`(y/log 2)·(1+log X)`; multiplying by the q-factor `log⁶`
does not produce inverse-log decay. Even retaining coprimality,
the choice `f = 1` leaves a pure-main-term contribution of
the indicated `(y/log y)·log X` size.
The classical application needs the specific Chen weights
and control of their harmonic sum `Σ f(a)/a`, together with
the sieve main term of shape `x/log x·∏(1-ν(p)/p)`
in the unnormalized density convention.
The saving is a difference estimate
`|main term − sieve main term| ≪ x/log^A x`.
These weight and main-term requirements belong to the Chen
application and its analytic bridge, not to the `a = 1`
identities below; see `PAN_PROOF_ATLAS.md`.
-/

/-- At `a = 1`, the scaled count is the ordinary AP prime count. -/
theorem primesInAPBelow_one (y q l : ℕ) :
    primesInAPBelow y 1 q l =
      ((Finset.range (y + 1)).filter (fun p => p.Prime ∧ p ≡ l [MOD q])).card := by
  unfold primesInAPBelow
  congr 1
  ext p
  constructor
  · intro hp
    rw [Finset.mem_filter] at hp ⊢
    rcases hp with ⟨hp1, hp2⟩
    rcases hp2 with ⟨hpp, hle, hcong⟩
    exact ⟨hp1, ⟨hpp, by simpa using hcong⟩⟩
  · intro hp
    rw [Finset.mem_filter] at hp ⊢
    rcases hp with ⟨hp1, hp2⟩
    rcases hp2 with ⟨hpp, hcong⟩
    exact ⟨hp1, ⟨hpp, ⟨by simpa [one_mul] using
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp1)), by simpa using hcong⟩⟩⟩

/-- At `a = 1`, the scaled count equals `primesInAP`,
the ordinary AP count in the BV interface. -/
theorem primesInAPBelow_one_eq_primesInAP (y q l : ℕ) :
    primesInAPBelow y 1 q l = primesInAP y q l := by
  simpa [primesInAP] using primesInAPBelow_one y q l

/-- At `a = 1`, the distribution error is
`π(y;q,l) − li(y)/φ(q)`, the ordinary AP prime error for
the implemented main-term proxy. -/
theorem panDistributionError_one (y q l : ℕ) :
    panDistributionError y 1 q l =
      (((Finset.range (y + 1)).filter (fun p => p.Prime ∧ p ≡ l [MOD q])).card : ℝ) -
        logarithmicIntegral (y : ℝ) / Nat.totient q := by
  unfold panDistributionError
  rw [primesInAPBelow_one]
  simp [logarithmicIntegral]

end AnalyticNumberTheory.Sieve
